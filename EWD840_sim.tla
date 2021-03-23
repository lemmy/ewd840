------------------------------- MODULE EWD840_sim -------------------------------
EXTENDS Naturals, TLC, TLCExt, IOUtils, CSV, Sequences, EWD840

\* The data collection below only works with TLC running in simulation mode.
\* Fail fast if TLC runs in the wrong mode.
\* TODO: Add "Generator" to TLC.
ASSUME TLCGet("mode") = "Simulation"

\* A function from action names to a Nat that is the TLCGet/TLCSet register for
\* the action (TLCGet/TLCSet only supports naturals for (user-defined) registers).
A2I ==
    [
        \* TLC does not always return a meaningful action name. For example, an
        \* action might be undeclared.
        UnnamedAction |-> 0,
        Init |-> 0, 
        \* InitSim is the name given to the initial predicate below that
        \* contraints EWD840!Init. 
        InitSim |-> 0,
        InitiateProbe |-> 1, 
        SendMsg |-> 2, 
        PassToken |-> 3, 
        Deactivate |-> 4
    ]

(*************************************************)
(* Initialization of TLC and OS (constant-level) *)
(*************************************************)

ToFile ==
    "N" \o ToString(N) \o ".csv"

InitializeStatistics ==
    /\ \A r \in DOMAIN A2I: TLCSet(A2I[r], 0)
    /\ TLCSet(5, 0)

\* Initialize TLCSet register at TLC startup.
ASSUME InitializeStatistics

\* Empty/clear an old out file at TLC startup and write column headers.
ASSUME 
    IOExec(
        <<"bash", "-c", 
            "echo \"Variant#Length#InitiateProbe#SendMsg#PassToken#Deactivate#Node#T\" > " \o ToFile>>
        ).exitValue = 0

(**************************************************************)
(* Domain-specific constraints (state-level) to collect data. *)
(**************************************************************)

1AtEndOfEachStep ==
    \* Counts the occurrences of actions in TLCGet/TLCSet registers.
    \* Pitfall:
    \* - Action counting in a constraint gives correct results iff TLC
    \*   rusn with -Dtlc2.tool.impl.Tool.probabilistic=true (or -generate).
    \*   Otherwise, the simulator evaluates A for every successor state,
    \*   not just the the one that the simulator will eventually choose
    \*   as the stateto explore further.
    \*   => Assert(TLCGet("mode")="Generation") conjunct or 
    \*      ASSUME(TLCGet("mode")...)
    \* TODO: Add TLCGet("action").id to avoid A21 function that might get
    \*       outdated when the (behavior) spec changes. However, .id should
    \*       abstract from the fact that TLC -internally- has many instances
    \*       of an action when it appears e.g. inside existential quantification.
    \*       Alternatively, TLCSet(k,v) could be changed to support any value
    \*       for k such as the record that is equal to TLCGet("action"). It
    \*       would not only spare us A2I here, but also below in 3AtEndOfBehavior
    \*       when writing the statistics.
    LET a == TLCGet("action").name
    IN \*/\ PrintT(<<a, TLCGet("level"), TLCGet(1), TLCGet(2), TLCGet(3), TLCGet(4)>>)
       /\ Assert(a \in DOMAIN A2I, <<"Unknown action", a>>)
       /\ TLCSet(A2I[a], TLCGet(A2I[a]) + 1)

\* "Termination" does not mean termination of TLC but the state when the nodes,
\* modeled by the algorithm, have terminated.  This is a singular state of the
\* algorithm.
2AtTermination ==
    \* AtTermination has to come before AtEndOfBehavior in the .cfg file. Here,
    \* we write TLCGet(5) and in AtEndOfBehavior we read its value.
    /\ terminated
    \* Do not override register 5 if it has already been set in the current
    \* behavior.
    /\ TLCGet(5) = 0
    \* It would be quite elegant here (changed to action constraint) if stated
    \* as:
    \*
    \*   /\ (~terminated /\ terminated')
    \*
    \* However, that would require some sort mechanism (think prophecy variable)
    \* to force the simulatior/generator to pick a successor state t s.t. 
    \* `terminated` t.
    =>
    \* Record the length of the prefix of the behavior the moment termination
    \* occurres.
    /\ TLCSet(5, TLCGet("level"))

3AtEndOfBehavior ==
    \* Just a good old state constraint. Could have been an invariant too.
    \* The disadvantage of a constraint is that the antecedent is evaluated
    \* for *every* state generated instead of just the last state generated
    \* by the simulator when we want the consequent to be evalauted.
    \* A constraint's advantage is that it works with old versions of TLC.
    \/ /\ terminationDetected
       /\ terminated
    \* It's possible that the nodes have not terminated after 100 states,
    \* which is the max trace length of the simulator.  Even though this 
    \* outcome isn't really what we are after with our simulation, we have
    \* to re-initialize the statistics.  Otherwise, we collect inconsistent
    \* statistics.
    \* https://github.com/tlaplus/tlaplus/commit/3d4d0f33b3298417f594b559cbf87a4f389697e3
    \* causes the regression that this has to be 101, even though -depth is 100.
    \/ TLCGet("level") >= 101
    \* Pitfall:
    \* - The D in `TLCGet("level") >= D` depends on what the user sets the simulator's
    \*   -depth command-line parameter to.  Hard-coding it here is, thus, brittle.  As
    \*   a workaround, the value of the -depth parameter could be available in a named
    \*   TLCGet(..) register, or -even better- a TLCGet("config") register could equal
    \*   a record whose keys are all of TLC's config values.
    \* - Stating the condition for what is essentially the last state of a behavior
    \*   can probably be challenging.  Also, the antecedent is going to be
    \*   evaluated on every state and not just the last one.  A generic antecedent
    \*   would be `~ENABLED Next`, which, however is usually prohibitively expensive.
    \*   Secondly, `ENABLED Next` obviously evaluates the next-state relation, which
    \*   might update the very statistics we wish to collect.  In other words, the
    \*   antecedent here has to be side-effect free/idempotent WRT the statistics.
    => 
    /\ LET l == TLCGet("level")
           ip == TLCGet(A2I["InitiateProbe"])  \* Number of InitiateProbe steps.
           sm == TLCGet(A2I["SendMsg"])  \* Number of SendMsg steps.
           pt == TLCGet(A2I["PassToken"])  \* Number of PassToken steps.
           da == TLCGet(A2I["Deactivate"])  \* Number of Deactivate steps.
       IN \* Validate data record (+ 1 to account for initial state).
          \* If there is a mismatch, TLC might be running without
          \* -Dtlc2.tool.impl.Tool.probabilistic=true
          /\ Assert(l = 1 + ip + sm + pt + da, 
                <<"mismatch (l=sumAllActions)", l, 1 + ip + sm + pt + da>>)
          \* Append record to CSV file on disk.
          /\ CSVWrite("%1$s#%2$s#%3$s#%4$s#%5$s#%6$s#%7$s#%8$s",
                <<feature, l, ip, sm, pt, da, N, TLCGet(5)>>,
                ToFile)
    \* Re-initialize stats *after* TLCGet register have been read above!
    /\ InitializeStatistics     

(***************************************************************************)
(* Behavior spec to reduce state-space to what is relevant for simualtion. *)
(***************************************************************************)

InitSim ==
    \* Constraint the set of initial states defined in EWD840!Init to
    \* those that correspond to what an implementation would start with.
    \* In other words, when collecting statistics, we don't want to start
    \* in a state where the system has already terminated.
    /\ active \in [Node -> {TRUE}]
    /\ color \in [Node -> {white}]
    /\ tpos = 0

SpecSim == InitSim /\ Spec

=============================================================================
