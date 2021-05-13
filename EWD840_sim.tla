
This spec variant works with TLC as of 05/13/2021!
=> TLCGet("config").version perhaps?

------------------------------- MODULE EWD840_sim -------------------------------
EXTENDS Naturals, TLC, TLCExt, IOUtils, CSV, Sequences, FiniteSetsExt, Functions, EWD840

\* TODO: Consume from CommunityModules:
\* https://github.com/tlaplus/CommunityModules/issues/40
FirstMatch(s, P(_)) ==
  IF { i \in 1..Len(s): P(s[i]) } = {}
  THEN 0
  ELSE Min({ i \in 1..Len(s): P(s[i]) })

---------------------------------------------------

\* The data collection below only works with TLC running in generation mode.
\* Unless TLC runs with -Dtlc2.tool.impl.Tool.probabilistic=true (or -generate).
\* the simulator generates all successor states and chooses one randomly. 
\* In "generate" mode, TLC randomly generates a (single) successor state.
\* Fail fast if TLC runs in modes that would cause bogus results.
ASSUME TLCGet("config").mode = "generate"

\* Actions defined in the spec/model.
SActs == { a.name : a \in TLCGet("config").actions }

(*************************************************)
(* Initialization of TLC and OS (constant-level) *)
(*************************************************)

ToFile ==
    "N" \o ToString(N) \o ".csv"

\* Empty/clear an old out file at TLC startup and write column headers.
ASSUME 
    IOExec(
        <<"bash", "-c", 
            "echo \"Variant#Length#InitiateProbe#SendMsg#PassToken#Deactivate#Node#T\" > " \o ToFile>>
        ).exitValue = 0 \* Fail fast if ToFile was not created.

(**************************************************************)
(* Domain-specific constraints (state-level) to collect data. *)
(**************************************************************)

AtEndOfBehavior ==
    \* Just an ordinary state constraint (could have been an invariant too).
    \* The disadvantage of a constraint (or inv) is that the antecedent is evaluated
    \* for *every* generated state, instead of just after the last state when we 
    \* actually want the consequent to be evalauted. A constraint's advantage is that
    \* it works with old versions of TLC.
    \/ /\ terminationDetected
       /\ terminated
    \* Generator (Simulator) will stop because the current behavior exceeds the
    \* max trace length given via the -depth parameter.
    \/ TLCGet("level") = TLCGet("config").depth   
    => 
    /\ LET l == TLCGet("level")
           o == LET \* Actions appearing in the trace.
                    TActs == [ i \in 1..Len(Trace) |-> Trace[i]._action.name ]
                \* Occurrences of each SActs in TActs (possibly zero for some).
                IN [ a \in SActs |-> Len(SelectSeq(TActs, LAMBDA x : x = a)) ]
           \* Lenght of prefix (of current behavior) for which ~terminated holds.
           t == FirstMatch(Trace, LAMBDA t: \A n \in Node: ~t.active[n])
       IN \* Data validation before collection (base = 1 to account for initial state).
          /\ Assert(l = FoldFunctionOnSet(LAMBDA x,y: x + y, 1, o, SActs), "Bogus number of action occurrences!")
          /\ Assert(t <= l, "Bogus results!")
          \* Append record to CSV file on disk.
          /\ CSVWrite("%1$s#%2$s#%3$s#%4$s#%5$s#%6$s#%7$s#%8$s",
                <<feature, l,
                  \* TODO: Generically write all elements of `DOMAIN o`?
                  o["InitiateProbe"], o["SendMsg"], o["PassToken"], o["Deactivate"],
                  N, t>>,
                ToFile)

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
