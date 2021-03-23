------------------------------- MODULE EWD840 -------------------------------
EXTENDS Naturals

Features == {"PT1","PT2","PT3","SM1"} \ {} \* Second set are disabled features.

-----------------------------------------------------------------------------

CONSTANT N
ASSUME NAssumption == N \in (Nat \ {0})

Node == 0 .. N-1

black == "black"
white == "white"
Color == {black, white}

VARIABLES active, color, tpos, tcolor, feature
vars == <<active, color, tpos, tcolor, feature>>

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ tpos \in Node
  /\ tcolor \in Color \* Only conjunct that differs from Init.
  /\ feature \in SUBSET Features

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ tpos \in Node
  /\ tcolor = black
  /\ feature \in SUBSET Features

InitiateProbe ==
  /\ tpos = 0
  /\ \/ tcolor = black
     \/ color[0] = black
  /\ tpos' = N-1
  /\ tcolor' = white
  /\ color' = [color EXCEPT ![0] = white]
  /\ UNCHANGED <<active, feature>>

PassToken(i) ==
    /\  \/ ~active[i]
        \* \* There is no need to wait for this node to terminate if a
        \* \* higher-numbered node has already marked this round inconclusive.
        \* \* Instead, the initiator may start a new round (upon receipt of
        \* \* the token) in the meantime.
        \/ PT1:: IF "PT1" \in feature THEN
                   tcolor = black
                 ELSE
                   FALSE
        \* \* Likewise, don't wait for this node to terminate, if it is
        \* \* going to cause an inconclusive round.
        \/ PT2:: IF "PT2" \in feature THEN
                   color[i] = black
                 ELSE
                   FALSE
    /\ tpos = i
    /\ PT3:: IF "PT3" \in feature THEN
               tpos' = IF tcolor = black THEN 0 ELSE i-1
             ELSE
               tpos' = i - 1
    \* Passing along the token transfers the taint
    \* from the node to the token.
    /\ tcolor' = IF color[i] = black THEN black ELSE tcolor
    /\ color' = [color EXCEPT ![i] = white]
    /\ UNCHANGED <<active, feature>>

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

-----------------------------------------------------------------------------

Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<color, tpos, tcolor, feature>>

SendMsg(i) ==
    /\ active[i]
    /\ \E j \in Node:
            /\ active' = [active EXCEPT ![j] = TRUE]
            \* If the message activates a lower-numbered node, there is
            \* no need to taint the token to mark the round inconclusive.
            \* This is because the lower numbered node has not yet received
            \* the token for this round and, thus, can taint it itself.
            \* Thus, this is an optimization to avoid another round in the
            \* case that the recipient node deactivates between receiving
            \* the message and the token.
            /\ SM1(j):: IF "SM1" \in feature THEN
                       color' = [color EXCEPT ![i] = IF j>i THEN black ELSE @]
                     ELSE 
                       color' = [color EXCEPT ![i] = black]
    /\ UNCHANGED <<tpos, tcolor, feature>>

Environment ==
    \E i \in Node:
        \/ Deactivate(i)
        \/ SendMsg(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

terminationDetected ==
    /\ ~active[0]
    /\ color[0] = white
    /\ tpos = 0
    /\ tcolor = white

terminated ==
    \A n \in Node: ~active[n]

\* If termination has been detected, all nodes are
\* indeed inactive.
Inv == 
    terminationDetected => terminated

THEOREM Spec => []Inv

-----------------------------------------------------------------------------

\* Dijkstra's (inductive) invariant.
IInv ==
    \/ P0:: \A i \in Node : tpos < i => ~ active[i]
    \/ P1:: \E j \in 0 .. tpos : color[j] = black
    \/ P2:: tcolor = black

THEOREM Spec => []IInv

-----------------------------------------------------------------------------

\* Termination of nodes leads to termination being detected.
Prop ==
    terminated ~> terminationDetected

THEOREM Spec => Prop

-----------------------------------------------------------------------------

SpecWFEnv ==
    \* It does not matter if we define weak-fairness on Environment or on
    \* Deactivate specifically.  AlwaysTerminates stipulates that for 
    \* behaviors where the exists a suffix with no SendMsg actions occurring,
    \* termination is eventually detected.  A suffix with no SendMsg actions
    \* satisfies WF_vars(Environment) iff Deactivate actions occur.
    \* In other words, the antecedence of AlwaysTerminates is false for
    \* behaviors with suffixes that have SendMsg actions.
    \* We cannot define fairness of the next-state relation to rule out
    \* behaviors with SendMsg actions unless we change the behavior part of
    \* the spec.
    Spec /\ WF_vars(Environment)

AlwaysTerminates ==    
    <>[][\A n \in Node: ~SendMsg(n)]_vars => <>[]terminationDetected

THEOREM SpecWFEnv => AlwaysTerminates

=============================================================================
