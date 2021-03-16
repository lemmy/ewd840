------------------------------- MODULE EWD840 -------------------------------
EXTENDS Naturals

CONSTANT N

Node == 0 .. N-1

VARIABLES active, tpos
vars == <<active, tpos>>

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ tpos \in Node

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ tpos \in Node

InitiateProbe ==
  /\ tpos = 0
  /\ tpos' = N-1
  /\ UNCHANGED <<active>>

PassToken(i) ==
    /\ tpos = i
    /\ tpos' = i-1
    /\ UNCHANGED <<active>>

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

Next == System

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

terminationDetected ==
    /\ ~active[0]
    /\ tpos = 0

terminated ==
    \A n \in Node: ~active[n]

\* If termination has been detected, all nodes are
\* indeed inactive.
Inv == 
    terminationDetected => terminated

THEOREM Spec => []Inv

=============================================================================
