------------------------------- MODULE EWD840 -------------------------------
EXTENDS Naturals

CONSTANT N

Node == 0 .. N-1

VARIABLES active, tpos, tcolor
vars == <<active, tpos, tcolor>>

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ tpos \in Node
  /\ tcolor \in BOOLEAN

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ tpos \in Node
  /\ tcolor = FALSE

InitiateProbe ==
  /\ tpos = 0
  /\ tcolor = FALSE
  /\ tpos' = N-1
  /\ tcolor' = TRUE
  /\ UNCHANGED <<active>>

PassToken(i) ==
    /\ ~active[i]
    /\ tpos = i
    /\ tpos' = i-1
    /\ UNCHANGED <<active, tcolor>>

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

-----------------------------------------------------------------------------

Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<tpos, tcolor>>

Environment ==
    \E i \in Node:
        \/ Deactivate(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)
                              /\ WF_vars(Environment)

-----------------------------------------------------------------------------

terminationDetected ==
    /\ ~active[0]
    /\ tpos = 0
    /\ tcolor = TRUE

terminated ==
    \A n \in Node: ~active[n]

\* If termination has been detected, all nodes are
\* indeed inactive.
Inv == 
    terminationDetected => terminated

THEOREM Spec => []Inv

\* Termination of nodes leads to termination being detected.
Prop ==
    terminated ~> terminationDetected

THEOREM Spec => Prop

AlwaysTerminates ==    
    <>[](terminationDetected)

=============================================================================
