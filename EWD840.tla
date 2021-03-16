------------------------------- MODULE EWD840 -------------------------------
EXTENDS Naturals

CONSTANT N

Node == 0 .. N-1

VARIABLES active, color, tpos, tcolor
vars == <<active, color, tpos, tcolor>>

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> BOOLEAN]
  /\ tpos \in Node
  /\ tcolor \in BOOLEAN

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> BOOLEAN]
  /\ tpos \in Node
  /\ tcolor = FALSE

InitiateProbe ==
  /\ tpos = 0
  /\ \/ tcolor = FALSE
     \/ color[0] = FALSE
  /\ tpos' = N-1
  /\ tcolor' = TRUE
  /\ color' = [color EXCEPT ![0] = TRUE]
  /\ UNCHANGED <<active>>

PassToken(i) ==
    /\ ~active[i]
    /\ tpos = i
    /\ tpos' = i-1
    \* Passing along the token transfers the taint
    \* from the node to the token.
    /\ tcolor' = IF color[i] = FALSE THEN FALSE ELSE tcolor
    /\ color' = [color EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<active>>

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

-----------------------------------------------------------------------------

Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<color, tpos, tcolor>>

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
            /\ color' = [color EXCEPT ![i] = IF j>i THEN FALSE ELSE @]
    /\ UNCHANGED <<tpos, tcolor>>

Environment ==
    \E i \in Node:
        \/ Deactivate(i)
        \/ SendMsg(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

terminationDetected ==
    /\ ~active[0]
    /\ color[0] = TRUE
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

-----------------------------------------------------------------------------

SpecWFEnv ==
    Spec /\ WF_vars(Environment)

AlwaysTerminates ==    
    <>[](terminationDetected)

THEOREM SpecWFEnv => AlwaysTerminates

=============================================================================
