------------------------------- MODULE EWD840 -------------------------------
EXTENDS Naturals

CONSTANT N
ASSUME NAssumption == N \in (Nat \ {0})

Node == 0 .. N-1

black == "black"
white == "white"
Color == {black, white}

VARIABLES active, color, tpos, tcolor
vars == <<active, color, tpos, tcolor>>

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ tpos \in Node
  /\ tcolor \in Color

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ tpos \in Node
  /\ tcolor = black

InitiateProbe ==
  /\ tpos = 0
  /\ \/ tcolor = black
     \/ color[0] = black
  /\ tpos' = N-1
  /\ tcolor' = white
  /\ color' = [color EXCEPT ![0] = white]
  /\ UNCHANGED <<active>>

PassToken(i) ==
    /\  \/ ~active[i]
        \* There is no need to wait for this node to terminate if a
        \* higher-numbered node has already marked this round inconclusive.
        \* Instead, the initiator may start a new round (upon receipt of
        \* the token) in the meantime.
        \/ tcolor = black
        \* Likewise, don't wait for this node to terminate, if it is
        \* going to cause an inconclusive round.
        \/ color[i] = black
    /\ tpos = i
    /\ tpos' = i-1
    \* Passing along the token transfers the taint
    \* from the node to the token.
    /\ tcolor' = IF color[i] = black THEN black ELSE tcolor
    /\ color' = [color EXCEPT ![i] = white]
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
            /\ color' = [color EXCEPT ![i] = IF j>i THEN black ELSE @]
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
    Spec /\ WF_vars(Environment)

AlwaysTerminates ==    
    <>[](terminationDetected)

THEOREM SpecWFEnv => AlwaysTerminates

=============================================================================
