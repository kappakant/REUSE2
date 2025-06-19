---- MODULE ToyRM_hist_TTrace_1750318441 ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, ToyRM_hist, ToyRM_hist_TEConstants

_expression ==
    LET ToyRM_hist_TEExpression == INSTANCE ToyRM_hist_TEExpression
    IN ToyRM_hist_TEExpression!expression
----

_trace ==
    LET ToyRM_hist_TETrace == INSTANCE ToyRM_hist_TETrace
    IN ToyRM_hist_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        rmState = ((res1 :> "abort" @@ res2 :> "commit" @@ res3 :> "working"))
    )
----

_init ==
    /\ rmState = _TETrace[1].rmState
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ rmState  = _TETrace[i].rmState
        /\ rmState' = _TETrace[j].rmState

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("ToyRM_hist_TTrace_1750318441.json", _TETrace)

=============================================================================

 Note that you can extract this module `ToyRM_hist_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `ToyRM_hist_TEExpression.tla` file takes precedence 
  over the module `ToyRM_hist_TEExpression` below).

---- MODULE ToyRM_hist_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, ToyRM_hist, ToyRM_hist_TEConstants

expression == 
    [
        \* To hide variables of the `ToyRM_hist` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        rmState |-> rmState
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_rmStateUnchanged |-> rmState = rmState'
        
        \* Format the `rmState` variable as Json value.
        \* ,_rmStateJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(rmState)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_rmStateModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].rmState # _TETrace[s-1].rmState
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE ToyRM_hist_TETrace ----
\*EXTENDS IOUtils, TLC, ToyRM_hist, ToyRM_hist_TEConstants
\*
\*trace == IODeserialize("ToyRM_hist_TTrace_1750318441.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE ToyRM_hist_TETrace ----
EXTENDS TLC, ToyRM_hist, ToyRM_hist_TEConstants

trace == 
    <<
    ([rmState |-> (res1 :> "working" @@ res2 :> "working" @@ res3 :> "working")]),
    ([rmState |-> (res1 :> "prepared" @@ res2 :> "working" @@ res3 :> "working")]),
    ([rmState |-> (res1 :> "abort" @@ res2 :> "working" @@ res3 :> "working")]),
    ([rmState |-> (res1 :> "abort" @@ res2 :> "commit" @@ res3 :> "working")])
    >>
----


=============================================================================

---- MODULE ToyRM_hist_TEConstants ----
EXTENDS ToyRM_hist

CONSTANTS res1, res2, res3

=============================================================================

---- CONFIG ToyRM_hist_TTrace_1750318441 ----
CONSTANTS
    RMs = { res1 , res2 , res3 }
    res3 = res3
    res2 = res2
    res1 = res1

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Thu Jun 19 03:34:02 EDT 2025