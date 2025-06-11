---- MODULE ToyTM_hist_TTrace_1749663820 ----
EXTENDS Sequences, TLCExt, ToyTM_hist, Toolbox, ToyTM_hist_TEConstants, Naturals, TLC

_expression ==
    LET ToyTM_hist_TEExpression == INSTANCE ToyTM_hist_TEExpression
    IN ToyTM_hist_TEExpression!expression
----

_trace ==
    LET ToyTM_hist_TETrace == INSTANCE ToyTM_hist_TETrace
    IN ToyTM_hist_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        Fluent14_0 = ((res1 :> FALSE @@ res2 :> TRUE @@ res3 :> FALSE))
        /\
        tmState = ("abort")
        /\
        tmPrepared = ({res1})
        /\
        Fluent13_0 = ((res1 :> FALSE @@ res2 :> TRUE @@ res3 :> TRUE))
    )
----

_init ==
    /\ Fluent13_0 = _TETrace[1].Fluent13_0
    /\ Fluent14_0 = _TETrace[1].Fluent14_0
    /\ tmState = _TETrace[1].tmState
    /\ tmPrepared = _TETrace[1].tmPrepared
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ Fluent13_0  = _TETrace[i].Fluent13_0
        /\ Fluent13_0' = _TETrace[j].Fluent13_0
        /\ Fluent14_0  = _TETrace[i].Fluent14_0
        /\ Fluent14_0' = _TETrace[j].Fluent14_0
        /\ tmState  = _TETrace[i].tmState
        /\ tmState' = _TETrace[j].tmState
        /\ tmPrepared  = _TETrace[i].tmPrepared
        /\ tmPrepared' = _TETrace[j].tmPrepared

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("ToyTM_hist_TTrace_1749663820.json", _TETrace)

=============================================================================

 Note that you can extract this module `ToyTM_hist_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `ToyTM_hist_TEExpression.tla` file takes precedence 
  over the module `ToyTM_hist_TEExpression` below).

---- MODULE ToyTM_hist_TEExpression ----
EXTENDS Sequences, TLCExt, ToyTM_hist, Toolbox, ToyTM_hist_TEConstants, Naturals, TLC

expression == 
    [
        \* To hide variables of the `ToyTM_hist` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        Fluent13_0 |-> Fluent13_0
        ,Fluent14_0 |-> Fluent14_0
        ,tmState |-> tmState
        ,tmPrepared |-> tmPrepared
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_Fluent13_0Unchanged |-> Fluent13_0 = Fluent13_0'
        
        \* Format the `Fluent13_0` variable as Json value.
        \* ,_Fluent13_0Json |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(Fluent13_0)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_Fluent13_0ModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].Fluent13_0 # _TETrace[s-1].Fluent13_0
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE ToyTM_hist_TETrace ----
\*EXTENDS IOUtils, ToyTM_hist, ToyTM_hist_TEConstants, TLC
\*
\*trace == IODeserialize("ToyTM_hist_TTrace_1749663820.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE ToyTM_hist_TETrace ----
EXTENDS ToyTM_hist, ToyTM_hist_TEConstants, TLC

trace == 
    <<
    ([Fluent14_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),tmState |-> "init",tmPrepared |-> {},Fluent13_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE)]),
    ([Fluent14_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),tmState |-> "init",tmPrepared |-> {res1},Fluent13_0 |-> (res1 :> FALSE @@ res2 :> TRUE @@ res3 :> TRUE)]),
    ([Fluent14_0 |-> (res1 :> FALSE @@ res2 :> TRUE @@ res3 :> FALSE),tmState |-> "abort",tmPrepared |-> {res1},Fluent13_0 |-> (res1 :> FALSE @@ res2 :> TRUE @@ res3 :> TRUE)])
    >>
----


=============================================================================

---- MODULE ToyTM_hist_TEConstants ----
EXTENDS ToyTM_hist

CONSTANTS res1, res2, res3

=============================================================================

---- CONFIG ToyTM_hist_TTrace_1749663820 ----
CONSTANTS
    RMs = { res1 , res2 , res3 }
    res1 = res1
    res3 = res3
    res2 = res2

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
\* Generated on Wed Jun 11 13:43:40 EDT 2025