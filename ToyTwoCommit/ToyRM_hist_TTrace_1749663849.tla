---- MODULE ToyRM_hist_TTrace_1749663849 ----
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
        Fluent15_0 = ((res1 :> TRUE @@ res2 :> FALSE @@ res3 :> TRUE))
        /\
        Fluent6_0 = ((res1 :> TRUE @@ res2 :> FALSE @@ res3 :> TRUE))
        /\
        Fluent14_0 = ((res1 :> FALSE @@ res2 :> TRUE @@ res3 :> FALSE))
        /\
        Fluent7_0 = ((res1 :> TRUE @@ res2 :> TRUE @@ res3 :> TRUE))
        /\
        rmState = ((res1 :> "commit" @@ res2 :> "abort" @@ res3 :> "prepared"))
    )
----

_init ==
    /\ Fluent7_0 = _TETrace[1].Fluent7_0
    /\ rmState = _TETrace[1].rmState
    /\ Fluent14_0 = _TETrace[1].Fluent14_0
    /\ Fluent15_0 = _TETrace[1].Fluent15_0
    /\ Fluent6_0 = _TETrace[1].Fluent6_0
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ Fluent7_0  = _TETrace[i].Fluent7_0
        /\ Fluent7_0' = _TETrace[j].Fluent7_0
        /\ rmState  = _TETrace[i].rmState
        /\ rmState' = _TETrace[j].rmState
        /\ Fluent14_0  = _TETrace[i].Fluent14_0
        /\ Fluent14_0' = _TETrace[j].Fluent14_0
        /\ Fluent15_0  = _TETrace[i].Fluent15_0
        /\ Fluent15_0' = _TETrace[j].Fluent15_0
        /\ Fluent6_0  = _TETrace[i].Fluent6_0
        /\ Fluent6_0' = _TETrace[j].Fluent6_0

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("ToyRM_hist_TTrace_1749663849.json", _TETrace)

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
        Fluent7_0 |-> Fluent7_0
        ,rmState |-> rmState
        ,Fluent14_0 |-> Fluent14_0
        ,Fluent15_0 |-> Fluent15_0
        ,Fluent6_0 |-> Fluent6_0
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_Fluent7_0Unchanged |-> Fluent7_0 = Fluent7_0'
        
        \* Format the `Fluent7_0` variable as Json value.
        \* ,_Fluent7_0Json |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(Fluent7_0)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_Fluent7_0ModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].Fluent7_0 # _TETrace[s-1].Fluent7_0
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
\*trace == IODeserialize("ToyRM_hist_TTrace_1749663849.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE ToyRM_hist_TETrace ----
EXTENDS TLC, ToyRM_hist, ToyRM_hist_TEConstants

trace == 
    <<
    ([Fluent15_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),Fluent6_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),Fluent14_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),Fluent7_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),rmState |-> (res1 :> "working" @@ res2 :> "working" @@ res3 :> "working")]),
    ([Fluent15_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),Fluent6_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),Fluent14_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),Fluent7_0 |-> (res1 :> TRUE @@ res2 :> FALSE @@ res3 :> FALSE),rmState |-> (res1 :> "prepared" @@ res2 :> "working" @@ res3 :> "working")]),
    ([Fluent15_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),Fluent6_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),Fluent14_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),Fluent7_0 |-> (res1 :> TRUE @@ res2 :> TRUE @@ res3 :> FALSE),rmState |-> (res1 :> "prepared" @@ res2 :> "prepared" @@ res3 :> "working")]),
    ([Fluent15_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),Fluent6_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),Fluent14_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),Fluent7_0 |-> (res1 :> TRUE @@ res2 :> TRUE @@ res3 :> TRUE),rmState |-> (res1 :> "prepared" @@ res2 :> "prepared" @@ res3 :> "prepared")]),
    ([Fluent15_0 |-> (res1 :> FALSE @@ res2 :> TRUE @@ res3 :> TRUE),Fluent6_0 |-> (res1 :> FALSE @@ res2 :> TRUE @@ res3 :> TRUE),Fluent14_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),Fluent7_0 |-> (res1 :> TRUE @@ res2 :> TRUE @@ res3 :> TRUE),rmState |-> (res1 :> "commit" @@ res2 :> "prepared" @@ res3 :> "prepared")]),
    ([Fluent15_0 |-> (res1 :> TRUE @@ res2 :> FALSE @@ res3 :> TRUE),Fluent6_0 |-> (res1 :> TRUE @@ res2 :> FALSE @@ res3 :> TRUE),Fluent14_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),Fluent7_0 |-> (res1 :> TRUE @@ res2 :> TRUE @@ res3 :> TRUE),rmState |-> (res1 :> "commit" @@ res2 :> "commit" @@ res3 :> "prepared")]),
    ([Fluent15_0 |-> (res1 :> TRUE @@ res2 :> FALSE @@ res3 :> TRUE),Fluent6_0 |-> (res1 :> TRUE @@ res2 :> FALSE @@ res3 :> TRUE),Fluent14_0 |-> (res1 :> FALSE @@ res2 :> TRUE @@ res3 :> FALSE),Fluent7_0 |-> (res1 :> TRUE @@ res2 :> TRUE @@ res3 :> TRUE),rmState |-> (res1 :> "commit" @@ res2 :> "abort" @@ res3 :> "prepared")])
    >>
----


=============================================================================

---- MODULE ToyRM_hist_TEConstants ----
EXTENDS ToyRM_hist

CONSTANTS res1, res2, res3

=============================================================================

---- CONFIG ToyRM_hist_TTrace_1749663849 ----
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
\* Generated on Wed Jun 11 13:44:09 EDT 2025