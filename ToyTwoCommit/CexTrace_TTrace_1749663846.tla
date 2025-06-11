---- MODULE CexTrace_TTrace_1749663846 ----
EXTENDS CexTrace, Sequences, TLCExt, Toolbox, Naturals, TLC

_expression ==
    LET CexTrace_TEExpression == INSTANCE CexTrace_TEExpression
    IN CexTrace_TEExpression!expression
----

_trace ==
    LET CexTrace_TETrace == INSTANCE CexTrace_TETrace
    IN CexTrace_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        err = (TRUE)
        /\
        Fluent9_0 = ((res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE))
        /\
        rmState = ((res1 :> "commit" @@ res2 :> "abort" @@ res3 :> "working"))
        /\
        Fluent10_0 = ((res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE))
        /\
        cexTraceIdx = (3)
    )
----

_init ==
    /\ Fluent9_0 = _TETrace[1].Fluent9_0
    /\ err = _TETrace[1].err
    /\ Fluent10_0 = _TETrace[1].Fluent10_0
    /\ rmState = _TETrace[1].rmState
    /\ cexTraceIdx = _TETrace[1].cexTraceIdx
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ Fluent9_0  = _TETrace[i].Fluent9_0
        /\ Fluent9_0' = _TETrace[j].Fluent9_0
        /\ err  = _TETrace[i].err
        /\ err' = _TETrace[j].err
        /\ Fluent10_0  = _TETrace[i].Fluent10_0
        /\ Fluent10_0' = _TETrace[j].Fluent10_0
        /\ rmState  = _TETrace[i].rmState
        /\ rmState' = _TETrace[j].rmState
        /\ cexTraceIdx  = _TETrace[i].cexTraceIdx
        /\ cexTraceIdx' = _TETrace[j].cexTraceIdx

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("CexTrace_TTrace_1749663846.json", _TETrace)

=============================================================================

 Note that you can extract this module `CexTrace_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `CexTrace_TEExpression.tla` file takes precedence 
  over the module `CexTrace_TEExpression` below).

---- MODULE CexTrace_TEExpression ----
EXTENDS CexTrace, Sequences, TLCExt, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `CexTrace` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        Fluent9_0 |-> Fluent9_0
        ,err |-> err
        ,Fluent10_0 |-> Fluent10_0
        ,rmState |-> rmState
        ,cexTraceIdx |-> cexTraceIdx
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_Fluent9_0Unchanged |-> Fluent9_0 = Fluent9_0'
        
        \* Format the `Fluent9_0` variable as Json value.
        \* ,_Fluent9_0Json |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(Fluent9_0)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_Fluent9_0ModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].Fluent9_0 # _TETrace[s-1].Fluent9_0
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE CexTrace_TETrace ----
\*EXTENDS CexTrace, IOUtils, TLC
\*
\*trace == IODeserialize("CexTrace_TTrace_1749663846.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE CexTrace_TETrace ----
EXTENDS CexTrace, TLC

trace == 
    <<
    ([err |-> FALSE,Fluent9_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),rmState |-> (res1 :> "working" @@ res2 :> "working" @@ res3 :> "working"),Fluent10_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),cexTraceIdx |-> 0]),
    ([err |-> FALSE,Fluent9_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),rmState |-> (res1 :> "prepared" @@ res2 :> "working" @@ res3 :> "working"),Fluent10_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),cexTraceIdx |-> 1]),
    ([err |-> FALSE,Fluent9_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),rmState |-> (res1 :> "commit" @@ res2 :> "working" @@ res3 :> "working"),Fluent10_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),cexTraceIdx |-> 2]),
    ([err |-> TRUE,Fluent9_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),rmState |-> (res1 :> "commit" @@ res2 :> "abort" @@ res3 :> "working"),Fluent10_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),cexTraceIdx |-> 3])
    >>
----


=============================================================================

---- CONFIG CexTrace_TTrace_1749663846 ----
CONSTANTS
    RMs = { res1 , res2 , res3 }
    res1 = res1
    res3 = res3
    res2 = res2
    res2 = res2
    res3 = res3
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
\* Generated on Wed Jun 11 13:44:06 EDT 2025