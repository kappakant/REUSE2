---- MODULE CexTrace_TTrace_1749661862 ----
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
        Fluent9_0 = ((res1 :> FALSE @@ res2 :> TRUE @@ res3 :> FALSE))
        /\
        Fluent8_0 = ((res1 :> FALSE @@ res2 :> TRUE @@ res3 :> FALSE))
        /\
        rmState = ((res1 :> "prepared" @@ res2 :> "abort" @@ res3 :> "commit"))
        /\
        cexTraceIdx = (4)
    )
----

_init ==
    /\ Fluent8_0 = _TETrace[1].Fluent8_0
    /\ Fluent9_0 = _TETrace[1].Fluent9_0
    /\ err = _TETrace[1].err
    /\ rmState = _TETrace[1].rmState
    /\ cexTraceIdx = _TETrace[1].cexTraceIdx
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ Fluent8_0  = _TETrace[i].Fluent8_0
        /\ Fluent8_0' = _TETrace[j].Fluent8_0
        /\ Fluent9_0  = _TETrace[i].Fluent9_0
        /\ Fluent9_0' = _TETrace[j].Fluent9_0
        /\ err  = _TETrace[i].err
        /\ err' = _TETrace[j].err
        /\ rmState  = _TETrace[i].rmState
        /\ rmState' = _TETrace[j].rmState
        /\ cexTraceIdx  = _TETrace[i].cexTraceIdx
        /\ cexTraceIdx' = _TETrace[j].cexTraceIdx

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("CexTrace_TTrace_1749661862.json", _TETrace)

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
        Fluent8_0 |-> Fluent8_0
        ,Fluent9_0 |-> Fluent9_0
        ,err |-> err
        ,rmState |-> rmState
        ,cexTraceIdx |-> cexTraceIdx
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_Fluent8_0Unchanged |-> Fluent8_0 = Fluent8_0'
        
        \* Format the `Fluent8_0` variable as Json value.
        \* ,_Fluent8_0Json |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(Fluent8_0)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_Fluent8_0ModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].Fluent8_0 # _TETrace[s-1].Fluent8_0
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
\*trace == IODeserialize("CexTrace_TTrace_1749661862.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE CexTrace_TETrace ----
EXTENDS CexTrace, TLC

trace == 
    <<
    ([err |-> FALSE,Fluent9_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),Fluent8_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),rmState |-> (res1 :> "working" @@ res2 :> "working" @@ res3 :> "working"),cexTraceIdx |-> 0]),
    ([err |-> FALSE,Fluent9_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),Fluent8_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),rmState |-> (res1 :> "prepared" @@ res2 :> "working" @@ res3 :> "working"),cexTraceIdx |-> 1]),
    ([err |-> FALSE,Fluent9_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),Fluent8_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),rmState |-> (res1 :> "prepared" @@ res2 :> "prepared" @@ res3 :> "working"),cexTraceIdx |-> 2]),
    ([err |-> FALSE,Fluent9_0 |-> (res1 :> FALSE @@ res2 :> TRUE @@ res3 :> FALSE),Fluent8_0 |-> (res1 :> FALSE @@ res2 :> TRUE @@ res3 :> FALSE),rmState |-> (res1 :> "prepared" @@ res2 :> "abort" @@ res3 :> "working"),cexTraceIdx |-> 3]),
    ([err |-> TRUE,Fluent9_0 |-> (res1 :> FALSE @@ res2 :> TRUE @@ res3 :> FALSE),Fluent8_0 |-> (res1 :> FALSE @@ res2 :> TRUE @@ res3 :> FALSE),rmState |-> (res1 :> "prepared" @@ res2 :> "abort" @@ res3 :> "commit"),cexTraceIdx |-> 4])
    >>
----


=============================================================================

---- CONFIG CexTrace_TTrace_1749661862 ----
CONSTANTS
    RMs = { res1 , res2 , res3 }
    res1 = res1
    res3 = res3
    res2 = res2
    res1 = res1
    res2 = res2
    res3 = res3

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
\* Generated on Wed Jun 11 13:11:03 EDT 2025