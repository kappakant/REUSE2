//13
//0
open util/boolean
open util/ordering[Idx] as IdxOrder
open util/ordering[ParamIdx] as ParamIdxOrder

abstract sig Var {}

abstract sig Atom {}

abstract sig Sort {
	atoms : some Atom,
	numericSort : Bool
}

abstract sig ParamIdx {}

// base name for an action
abstract sig BaseName {
	paramIdxs : set ParamIdx,
	paramTypes : set(ParamIdx->Sort)
}

// concrete action
abstract sig Act {
	baseName : BaseName,
	params : ParamIdx->Atom
}


/* Formula signatures (represented by a DAG) */
abstract sig Formula {
	children : set Formula
}

sig Not extends Formula {
	child : Formula
} {
	children = child
	child in (Fluent + VarEquals + VarSetContains + VarLTE)
}

sig Implies extends Formula {
	left : Formula,
	right : Formula
} {
	children = left + right
	left != right
	not (left in Not and right in Not) // for readability
}

sig FlSymAction {
    baseName : BaseName,

    // flToActParamsMap maps fluent-param idxs to action-param idxs.
    // in other words, flToActParamsMap decides which of the action-params will be
    // used for setting a boolean value of the state variable (representing the
    // fluent) in the _hist TLA+ code.
    flToActParamsMap : set(ParamIdx->ParamIdx),

    value : Bool, // init v. term
    mutexFl : Bool
} {
    // domain(flToActParamsMap) must be a sequence of P0, P1, ... (i.e. no gaps between param numbers)
    (no flToActParamsMap) or (P0 in flToActParamsMap.ParamIdx)
    (flToActParamsMap.ParamIdx).*(~ParamIdxOrder/next) = flToActParamsMap.ParamIdx

    // range(flToActParamsMap) \subseteq paramIdxs(baseName), i.e. the range must be valid param idxs
    ParamIdx.flToActParamsMap in baseName.paramIdxs

    // flToActParamsMap is a function
    all k,v1,v2 : ParamIdx | (k->v1 in flToActParamsMap and k->v2 in flToActParamsMap) implies (v1 = v2)

    // flToActParamsMap is injective
    // this is an overconstraint for improving speed
    all k1,k2,v : ParamIdx | (k1->v in flToActParamsMap and k2->v in flToActParamsMap) implies (k1 = k2)

    // constraints for improving speed, but sacrifice expressivity
    (mutexFl = True) implies (value = True)
}

sig Fluent extends Formula {
    initially : Bool,
    flActions : some FlSymAction,

    // vars represents the parameters (including the ordering) to the fluent itself
    vars : set(ParamIdx->Var)
} {
    no children
    some vars

    initially = False // makes the fluent easier to read, but doesn't sacrifice expressivity (because of Not)

    // each param to the fluent must be used by some fl action
    (flActions.flToActParamsMap).ParamIdx = vars.Var

    // strong condition for ensuring each fluent category is mutex
    all fl1,fl2 : flActions | (some fl1.baseName & fl2.baseName) implies fl1 = fl2

    // vars is a function
    all p : ParamIdx, v1,v2 : Var | (p->v1 in vars and p->v2 in vars) implies (v1 = v2)

    // each action must input the same param-types to the fluent
    let flParamTypes = vars.envVarTypes |
        all a : flActions |
            // for each param in the action, its type must match the fluent
            all actIdx : ParamIdx.(a.flToActParamsMap) |
                let flIdx = (a.flToActParamsMap).actIdx |
                    flIdx.flParamTypes = actIdx.(a.baseName.paramTypes)

    // flToActParamsMap is an injective function across all actions
    // this is an overconstraint for improving speed
    all x1,x2,y1,y2 : ParamIdx |
        (x1->y1 in flActions.flToActParamsMap and x2->y2 in flActions.flToActParamsMap) implies (x1->y1 = x2->y2 or (not x1=x2 and not y1=y2))
}

sig VarEquals extends Formula {
    lhs : Var,
    rhs : Var
} {
	no children
	lhs != rhs
	lhs.envVarTypes = rhs.envVarTypes // only compare vars of the same type
}

sig VarSetContains extends Formula {
    elem : Var,
    theSet : Var
} {
	no children
	elem != theSet
	isElemOfSet[elem.envVarTypes, theSet.envVarTypes]
}

sig VarLTE extends Formula {
    sort : Sort,
    lhs : Var,
    rhs : Var
} {
	no children
	lhs != rhs
	lhs.envVarTypes = sort
	rhs.envVarTypes = sort
	sort.numericSort = True // the sort type must be numeric
}

sig Forall extends Formula {
	var : Var,
	sort : Sort,
	matrix : Formula
} {
	children = matrix
}

sig Exists extends Formula {
	var : Var,
	sort : Sort,
	matrix : Formula
} {
	children = matrix
}

one sig Root extends Formula {} {
	one children
}

fact {
	// the following two facts make sure that the formulas create a tree (i.e. DAG w/o 'diamond' structures)
	no Root.(~children) // the root has no parents
	all f : (Formula - Root) | one f.(~children) // all non-root formulas have exactly one parent
	all f : Formula | f in Root.*children // all Formulas must be part of the overall formula
	Fluent.flActions = FlSymAction // all FlSymActions must be in fluents
	all f1,f2 : Fluent, a : FlSymAction | (a in f1.flActions and a in f2.flActions) implies f1 = f2 // no sharing FlSymActions

	// no free vars, all vars must be used in the matrix
	let varsInMatrix = ParamIdx.(Fluent.vars) + VarEquals.(lhs+rhs) + VarSetContains.(elem+theSet) + VarLTE.(lhs+rhs) |
		varsInMatrix = (Forall.var + Exists.var)

	// do not quantify over a variable that's already in scope
	all f1, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1 : Forall, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1 : Exists, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)

	// require lhs to not have have an Implies node
	// this is an overconstraint for improving speed
	all f : Implies | no (f.left.*children) & Implies

	(Forall+Exists).^(~children) in (Root+Forall+Exists) // prenex normal form
	some Implies // non-degenerate formulas

	// constraints for improving speed, but sacrifice expressivity
	lone mutInitFluents // at most one mutex action per formula
}


abstract sig Env {
	maps : set(Var -> Atom)
}
one sig EmptyEnv extends Env {} {
	no maps
}

abstract sig Idx {}

abstract sig Trace {
	path : Idx -> Act, // the path for the trace
	lastIdx : Idx, // the last index in the path for the trace
	satisfies : Env -> Idx -> Formula // formulas that satisfy this trace
} {
	// trace semantics, i.e. e |- t,i |= f, where e is an environment, t is a trace, i is an index, and f is a formula
	all e : Env, i : Idx, f : Not | e->i->f in satisfies iff (e->i->f.child not in satisfies)
	all e : Env, i : Idx, f : Implies | e->i->f in satisfies iff (e->i->f.left in satisfies implies e->i->f.right in satisfies)
	all e : Env, i : Idx, f : VarEquals | e->i->f in satisfies iff (f.lhs).(e.maps) = (f.rhs).(e.maps)
	all e : Env, i : Idx, f : VarSetContains | e->i->f in satisfies iff setContains[(f.theSet).(e.maps), (f.elem).(e.maps)]
	all e : Env, i : Idx, f : VarLTE | e->i->f in satisfies iff lte[(f.lhs).(e.maps), (f.rhs).(e.maps)]

	// e |- t,i |= f (where f is a fluent) iff any (the disjunction) of the following three hold:
	// 1. t[i] \in f.initFl
	// 2. t[i] \notin f.termFl and i = 0 and f.initally = True
	// 3. t[i] \notin f.termFl and (e |- t,i-1 |= f)
	all e : Env, i : Idx, f : Fluent | e->i->f in satisfies iff
        // a is the action at the current index i in the trace (i.e. a = t[i])
        let a = i.path |
            (isInitAct[a,e,f]) or
            (not isTermAct[a,e,f] and no i.prev and f.initially = True) or
            (not isTermAct[a,e,f] and some i.prev and e->(i.prev)->f in satisfies)

	all e : Env, i : Idx, f : Forall | e->i->f in satisfies iff
		(all x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->i->f.matrix in satisfies)
	all e : Env, i : Idx, f : Exists | e->i->f in satisfies iff
		(some x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->i->f.matrix in satisfies)
	all e : Env, i : Idx, f : Root | e->i->f in satisfies iff e->i->f.children in satisfies
}

// does this action initiate the fluent?
pred isInitAct[a : Act, e : Env, f : Fluent] {
    // init fluents, both usual and mutex
    (some s : f.flActions |
        s.value = True and a.baseName = s.baseName and (~(f.vars)).(s.flToActParamsMap).(a.params) in e.maps)
    or
    // mutex term fluents
    (some s : f.flActions |
        s.mutexFl = True and s.value = False and a.baseName = s.baseName and (~(f.vars)).(s.flToActParamsMap).(a.params) not in e.maps)
}

// does this action terminate the fluent?
pred isTermAct[a : Act, e : Env, f : Fluent] {
    // term fluents, both usual and mutex
    (some s : f.flActions |
        s.value = False and a.baseName = s.baseName and (~(f.vars)).(s.flToActParamsMap).(a.params) in e.maps)
    or
    // mutex init fluents
    (some s : f.flActions |
        s.mutexFl = True and s.value = True and a.baseName = s.baseName and (~(f.vars)).(s.flToActParamsMap).(a.params) not in e.maps)
}

pred pushEnv[env', env : Env, v : Var, x : Atom] {
	env'.maps = env.maps + (v->x)
}

fun indices[t : Trace] : set Idx {
	t.lastIdx.*(~IdxOrder/next)
}

fun rangeParamIdx[p : ParamIdx] : set ParamIdx {
	p.*(~ParamIdxOrder/next)
}

abstract sig PosTrace extends Trace {} {}
abstract sig NegTrace extends Trace {} {}
one sig EmptyTrace extends Trace {} {
	 no path
}


fun mutInitFluents : set FlSymAction {
	 { a : FlSymAction | a.mutexFl = True }
}

	// 'partial fluents' are fluents that do not update every param in the fluent (and hence, in practice,
	// update every sort value of the missing param).
fun partialFluents : set FlSymAction {
	 { a : FlSymAction | some f : Fluent | a in f.flActions and a.flToActParamsMap.ParamIdx != f.vars.Var }
}


/* main */
run {
	// find a formula that separates "good" traces from "bad" ones
	all pt : PosTrace | EmptyEnv->indices[pt]->Root in pt.satisfies
	all nt : NegTrace | no (EmptyEnv->nt.lastIdx->Root & nt.satisfies)
	EmptyEnv->T0->Root in EmptyTrace.satisfies // the formula must satisfy the empty trace

	// minimization constraints
	softno mutInitFluents // fewer mutex fluents
	softno partialFluents // fewer partial fluents
	minsome Formula.children & (Forall+Exists+Fluent+VarEquals+VarSetContains+VarLTE) // smallest formula possible, counting only quants and terminals
	minsome flActions // heuristic to synthesize the least complicated fluents as possible
	minsome Fluent.vars // minimize the # of params for each fluent
}
for 8 Formula, 4 FlSymAction

one sig P0 extends ParamIdx {}

fact {
	ParamIdxOrder/first = P0
	ParamIdxOrder/next = none->none
	all f : Fluent | (f.vars.Var = P0)
}



pred setContains[s : Atom, e : Atom] {
	let containsRel = (none->none) |
		(s->e) in containsRel
}


pred isElemOfSet[e : Sort, s : Sort] {
	let elemOfRel = (none->none) |
		(e->s) in elemOfRel
}


pred lte[lhs : Atom, rhs : Atom] {
	let containsRel = (none->none) |
		(lhs->rhs) in containsRel
}


one sig res1, res3, res2 extends Atom {}

one sig RMs extends Sort {} {
	atoms = res1 + res3 + res2
	numericSort = False
}

one sig SndAbort extends BaseName {} {
	paramIdxs = P0
	paramTypes = P0->RMs
}
one sig SndAbortres1 extends Act {} {
	params = (P0->res1)
}
one sig SndAbortres3 extends Act {} {
	params = (P0->res3)
}

one sig RcvPrepare extends BaseName {} {
	paramIdxs = P0
	paramTypes = P0->RMs
}
one sig RcvPrepareres2 extends Act {} {
	params = (P0->res2)
}
one sig RcvPrepareres1 extends Act {} {
	params = (P0->res1)
}
one sig RcvPrepareres3 extends Act {} {
	params = (P0->res3)
}

one sig SndCommit extends BaseName {} {
	paramIdxs = P0
	paramTypes = P0->RMs
}
one sig SndCommitres2 extends Act {} {
	params = (P0->res2)
}
one sig SndCommitres1 extends Act {} {
	params = (P0->res1)
}


one sig T0, T1, T2, T3, T4 extends Idx {}

fact {
	IdxOrder/first = T0
	IdxOrder/next = T0->T1 + T1->T2 + T2->T3 + T3->T4
	SndCommit in FlSymAction.baseName // the final base name in the neg trace must appear in the sep formula
}


fun envVarTypes : set(Var->Sort) {
	var2->RMs + var1->RMs + var0->RMs
}


one sig var2, var1, var0 extends Var {} {}


one sig var0tores1 extends Env {} {}
one sig var1tores1var0tores1 extends Env {} {}
one sig var2tores1var1tores1var0tores1 extends Env {} {}
one sig var2tores1var1tores1var0tores3 extends Env {} {}
one sig var2tores1var0tores1var1tores3 extends Env {} {}
one sig var1tores2var0tores2var2tores1 extends Env {} {}
one sig var0tores2var1tores3 extends Env {} {}
one sig var1tores2var0tores3 extends Env {} {}
one sig var1tores1var0tores1var2tores3 extends Env {} {}
one sig var2tores2var0tores2var1tores1 extends Env {} {}
one sig var2tores2var1tores2var0tores1 extends Env {} {}
one sig var0tores2var2tores1var1tores1 extends Env {} {}
one sig var1tores2var2tores1var0tores1 extends Env {} {}
one sig var2tores2var1tores1var0tores1 extends Env {} {}
one sig var1tores1var0tores3 extends Env {} {}
one sig var0tores1var1tores3 extends Env {} {}
one sig var1tores2var0tores2 extends Env {} {}
one sig var0tores2var2tores1var1tores3 extends Env {} {}
one sig var1tores2var2tores1var0tores3 extends Env {} {}
one sig var0tores2var1tores1var2tores3 extends Env {} {}
one sig var1tores2var0tores1var2tores3 extends Env {} {}
one sig var2tores2var1tores1var0tores3 extends Env {} {}
one sig var2tores2var0tores1var1tores3 extends Env {} {}
one sig var2tores2var1tores2var0tores2 extends Env {} {}
one sig var0tores2var1tores1 extends Env {} {}
one sig var1tores2var0tores1 extends Env {} {}
one sig var0tores2var2tores3var1tores3 extends Env {} {}
one sig var1tores2var2tores3var0tores3 extends Env {} {}
one sig var2tores2var1tores3var0tores3 extends Env {} {}
one sig var0tores2 extends Env {} {}
one sig var2tores1var1tores3var0tores3 extends Env {} {}
one sig var1tores1var2tores3var0tores3 extends Env {} {}
one sig var0tores1var2tores3var1tores3 extends Env {} {}
one sig var1tores2var0tores2var2tores3 extends Env {} {}
one sig var2tores2var0tores2var1tores3 extends Env {} {}
one sig var2tores2var1tores2var0tores3 extends Env {} {}
one sig var2tores3var1tores3var0tores3 extends Env {} {}
one sig var0tores3 extends Env {} {}
one sig var1tores3var0tores3 extends Env {} {}


fact PartialInstance {
	lastIdx = (EmptyTrace->T0) + (PT2->T0) + (PT3->T1) + (PT1->T4) + (NT1->T4)

	path = (PT2 -> (T0->SndCommitres1)) +
		(PT3 -> (T0->RcvPrepareres1 + T1->SndCommitres1)) +
		(PT1 -> (T0->RcvPrepareres1 + T1->RcvPrepareres2 + T2->RcvPrepareres3 + T3->SndAbortres1 + T4->SndAbortres3)) +
		(NT1 -> (T0->RcvPrepareres1 + T1->RcvPrepareres2 + T2->RcvPrepareres3 + T3->SndAbortres1 + T4->SndCommitres2))

	maps = var0tores1->(var0->res1) +
		var1tores1var0tores1->(var1->res1 + var0->res1) +
		var2tores1var1tores1var0tores1->(var2->res1 + var1->res1 + var0->res1) +
		var2tores1var1tores1var0tores3->(var2->res1 + var1->res1 + var0->res3) +
		var2tores1var0tores1var1tores3->(var2->res1 + var0->res1 + var1->res3) +
		var1tores2var0tores2var2tores1->(var1->res2 + var0->res2 + var2->res1) +
		var0tores2var1tores3->(var0->res2 + var1->res3) +
		var1tores2var0tores3->(var1->res2 + var0->res3) +
		var1tores1var0tores1var2tores3->(var1->res1 + var0->res1 + var2->res3) +
		var2tores2var0tores2var1tores1->(var2->res2 + var0->res2 + var1->res1) +
		var2tores2var1tores2var0tores1->(var2->res2 + var1->res2 + var0->res1) +
		var0tores2var2tores1var1tores1->(var0->res2 + var2->res1 + var1->res1) +
		var1tores2var2tores1var0tores1->(var1->res2 + var2->res1 + var0->res1) +
		var2tores2var1tores1var0tores1->(var2->res2 + var1->res1 + var0->res1) +
		var1tores1var0tores3->(var1->res1 + var0->res3) +
		var0tores1var1tores3->(var0->res1 + var1->res3) +
		var1tores2var0tores2->(var1->res2 + var0->res2) +
		var0tores2var2tores1var1tores3->(var0->res2 + var2->res1 + var1->res3) +
		var1tores2var2tores1var0tores3->(var1->res2 + var2->res1 + var0->res3) +
		var0tores2var1tores1var2tores3->(var0->res2 + var1->res1 + var2->res3) +
		var1tores2var0tores1var2tores3->(var1->res2 + var0->res1 + var2->res3) +
		var2tores2var1tores1var0tores3->(var2->res2 + var1->res1 + var0->res3) +
		var2tores2var0tores1var1tores3->(var2->res2 + var0->res1 + var1->res3) +
		var2tores2var1tores2var0tores2->(var2->res2 + var1->res2 + var0->res2) +
		var0tores2var1tores1->(var0->res2 + var1->res1) +
		var1tores2var0tores1->(var1->res2 + var0->res1) +
		var0tores2var2tores3var1tores3->(var0->res2 + var2->res3 + var1->res3) +
		var1tores2var2tores3var0tores3->(var1->res2 + var2->res3 + var0->res3) +
		var2tores2var1tores3var0tores3->(var2->res2 + var1->res3 + var0->res3) +
		var0tores2->(var0->res2) +
		var2tores1var1tores3var0tores3->(var2->res1 + var1->res3 + var0->res3) +
		var1tores1var2tores3var0tores3->(var1->res1 + var2->res3 + var0->res3) +
		var0tores1var2tores3var1tores3->(var0->res1 + var2->res3 + var1->res3) +
		var1tores2var0tores2var2tores3->(var1->res2 + var0->res2 + var2->res3) +
		var2tores2var0tores2var1tores3->(var2->res2 + var0->res2 + var1->res3) +
		var2tores2var1tores2var0tores3->(var2->res2 + var1->res2 + var0->res3) +
		var2tores3var1tores3var0tores3->(var2->res3 + var1->res3 + var0->res3) +
		var0tores3->(var0->res3) +
		var1tores3var0tores3->(var1->res3 + var0->res3)

	baseName = RcvPrepareres1->RcvPrepare +
		RcvPrepareres3->RcvPrepare +
		SndCommitres2->SndCommit +
		RcvPrepareres2->RcvPrepare +
		SndCommitres1->SndCommit +
		SndAbortres1->SndAbort +
		SndAbortres3->SndAbort
}


fact {
	#(Forall + Exists) <= 3 // allow only 3 quantifiers
	Root.children in Forall // the first quantifier must be a forall
}


one sig NT1 extends NegTrace {} {}

one sig PT2 extends PosTrace {} {}
one sig PT3 extends PosTrace {} {}
one sig PT1 extends PosTrace {} {}
