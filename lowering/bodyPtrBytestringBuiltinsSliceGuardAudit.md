# Slice global success guard diagnostic

C1.slice.guard. Audit only, no new AST fixture, target change or assumed lemma.
E0131's exact residual was read from TO_bytestring-20261106T070926Z_m5045_t001.
It retains all actual entry premises, typed child pre, and:

  forall s tv t s1 v t1.
    eval_expr cx src s = (INL tv,t) ==>
    read_result cx tv s1 <> (INL v,t1)

The remaining goal is expr_sim_ptr ... start es. This is GLOBAL guard failure,
not merely failure of src at the current es. It survived the complete code,
reservation, gas-admissibility, state/ghost and PC premise set. No contradiction
or full target counterexample was established in E0131.

## Literal normalization

bodyPtrPreds 61-67 gives, for [src,start,len]:
body_expr_ptr_ok cx src AND
((exists s tv t s1 v t1. eval_expr cx src s=(INL tv,t) AND
 read_result cx tv s1=(INL v,t1)) ==>
 (body_expr_ptr_ok cx start AND
  ((exists u tw u' u1 w u1'. eval_expr cx start u=(INL tw,u') AND
    read_result cx tw u1=(INL w,u1')) ==> body_expr_ptr_ok cx len))).

s1 is independent of t; likewise u1 independent of u'. No typing, consistency,
source gas state, reachability, or relation to the queried es restricts these
existential states. One exception in a current state never negates this guard.
In particular the existing OrderProbe's Pop address can succeed in its explicit
two-element arr scopes; it is not evidence of global source failure. Ordinary
Name failures may similarly disappear by choosing another source scope state.

## Compiler/evaluator branch table

slice_source_action (SliceDispatch 128-137) uses eval_exprs [src,start,len] in
surface order, including read_result. The compile cuts expose:

| branch | compiler first / next | judgment and precondition issues |
|---|---|---|
| msg.data | start, len, calldata slice | source is special syntactic accessor; typed start pre from expr_body_pre_builtin_typed_arg; source success guard must be justified at fixed cx if used, not from current success |
| self.code | start, len, code slice | same compiler-first obligation; source accessor depends on cx/module deployment data, which cannot be changed by choosing source states |
| extcode | start, len, allocate output, address expression, extcode copy | source is Acc Code [addr]; source pre does NOT automatically transfer via ordinary builtin-head lemma (explicit is_extcode exclusion). Typed word start pre still follows, but body pointer judgment for start is behind global src guard. Later address judgment is not literally one of the outer operand judgments; requires precise wrapper/address relation. |
| ordinary bytestring | src, length/data loads, start, len, slice copy | src head body judgment available unconditionally and child body pre via ordinary-head lemma; its successful simulation can unlock tail judgments in normal continuation. Exceptional src is handled before compiler evaluates tail. |
| ordinary fixed bytes | src, scratch allocation/store, start, len, slice | same source-first structure; full-word scratch stores separate safety obligations. |

expr_body_pre supplies expr_sim_inv, queried whole-expression typing, widths,
allocation limits, call evaluation safety/module conditions, no EVM-run and ABI
conditions. E0131 already derived typed start expr_body_pre at es. Typing does
not imply body_expr_ptr_ok of that word expression. Source evaluation exceptions
are compatible with gas_admissible and do not imply immediate target halt before
the compiler-first start instructions execute.

## Can an arbitrary-state witness always unlock the guard?

Not established. For state-dependent failures (missing local or empty Pop array),
independent existential states may repair the source. But context-dependent
failure and state-independent failing subexpressions cannot be repaired by
changing scopes/accounts/gas alone. Source syntax may include a well-typed checked
arithmetic error as the address producer, or a context accessor with no valid
module data. A blanket witness lemma from well_typed_expr would require proving
success for these branches and is not justified. This audit does NOT introduce
one or claim a particular concrete source globally fails without a check.

The smallest ALREADY CHECKED order fixture is OrderProbe's Acc Code [Pop arr].
It is NOT globally failing: order_probe_pop_read and order_probe_source_slice
supply successful instances with chosen scopes/accounts. No already-studied
checked globally-failing source was located in the inspected evidence. E0131
is a symbolic global-failure branch, not a concrete globally failing AST. A new
concrete falsification probe would need explicit strategist authorization; do
not mislabel the current-state OrderProbe as that probe.

## Precise next obligation / counterexample specification

A valid completion needs either:
1. exact fixed-cx global success witnesses for the special-source forms actually
   allowed by expr_body_pre, including the address expression and read_result,
   OR
2. an entry lemma handling the global-failure branch without tail operand IH,
   while preserving arbitrary PG,G0,tn0, counted gas and all expression posts,
   OR
3. a checked concrete globally-failing special source plus a full admissible
   installed/frame witness demonstrating unavoidable unsafe compiler-first code.

For (3), full obligations include typing/arity and whole expr_body_pre, src
body_expr_ptr_ok even though its successful outcomes are absent, exact vacuous
tail guard, actual unit lowering and body_inv, FULL compile code in installed
func (not synthetic code), stmt_state_rel/alloca/fmp room, ghost_inv and PC,
no ctor/DALLOCA, old-variable reservations, gas_admissible and unavoidable failure
of gas_outcome_ptr despite source exception exits and exemptions. The known
OrderRun state-changing evaluation-order discrepancy does not supply these
clauses. Neither does E0131's residual prove falsehood.

Recommendation: authorize one concrete fixed-cx global-failure/success probe
before any further Slice entry proof; select its AST from actual special-source
and source typing definitions, not an assumed arbitrary unsafe tail. Do not rerun
E0131's primary tactic or silently replace the guard by EVERY body_expr_ptr_ok.
