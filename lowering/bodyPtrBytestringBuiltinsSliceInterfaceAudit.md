# Compiler-first Slice pointer interface audit

Scope: C1.slice.interfaceaudit. This is a premise/dependency diagnostic, not a
proof, counterexample, new semantic assumption, or replacement for the frozen
bytestring_builtin_expr_ptr_ok statement.

## Available premise ledger

The frozen premise gives body_exprs_ptr_ok cx [src; start; len] when arity is
valid. bodyPtrPredsScript.sml:61-67 supplies the head judgment, but grants the
start judgment only under

    ?s tv t s1 v t1. eval_expr cx src s = (INL tv,t) /\
                     read_result cx tv s1 = (INL v,t1).

The states s1 and t are independent. SliceGuardFixture already proves this
existential false for slice_guard_source, and SliceGuardFrame proves the list
judgment for arbitrary tails. Neither fact supplies a start judgment.

Source frame: body_inv (bodySimScript.sml:61-88) supplies a supported, actually
lowered unit/context; source module agreement; compiler metadata agreement;
constructor/runtime agreement and local-allocation mode. It does not identify
an arbitrary queried expression as installed code and does not assert dynamic
access_ok, taint_ok or frame_reachable for arbitrary G0/tn0.

Whole expression precondition (exprSimHypsDefs.expr_body_pre_def):
expr_sim_inv, well_typed_expr, byte widths, allocation limits, call evaluation
safety, no EVM-run, internal-call module/support conditions, ABI-target
occurrence and dynamic ABI consistency. For typed word start/len,
exprSimSource.expr_body_pre_builtin_typed_arg transfers these facts at any
state satisfying expr_sim_inv. The ordinary untyped argument lemma excludes
Slice extcode sources; it cannot yield the address judgment through the wrapper.
Typed preconditions are NOT pointer simulations.

Runtime ledger (bodyPtrDefsScript.sml:267-326): the value judgment quantifies
sa, sb, op, s0, G0, tn0. Its inputs are a lower_value equation, fn_has_code,
fn_inst_ids_distinct, local_ptrs_reserved, no context DALLOCA, nonconstructor
cenv, old return-buffer/PC variables, gas_admissible for the queried source
computation, stmt_state_rel, ghost_inv, nonhaltedness and initial bb/index.
The vv judgment has the analogous compile_expr equation and unforced evaluator.
The result must be gas_outcome_ptr, not merely a safe edge: normal results need
expr_post/vv_post, endpoint PC, ghost_inv, ptr_val_ok/ptr_vv_ok, buffer coverage
and ghost_kept; exceptional results need expr_exit. Ghosts/taint are arbitrary
subject to ghost_inv, not entry FEMPTY/entry_taint.

stmt_state_rel (exprLoweringPropsScript.sml:412-422) gives state_rel,
alloca_inv, alloca_room, fmp_room, immutable separation/base and consistency of
existing allocation site sizes. ghost_inv covers live local pointers/values,
return buffer/PC and dead-byte storage taint (bodyPtrDefs:80-93). Neither
contains a safe counted execution of an arbitrary compiler-first operand.

For special extcode Slice, SliceDispatch.slice_extcode_compile_cut says start,
then len, then allocation, then extcode_addr_expr, then copy. Source evaluation
is source-first. Whole-expression gas admissibility therefore cannot silently
be specialized to start evaluation if the source always fails first.

## Candidate interfaces and dependency rejection

* exprSimPtr.leaf_expr_sim_ptr requires leaf syntax plus expr_sim_pre and proves
  both pointer judgments. It covers Name, TopLevelName, FlagMember and Literal,
  not arbitrary typed word expressions. A typed word may contain a call, Pop,
  subscript, arithmetic or a nested builtin.
* exprPtrUnwrap.expr_sim_ptr_of_vv requires expr_body_pre AND an existing
  expr_vv_sim_ptr; expr_vv_sim_ptr_stack requires an existing value judgment.
  They change representation, not establish safety without an operand judgment.
* Task operand combinators (Unary, Eval, ConcatHead) explicitly require
  expr_sim_ptr for the operand. Existing SliceTraceProbe's successful-source
  lemma also explicitly requires the six-witness source success premise.
* exprSimHyps.expr_sim_case_apply supplies erased expr_sim, not counted pointer
  safety. No implication from that erased judgment to expr_sim_ptr was found.
* bodySimPtrMain.body_sim_ptr_mutual includes !cx e. body_expr_ptr_ok cx e,
  but its evaluate_ind proof uses body_builtin_case_ptr (line 93), whose
  bodyPtrExprCases theory imports bodyPtrBytestringBuiltins (line 21).
  Using this theorem here would be circular. It is not an independent boundary.
* lower_vyper_runtime_unit_fn_ptr_ok and ptr_ok_check_sound establish static
  fn_ptr_ok. ptrSafeRun.ptr_safe_ptr_discipline additionally ASSUMES safe blocks
  at every entry fuel, with FEMPTY and entry_taint. It cannot manufacture that
  premise or apply directly at arbitrary quantified G0/tn0 expression entries.
  ptr_discipline's access_ok consequence also needs actual frame_reachable.

Searches: search_theorems for expr/ptr_safe, ptr/well_typed_expr,
ptr/fn_ptr_ok, expr_sim_ptr/expr_body_pre, leaf_expr_sim_ptr, expr_sim_case;
read actual bodySimPtrMain, bodyPtrExprCases, bodyPtrDefs, exprPtrUnwrap,
bodyPtrPreds, stmt_state_rel and body_inv. These found no noncircular generic
compiler-first pointer judgment applicable to arbitrary tails. This is a bounded
repository audit, not a metatheorem that no alternative proof exists.

## Countermodel assessment and selected route

No concrete unsafe instruction was validated by this audit. A local word Name
load is not a countermodel: ghost_inv covers the local's pointer and robust
value representation. A literal has an independent leaf proof. A memory access
inside an arbitrary complex tail still requires tracing its producer and its
access/taint obligations; missing an IH alone proves no failure. The concrete
Div0 address fixture now has slice_guard_counted_abort under the explicit
runtime premises, so its literal-tail evaluation-order mismatch is not an
unsafe instruction. Do not install a speculative frame or enumerate safe
literal variants on this evidence.

Selected route for strategist review: a separate structural compiler-safety
induction (over compiler-first operands, not evaluator-success-guarded lists),
or an applicable noncircular boundary from such an induction, is still missing.
Its input must be the actual source/body/runtime ledger above; its output must
supply counted pointer execution with appropriate ghost transport and outcome
handling. In particular a full expr_sim_ptr theorem for arbitrary typed start
would be stronger than what the current conditional induction hypothesis gives,
and whole Slice gas admissibility need not grant start gas admissibility in the
source-failure branch. No such new theorem is assumed here, and implementing it
would be a broader architectural change, not a local proof tactic repair.

If selecting a counterexample route instead, first identify and check a typed
tail's specific failing ptr_inst_ok memory/provenance/taint condition while
accounting for ghost_inv. Only then construct body_inv/expr_body_pre,
installation, runtime relation, gas and inevitable failure of the full counted
outcome (including source exception exits). This audit has not completed that
selection. Frozen target truth remains unresolved.
