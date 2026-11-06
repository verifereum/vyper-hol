# Widened call boundary audit (C1.31.1)

This is a source diagnostic, not a checked counterexample.

## Fixture and source

Let R = TupleT [BaseT (BytesT (Dynamic 32)); BaseT (UintT 256)]
and A = TupleT [BaseT (BytesT (Dynamic 64)); BaseT (UintT 256)].
The actual AST to investigate is `Call A (IntCall (NONE,"helper")) [] NONE`.
`scalar_probe_tops` declares helper returning R and returning
`scalar_probe_expr` (empty bytes, integer 42): ScalarProbe lines 10-25.
Its supported module is checked, but no actual caller frame is checked.
Interpreter lines 1609-1646 ignore call annotation A, look up helper,
evaluate zero arguments/defaults, push a function, evaluate its body,
pop/unlock, safe_cast to the DECLARED R, and return `Value crv`.
Success equation `eval_expr cx e es = (INL (Value (ArrayV (TupleV
[BytesV []; IntV 42]))),ee)` remains missing at an admissible concrete frame.

## Exact operand boundary ledger

From `body_expr_ptr_ok cx e`, for EVERY
`d PG tops ctx func cenv env ty es`, the antecedent is
`body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es`;
conclusion is BOTH `expr_sim_ptr d ctx PG func cenv cx ty e es`
and `expr_vv_sim_ptr d ctx PG func cenv cx ty e es` (bodyPtrPreds:20-26).
`ty` here is arbitrary and is not A or R by definition.

body_inv (bodySim:61-88) requires supported_program tops; an actual
runtime/deploy lowering unit whose context is ctx and policy target equals
cenv.ce_target; module-code equality; dynamic ABI compatibility;
exact build_func_ids, param_types, func_info, func_return_type, event_info,
struct_fields, hashmap_info and module_dynarray_capacity metadata;
acyclic struct metadata; constructor/deployment equality; alloca_locals;
distinct toplevel keys; module-var typing equality. The diagnostic has only
supported_program for scalar_probe_tops, NOT this lowering-unit witness.

expr_body_pre (exprSimHypsDefs:148-161) requires expr_sim_inv, well_typed_expr,
byte_widths_expr, alloc_limits_expr, call_evaluation_safe, no EVM-run,
EVERY internal call module NONE and supported module witness, ABI-decode
occurrence and dynamic ABI compatibility. expr_sim_inv (29 onward) includes
env/state/accounts/context/functions typing, ce_vars and ce_var_type matching
env locals, flag metadata, structural metadata, typed outcomes with IS_SOME,
storage/layout/oracle invariants and further state consistency clauses.
None of these full concrete antecedents has yet been instantiated here.

For EACH `sa sb vv s0 G0 tn0`, the vv antecedent (bodyPtrDefs:296-311) is:
`compile_expr cenv ty e sa = (vv,sb)`, `fn_has_code sa sb func`,
`fn_inst_ids_distinct func`, `local_ptrs_reserved cenv sa`,
`~ctx_has_dalloca ctx`, `~cenv.ce_is_ctor`, return-buffer and return-PC
variables not_fresh_at sa, `gas_admissible (eval_expr cx e) expr_vv_res_ok es`,
`stmt_state_rel ctx func cenv cx es s0`,
`ghost_inv d cenv cx es G0 tn0 s0`, `~s0.vs_halted`, and initial PC exactly
`sa.cs_current_bb, LENGTH sa.cs_current_insts`.
The value judgment (267-282) substitutes
`lower_value compile_expr cenv ty e sa = (op,sb)` and
`gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es`;
all other frame antecedents are the same.

## Exact outputs and crucial syntactic obstruction

Both deliver gas_outcome_ptr with D=cx_dead cx and tops=cx_tops cx.
The vv normal Q (314-324) existentially binds tv, res=INL tv,
`vv_post ctx func cenv cx e es sa sb s0 ee tv vv t`, endpoint PC sb,
ghost_inv at ee, `ptr_vv_ok cx (expr_type e) tv vv ee G tn t`, buffer
coverage for nonword StackValue or memory LocatedValue, and
`ghost_kept cenv es sa G0 tn0 s0 G tn`.
The value Q (285-292) similarly binds v, res=INL v, expr_post,
endpoint PC, ghost_inv, ptr_val_ok at expr_type e, nonword ptr_buf_ok,
and ghost_kept. Both exit posts are EXACTLY `expr_exit res r`, without
additional ghost constraint; expr_exit (exprSimDefs:7-12) rejects INL.
Gas outcome also permits gas_exempt_cert, so Q cannot be assumed directly
from gas admissibility or a standalone successful run.

expr_post (loweringPosts:251-266) uses expr_type e = A for expr_val_rel
and expr_val_at, plus state relation, old-variable/allocation/memory and
locals preservation. vv_post (377-392) uses A for vv_holds and vv_at,
with the same preservation fields.
**vv_holds (332-349) for `LocatedValue t' p` requires `t' = t`.**
Thus if compile_expr returns `LocatedValue R p`, its vv_post for annotation
A is FALSE already by R <> A, independently of memory, provenance or
callee execution. This is stronger and cheaper than the offset-64 mismatch.
The compiler (exprLowering:2627-2667) explicitly returns LocatedValue call_ty
(base_ptr rbuf), call_ty=cenv.ce_func_return_type name. Under body_inv this
is the declared R. The zero-args buffer path emits ALLOCA then INVOKE []
outputs (CallPrefix positions, checked).

ptr_buf_ok (bodyPtrDefs:223-231) uses `lowered_value_type cenv e`, which
is the declared R for an IntCall (exprLowering:172-174), NOT annotation A.
It asserts lower coverage only, not exact extent. Hence interpreting the
physical return at R cannot be obtained merely by changing the type in
expr_post; but the vv branch's type equality could exclude this successful
widened LocatedValue call, provided all outcome alternatives are handled.

## Execution after the checked prefix

CallPrefix semantic_prefix exposes actual successful ALLOCA, safe step,
count and ghost update, plus original residual counted path. It does not
force the residual path to stop immediately after INVOKE.
For this empty call the only generated instruction after allocation is
INVOKE with [] outputs. step_inst (venomExecSemantics:1704-1730) decodes,
looks up callee, evaluates arguments, sets up frame, runs callee, and on
IntRet binds outputs after adopt_return_fmp/merge_callee_state.
merge_callee_state (1468-1482) retains caller variables and allocas and
copies memory and external side effects. With no outputs, bind_outputs
cannot overwrite the return-buffer variable. This is a definitional fact,
not yet an exported checked whole-call lemma here.
ghost_step (ptrSafeRun:58-81) successful setup uses
`DRESTRICT G (COMPL (set inst.inst_outputs))`, so for [] outputs caller
provenance survives. Returned taint takes callee ghost taint, then restores
caller t_var restricted by outputs. No non-invoke ghost lemma applies.
Further arbitrary suffixes are NOT excluded by this observation.

## Status of bridges / recommendation

Checked: module supportedness, R/A supported return types; standalone
scalar_probe_return_run (offset64=42, offset96=0, R interpretation true,
A interpretation false); actual empty-call compiler positions, first edge
cut/fetch and semantic allocation prefix.
Directly definitional: annotation ignored by source internal-call clause;
call vv carries declared type; LocatedValue vv_holds forces exact type;
INVOKE [] preserves caller G/variables in its immediate successful step.
Missing: concrete actual AST typing/body pre; lowered runtime unit and full
body_inv; concrete stmt_state_rel/ghost/reservation/freshness/distinct code
frame; successful source run and gas conditions; exclusion of exemption
and exit alternatives for the resulting outcome. Standalone copied return
run proves none of these bridges.

Recommend FIRST a small checked boundary theorem, NOT memory transport:
`vv_post ctx func ce cx e es sa sb s0 ee tv (LocatedValue R p) t ==>
 R = expr_type e`.
Search/generalize an existing vv_holds inversion before adding it. Then
prove the actual empty widened compile output has tag R. These facts show
normal vv post impossible for A<>R without reconstructing callee memory.
The single next semantic obligation is to force the ORIGINAL vv operand
outcome to its normal Q from a fully admissible successful source frame,
excluding gas_exempt_cert and expr_exit. This still needs a real frame (or
an applicable existing nonexemption theorem); no universal-frame vacuity
or frozen-target falsehood follows yet. Do not invest in full machine run
or generic physical-layout conversion before that boundary is reviewed.
