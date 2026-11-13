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

## Outcome forcing audit (C1.31.2.3)

Checked tag interfaces are now available: vv_holds_located_type in
bodyPtrIfExpLocatedTag; existing vv_post_located_type in UnwrapContract;
ifexp_buffer_call_post_incompatible in CallTag. These do not force Q.

The exact compiler bridge is compile_expr's Call case in
exprLoweringScript.sml:3010-3011:
`Call _ target args default_ret =>
 compile_call compile_expr cenv ret_ty ty target args default_ret st`.
It is exposed through compile_expr_component_eq, as in ScalarProbe:57;
no special AST embedding theorem has been proved for this audit.

Certificate exclusion has an existing checked interface:
gasExemptCert:241-249, gas_exempt_cert_execution:
`gas_exempt_cert memory tops (ctx,func) source (es,s0)
 marks (err,ee) (leaf,finish) ==>`
`(!tail. source (es with gas_obs :=
 gas_explicit marks s0.vs_gas_readings ++ tail) =
 (INR (Error err), ee with gas_obs := tail)) /\
 gas_focus_path memory (ctx,func) s0 (LENGTH marks) (leaf,finish) /\
 unspecified_behaviour_exempt tops err`.
For the original vv outcome the certificate source is
`ignore_bind (eval_expr cx e) (return ())`, NOT eval_expr itself.
Thus a proof of successful eval_expr for EVERY gas observation list,
plus bind/ignore_bind computation, contradicts the certificate at tail=[].
Successful eval_expr at only the original es.gas_obs is insufficient.
No assumption ~source_exempt for call_external is available here;
top-level e2e source_exempt checks do not discharge this local certificate.

For the summary alternative, gas_summary_ptr_at_def gives an existential
res ee G tn r and
`!tail. eval_expr cx e
 (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
 (res, ee with gas_obs := tail)`.
A pointwise success theorem for all lists `gs`:
`!gs. ?tv ee. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee)`
is enough to force res=INL tv by specializing at tail=[] and comparing
pairs. No equality of successful values across gs is needed for the tag
contradiction. expr_exit (exprSimDefs:7-12) rejects all INL results, so
summary's exit branch is impossible. The remaining Q contains vv_post,
contradicting CallTag. This uses the exact source equation and does not
require an all-path machine proof or a successful invocation witness.

The SAME all-gs success statement would eliminate the certificate, using
gas_exempt_cert_execution on ignore_bind as above. The source interpreter
for scalar_probe_tops reads no gas in helper, but a checked all-gs call
success theorem is still missing, with actual cx/es and type checks.
This is an execution theorem for the source, not something supplied by
gas_admissible: admissibility permits exception results.

Frame antecedents remain the entire ledger above, independently of source
success. To refute `body_expr_ptr_ok cx e` one needs ONE instantiation of
body_inv/expr_body_pre AND the vv simulation frame including compilation,
code/distinct IDs/reservation, no dalloca/ctor, return variables freshness,
gas admissibility, state relation and ghost invariant. We have not shown
these coexist for the concrete misannotated call. In particular functions
well-typed and expression typing are substantive; neither supported_program
nor scalar_probe_return_run alone witnesses them.

Recommendation: next semantic statement should establish the all-gs source
success theorem for the actual scalar helper call at a concrete source
context/state that is compatible with expr_body_pre. Search an existing
internal-call evaluation computation before introducing any new fixture.
Then evaluate whether actual lower_vyper_runtime_unit and an empty-local
stmt_state_rel/ghost frame can be witnessed. A normal-forcing wrapper with
hypotheses merely saying no certificate/no exit would add no evidence.
If the source frame cannot be admitted, classify why rather than silently
assuming it. Even successful exclusion of this operand premise only removes
one widened-arm candidate; it cannot falsify the frozen IfExp implication,
which assumes that premise. A proof of the general target would still need
a principled use of the original operand judgments across all arm forms.

## Normal-continuation alignment (C1.31.4)

`bodyPtrIfExpCallAlignment.ifexp_buffer_call_normal_alignment` is checked
for the actual Call AST, arbitrary arguments and frames. The compiler's
buffer descriptor plus the existing `vv_post_located_type` projection
imply `lowered_value_type ce arm = expr_type arm` within that normal post.
No invocation execution, nonexemption assumption or forced normal outcome
is used. Search found no existing theorem with this actual AST boundary.

The original `expr_vv_sim_ptr` normal continuation retains `vv_post`
(bodyPtrDefs:315); its compiler equation is part of the same judgment.
Thus a compositional IfExp proof can retain that post and apply alignment
before unwrapping the selected buffer-call arm. It must not first erase
the vv evidence to a plain expr_post. The existing no-copy consumer
`ifexp_read_no_copy_ptr_mem_ok` requires equality of memory byte counts
between lowered arm type and result annotation (NoCopyConsumer:12-13).
The new equality bridges lowered arm type to arm annotation only. The
remaining bridge is arm annotation to IfExp result annotation, through
actual typing/layout hypotheses: this theorem alone does not supply it.
For copying, it similarly identifies the source interpretation type with
its actual buffer descriptor; counted pointer-safe copy execution remains
an independent obligation. Exempt/exit outcomes remain separate branches.
Zero-buffer calls, stack-return calls, other expressions, and general
IfExp composition are not discharged by this boundary.

## Typed buffer-call consumer (C1.33)

Checked `bodyPtrIfExpCallConsumer` combines the retained original vv post
with IfExp typing, deriving lowered arm type = result annotation. Its
non-word consumer transports both ptr_mem_ok and ptr_buf_ok at an arbitrary
later state u, independent of the original vv witness endpoint t. A single
general `ptr_buf_ok_bytes_cong` captures capacity extensionality; repository
search found no equivalent exported helper. No new definition was needed.

For this normal buffer internal-call boundary the suspected physical-layout
obstruction no longer survives: the original vv post forces declared call
return type to equal arm annotation, and typing equates arm/result
annotations. This is not a realizability proof or a generic widening rule.
The next semantic boundary is counted pointer-safe materialization retaining
this evidence and delivering ptr_buf_ok at u, followed by control/branch
composition. Other lowered-type exceptions (bytelike literals, AbiEncode),
stack/zero-buffer calls, and exceptional/exempt outcomes remain unresolved.
