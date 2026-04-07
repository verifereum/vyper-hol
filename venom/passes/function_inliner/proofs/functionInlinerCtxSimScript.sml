(*
 * Cross-Context Simulation for inline_candidate
 *
 * APPROACH (two-step composition):
 *   Step 1 (ctx_replace): run_function fuel ctx g s ~ run_function F1 ctx' g s
 *     Running the SAME function g in ctx vs ctx'. Non-INVOKE instructions are
 *     ctx-independent. INVOKE dispatches differ but IH + merge identity give
 *     equal post-INVOKE states.
 *
 *   Step 2 (per-fn inlining): run_function F1 ctx' g s ~ run_function F2 ctx' g' s
 *     Reuse inline_at_sites_fn_correct with ctx' (callee unchanged in ctx').
 *
 *   Compose via lift_result transitivity.
 *)

Theory functionInlinerCtxSim
Ancestors
  functionInlinerCallSim functionInlinerSim functionInlinerDefs
  stateEquiv stateEquivProps
  venomExecSemantics venomInst venomWf

open stringTheory pairTheory listTheory
open functionInlinerDefsTheory functionInlinerSimTheory
     functionInlinerCallSimTheory functionInlinerCallSimHelpersTheory
     functionInlinerCalleeSimTheory functionInlinerRenumberTheory
     functionInlinerFreshTheory
     venomExecSemanticsTheory venomExecPropsTheory
     venomInstTheory venomWfTheory
     stateEquivTheory stateEquivPropsTheory cfgTransformTheory

(* ================================================================
   FOUNDATION LEMMAS
   ================================================================ *)

(* Project EVERY over lookup_function: if P holds for all functions
   in a list and we look up a specific one, P holds for it. *)
Triviality every_lookup:
  !P name fns f.
    EVERY P fns /\ lookup_function name fns = SOME f ==> P f
Proof
  rpt strip_tac >>
  imp_res_tac lookup_function_MEM >>
  fs[EVERY_MEM]
QED

Triviality shared_globals_np_refl[simp]:
  shared_globals_np s s
Proof
  rw[shared_globals_np_def]
QED

(* merge_callee_state produces EQUAL results when callee states
   agree on shared_globals_np fields. This is because merge_callee_state
   copies exactly the fields that shared_globals_np equates. *)
Theorem merge_callee_state_shared_globals_np:
  !s c1 c2.
    shared_globals_np c1 c2 ==>
    merge_callee_state s c1 = merge_callee_state s c2
Proof
  rw[shared_globals_np_def, merge_callee_state_def,
     venomStateTheory.venom_state_component_equality]
QED

(* setup_callee depends only on entry label, not on full function *)
Theorem setup_callee_entry_eq:
  !h h' args s.
    ~NULL h.fn_blocks /\ ~NULL h'.fn_blocks /\
    (HD h.fn_blocks).bb_label = (HD h'.fn_blocks).bb_label ==>
    setup_callee h args s = setup_callee h' args s
Proof
  rw[setup_callee_def]
QED

(* lift_result transitivity *)
Theorem lift_result_trans:
  !R_ok R_term r1 r2 r3.
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) ==>
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) ==>
    lift_result R_ok R_term r1 r2 ==>
    lift_result R_ok R_term r2 r3 ==>
    lift_result R_ok R_term r1 r3
Proof
  rpt gen_tac >> ntac 2 strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  simp[lift_result_def] >>
  metis_tac[]
QED

(* Compose lift_result (=) with lift_result R *)
Theorem lift_result_eq_then:
  !R_ok R_term r1 r2 r3.
    lift_result (=) (=) r1 r2 ==>
    lift_result R_ok R_term r2 r3 ==>
    lift_result R_ok R_term r1 r3
Proof
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  simp[lift_result_def]
QED

(* lift_result reflexivity for equality *)
Theorem lift_result_eq_refl:
  !r. lift_result (=) (=) r r
Proof
  Cases >> simp[lift_result_def]
QED

(* lift_result reflexivity with shared_globals_np *)
Triviality lift_result_eq_sgnp_refl:
  !r. lift_result (=) shared_globals_np r r
Proof
  Cases >> REWRITE_TAC[lift_result_def, shared_globals_np_refl]
QED

(* Weaken R_ok: (=) implies any reflexive relation *)
Triviality lift_result_weaken_ok:
  !R_ok R_term r1 r2.
    (!s. R_ok s s) ==>
    lift_result (=) R_term r1 r2 ==>
    lift_result R_ok R_term r1 r2
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >>
  simp[lift_result_def] >> metis_tac[]
QED

(* For non-OK results, R_ok is irrelevant — only R_term matters *)
Triviality lift_result_change_ok:
  !R1 R2 R_term r1 r2.
    (!v. r1 <> OK v) ==>
    lift_result R1 R_term r1 r2 ==>
    lift_result R2 R_term r1 r2
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >>
  gvs[lift_result_def]
QED

(* ================================================================
   STEP 1: CTX-REPLACEMENT (same function, different context)

   When running the SAME function g in ctx vs ctx', only INVOKE
   dispatch differs. For non-INVOKE, step_inst_base is ctx/fuel
   independent. For INVOKE with IntRet callee, merge identity gives
   equal post-INVOKE states. For terminal callees, shared_globals_np
   propagates.
   ================================================================ *)

Theorem step_inst_cross_ctx:
  !fuel fuel' ctx ctx' inst s.
    inst.inst_opcode <> INVOKE ==>
    step_inst fuel ctx inst s = step_inst fuel' ctx' inst s
Proof
  rw[step_inst_non_invoke]
QED

(* step_inst with INVOKE: when both callees return IntRet with
   shared_globals_np callee states, merge identity gives equal step results *)
Theorem step_inst_invoke_cross_ctx:
  !fuel fuel_h ctx ctx' inst s h h' callee_s vals c1 c2 h_name arg_ops args.
    inst.inst_opcode = INVOKE /\
    decode_invoke inst = SOME (h_name, arg_ops) /\
    lookup_function h_name ctx.ctx_functions = SOME h /\
    lookup_function h_name ctx'.ctx_functions = SOME h' /\
    eval_operands arg_ops s = SOME args /\
    setup_callee h args s = SOME callee_s /\
    setup_callee h' args s = SOME callee_s /\
    run_function fuel ctx h callee_s = IntRet vals c1 /\
    run_function fuel_h ctx' h' callee_s = IntRet vals c2 /\
    shared_globals_np c1 c2 ==>
    step_inst fuel ctx inst s = step_inst fuel_h ctx' inst s
Proof
  rpt strip_tac >>
  `merge_callee_state s c1 = merge_callee_state s c2`
    by metis_tac[merge_callee_state_shared_globals_np] >>
  ONCE_REWRITE_TAC[step_inst_def] >> gvs[]
QED

(* step_inst for INVOKE depends on run_function only through its result.
   So if run_function gives the same result at two fuel values,
   step_inst gives the same result too. *)
Triviality step_inst_invoke_run_function_eq:
  !fuel1 fuel2 ctx inst s.
    inst.inst_opcode = INVOKE ==>
    (!callee_name arg_ops callee_fn args callee_s.
       decode_invoke inst = SOME (callee_name, arg_ops) /\
       lookup_function callee_name ctx.ctx_functions = SOME callee_fn /\
       eval_operands arg_ops s = SOME args /\
       setup_callee callee_fn args s = SOME callee_s ==>
       run_function fuel1 ctx callee_fn callee_s =
       run_function fuel2 ctx callee_fn callee_s) ==>
    step_inst fuel1 ctx inst s = step_inst fuel2 ctx inst s
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[step_inst_def] >> ASM_REWRITE_TAC[] >>
  Cases_on `decode_invoke inst` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 ctx.ctx_functions` >> simp[] >>
  Cases_on `eval_operands x1 s` >> simp[] >>
  Cases_on `setup_callee x x' s` >> simp[]
QED

(* step_inst fuel monotonicity: if step_inst doesn't return Error,
   adding fuel gives the same result.
   Non-INVOKE: fuel-independent. INVOKE: run_function_fuel_mono. *)
Triviality step_inst_fuel_mono:
  !fuel ctx inst s.
    (!e. step_inst fuel ctx inst s <> Error e) ==>
    !k. step_inst (fuel + k) ctx inst s = step_inst fuel ctx inst s
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    mp_tac (Q.SPECL [`fuel + k`, `fuel`, `ctx`, `inst`, `s`]
      step_inst_invoke_run_function_eq) >>
    ASM_REWRITE_TAC[] >>
    DISCH_THEN irule >>
    rpt strip_tac >>
    `terminates (run_function fuel ctx callee_fn callee_s)` by (
      CCONTR_TAC >> gvs[terminates_def] >>
      Cases_on `run_function fuel ctx callee_fn callee_s` >> gvs[] >>
      first_x_assum (qspec_then `s'` mp_tac) >>
      simp[step_inst_def] >>
      Cases_on `bind_outputs inst.inst_outputs l
        (merge_callee_state s callee_s)` >> gvs[step_inst_def]) >>
    metis_tac[run_function_fuel_mono])
  >>
  simp[step_inst_non_invoke]
QED

(* General cross-ctx step_inst for INVOKE: produces lift_result on
   step_inst results when callee results are related.
   For IntRet: merge identity gives equal OK states.
   For Halt/Abort: shared_globals_np propagates.
   For Error/OK-callee: both sides Error. *)
Theorem step_inst_invoke_cross_ctx_general:
  !fuel fuel_h ctx ctx' inst s h h' callee_s h_name arg_ops args.
    inst.inst_opcode = INVOKE /\
    decode_invoke inst = SOME (h_name, arg_ops) /\
    lookup_function h_name ctx.ctx_functions = SOME h /\
    lookup_function h_name ctx'.ctx_functions = SOME h' /\
    eval_operands arg_ops s = SOME args /\
    setup_callee h args s = SOME callee_s /\
    setup_callee h' args s = SOME callee_s /\
    lift_result (=) shared_globals_np
      (run_function fuel ctx h callee_s)
      (run_function fuel_h ctx' h' callee_s) ==>
    lift_result (=) shared_globals_np
      (step_inst fuel ctx inst s)
      (step_inst fuel_h ctx' inst s)
Proof
  rpt strip_tac >>
  Cases_on `run_function fuel ctx h callee_s` >>
  Cases_on `run_function fuel_h ctx' h' callee_s` >>
  gvs[lift_result_def] >>
  ONCE_REWRITE_TAC[step_inst_def] >> gvs[lift_result_def] >>
  imp_res_tac merge_callee_state_shared_globals_np >>
  (* IntRet case: merge identity makes bind_outputs identical *)
  first_x_assum (qspec_then `s` mp_tac) >> DISCH_THEN SUBST_ALL_TAC >>
  Cases_on `bind_outputs inst.inst_outputs l (merge_callee_state s v')` >>
  simp[lift_result_def]
QED

(* run_block cross-ctx: same block, different contexts.
   The callee_hyp provides cross-ctx simulation for all INVOKE targets.
   Returns lift_result (=) shared_globals_np, and for OK states they
   are literally equal (not just related). *)
(* Helper: step_inst fuel-monotone for non-Error *)
Triviality step_inst_fuel_mono_ge:
  !f g ctx inst s.
    f <= g /\ (!e. step_inst f ctx inst s <> Error e) ==>
    step_inst g ctx inst s = step_inst f ctx inst s
Proof
  rpt strip_tac >>
  `g = f + (g - f)` by simp[] >>
  pop_assum SUBST1_TAC >>
  irule step_inst_fuel_mono >> ASM_REWRITE_TAC[]
QED

(* run_block fuel monotonicity: f <= g ==> non-Error(rb f) ==> rb g = rb f *)
Triviality run_block_fuel_mono_ge:
  !f g ctx bb s. f <= g /\
    (!e. run_block f ctx bb s <> Error e) ==>
    run_block g ctx bb s = run_block f ctx bb s
Proof
  rpt strip_tac >>
  `g = f + (g - f)` by simp[] >>
  pop_assum SUBST1_TAC >>
  irule run_block_fuel_mono >> ASM_REWRITE_TAC[]
QED

(* run_function fuel monotonicity: f <= g ==> terminates(rf f) ==> rf g = rf f *)
Triviality run_function_fuel_mono_ge:
  !f g ctx fn s. f <= g /\
    terminates (run_function f ctx fn s) ==>
    run_function g ctx fn s = run_function f ctx fn s
Proof
  rpt strip_tac >>
  `g = f + (g - f)` by simp[] >>
  pop_assum SUBST1_TAC >>
  irule run_function_fuel_mono >> ASM_REWRITE_TAC[]
QED

(*
 * run_block_cross_ctx: same block, different contexts.
 * Key insight: choose fuel' = fuel_cont (from IH), NOT MAX(fuel_h, fuel_cont).
 * At fuel_cont, the INVOKE callee either:
 *   (a) returns IntRet (same as fuel_h, by fuel_mono) → step_inst OK, IH works
 *   (b) returns Error → step_inst Error → both sides Error
 * This avoids the unsound MAX approach where more fuel could turn Error into success.
 *)

(* run_function never returns OK — fundamental property.
   Local copy since IntretChainScript marks it [local]. *)
Triviality run_function_not_ok[local]:
  !fuel ctx fn s v. run_function fuel ctx fn s <> OK v
Proof
  Induct >> rpt gen_tac >>
  ONCE_REWRITE_TAC[run_function_def] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  Cases_on `run_block fuel ctx x s` >> simp[] >>
  Cases_on `v'.vs_halted` >> simp[]
QED

(* If step_inst for INVOKE returns OK, callee returned IntRet *)
Triviality step_inst_invoke_ok_callee_intret:
  !fuel ctx inst s v h_name arg_ops h args callee_s.
    step_inst fuel ctx inst s = OK v /\
    inst.inst_opcode = INVOKE /\
    decode_invoke inst = SOME (h_name, arg_ops) /\
    lookup_function h_name ctx.ctx_functions = SOME h /\
    eval_operands arg_ops s = SOME args /\
    setup_callee h args s = SOME callee_s ==>
    ?vals c. run_function fuel ctx h callee_s = IntRet vals c
Proof
  rpt strip_tac >>
  Cases_on `run_function fuel ctx h callee_s` >>
  gvs[step_inst_def, run_function_not_ok]
QED

(* Helper: if run_function terminates at fuel_h (IntRet), and also terminates
   at fuel_cont, then it gives the same result at both fuels *)
Triviality rf_terminates_same_result:
  !f1 f2 ctx fn s.
    terminates (run_function f1 ctx fn s) /\
    terminates (run_function f2 ctx fn s) ==>
    run_function f1 ctx fn s = run_function f2 ctx fn s
Proof
  rpt strip_tac >>
  Cases_on `f1 <= f2`
  >- (`run_function f2 ctx fn s = run_function f1 ctx fn s`
        suffices_by simp[] >>
      irule run_function_fuel_mono_ge >> ASM_REWRITE_TAC[])
  >>
  `f2 <= f1` by simp[] >>
  irule run_function_fuel_mono_ge >> ASM_REWRITE_TAC[]
QED

(* step_inst at fuel=0 always returns Error for INVOKE *)
Triviality step_inst_invoke_zero_error:
  !ctx inst s. inst.inst_opcode = INVOKE ==>
    ?e. step_inst 0 ctx inst s = Error e
Proof
  rpt strip_tac >> simp[step_inst_def] >>
  Cases_on `decode_invoke inst` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 ctx.ctx_functions` >> simp[] >>
  Cases_on `eval_operands x1 s` >> simp[] >>
  Cases_on `setup_callee x x' s` >> simp[] >>
  simp[run_function_def]
QED

(* Helper: for non-OK step_inst with INVOKE, find fuel' for the right side.
   Two cases:
   - Error: choose fuel'=0 (INVOKE always errors at fuel 0), lift_result T
   - Non-Error non-OK (Halt/Abort/IntRet): use cross_ctx_general *)
Triviality step_inst_invoke_non_ok_cross_ctx:
  !fuel ctx ctx' inst s r.
    step_inst fuel ctx inst s = r /\
    (!v. r <> OK v) /\
    inst.inst_opcode = INVOKE /\
    (!h_name h callee_s.
      lookup_function h_name ctx.ctx_functions = SOME h ==>
      ?h'.
        lookup_function h_name ctx'.ctx_functions = SOME h' /\
        ~NULL h.fn_blocks /\ ~NULL h'.fn_blocks /\
        (HD h.fn_blocks).bb_label = (HD h'.fn_blocks).bb_label /\
        ?fuel_h.
          lift_result (=) shared_globals_np
            (run_function fuel ctx h callee_s)
            (run_function fuel_h ctx' h' callee_s)) ==>
    ?fuel'.
      lift_result (=) shared_globals_np r (step_inst fuel' ctx' inst s)
Proof
  rpt strip_tac >>
  (* Case split on decode/lookup/eval/setup chain on the LEFT.
     NONE cases: left = Error, choose fuel'=0, right = Error. T.
     All SOME: use step_inst_invoke_cross_ctx_general. *)
  (* First establish: if decode/lookup/eval/setup fail on left, r = Error *)
  Cases_on `decode_invoke inst`
  >- (
    (* decode = NONE: left step_inst = Error *)
    qexists_tac `0` >>
    `?e. step_inst 0 ctx' inst s = Error e` by
      metis_tac[step_inst_invoke_zero_error] >>
    `?e'. r = Error e'` by (
      qpat_x_assum `step_inst _ _ _ _ = r` (SUBST_ALL_TAC o SYM) >>
      simp[step_inst_def]) >>
    ASM_REWRITE_TAC[lift_result_def])
  >>
  PairCases_on `x` >> rename [`SOME (h_name, arg_ops)`] >>
  Cases_on `lookup_function h_name ctx.ctx_functions`
  >- (
    (* lookup = NONE on left: left = Error *)
    qexists_tac `0` >>
    `?e. step_inst 0 ctx' inst s = Error e` by
      metis_tac[step_inst_invoke_zero_error] >>
    `?e'. r = Error e'` by (
      qpat_x_assum `step_inst _ _ _ _ = r` (SUBST_ALL_TAC o SYM) >>
      simp[step_inst_def]) >>
    ASM_REWRITE_TAC[lift_result_def])
  >>
  rename [`lookup_function _ ctx.ctx_functions = SOME h`] >>
  Cases_on `eval_operands arg_ops s`
  >- (
    (* eval = NONE: left = Error *)
    qexists_tac `0` >>
    `?e. step_inst 0 ctx' inst s = Error e` by
      metis_tac[step_inst_invoke_zero_error] >>
    `?e'. r = Error e'` by (
      qpat_x_assum `step_inst _ _ _ _ = r` (SUBST_ALL_TAC o SYM) >>
      simp[step_inst_def]) >>
    ASM_REWRITE_TAC[lift_result_def])
  >>
  rename [`eval_operands _ _ = SOME args`] >>
  Cases_on `setup_callee h args s`
  >- (
    (* setup = NONE: left = Error *)
    qexists_tac `0` >>
    `?e. step_inst 0 ctx' inst s = Error e` by
      metis_tac[step_inst_invoke_zero_error] >>
    `?e'. r = Error e'` by (
      qpat_x_assum `step_inst _ _ _ _ = r` (SUBST_ALL_TAC o SYM) >>
      simp[step_inst_def]) >>
    ASM_REWRITE_TAC[lift_result_def])
  >>
  rename [`setup_callee h _ _ = SOME callee_s`] >>
  (* NOW specialize callee_hyp with h_name, h, callee_s *)
  first_x_assum (qspecl_then [`h_name`, `h`, `callee_s`] mp_tac) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >> strip_tac >>
  (* setup_callee h' args s = SOME callee_s by entry label equality *)
  `setup_callee h' args s = SOME callee_s` by
    metis_tac[setup_callee_entry_eq] >>
  (* All SOME: use step_inst_invoke_cross_ctx_general *)
  qexists_tac `fuel_h` >>
  mp_tac (Q.SPECL [`fuel`, `fuel_h`, `ctx`, `ctx'`, `inst`, `s`,
    `h`, `h'`, `callee_s`, `h_name`, `arg_ops`, `args`]
    step_inst_invoke_cross_ctx_general) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >>
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = r` (SUBST_ALL_TAC o SYM) >>
  ASM_REWRITE_TAC[]
QED

(* Bridge: convert lift_result on step_inst to lift_result on run_block
   for non-OK step_inst results. The case expression just passes through. *)
Triviality lift_result_step_to_block:
  !R_ok R_term r fuel' ctx' inst s bb.
    lift_result R_ok R_term r (step_inst fuel' ctx' inst s) /\
    (!v. r <> OK v) ==>
    lift_result R_ok R_term r
      (case step_inst fuel' ctx' inst s of
         OK s'' =>
           if is_terminator inst.inst_opcode then
             if s''.vs_halted then Halt s'' else OK s''
           else
             run_block fuel' ctx' bb
               (s'' with vs_inst_idx := SUC s.vs_inst_idx)
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet vals s' => IntRet vals s'
       | Error e => Error e)
Proof
  rpt strip_tac >>
  Cases_on `r` >> gvs[] >>
  Cases_on `step_inst fuel' ctx' inst s` >>
  gvs[lift_result_def]
QED

(* When step_inst returns OK for an INVOKE instruction, all intermediate
   decode/lookup/eval/setup steps must have succeeded. This avoids 4 nested
   NONE case splits in run_block_cross_ctx. *)
Triviality step_inst_invoke_ok_decompose:
  step_inst fuel ctx inst s = OK v /\
  inst.inst_opcode = INVOKE ==>
  ?h_name arg_ops h args callee_s vals callee_s'.
    decode_invoke inst = SOME (h_name, arg_ops) /\
    lookup_function h_name ctx.ctx_functions = SOME h /\
    eval_operands arg_ops s = SOME args /\
    setup_callee h args s = SOME callee_s /\
    run_function fuel ctx h callee_s = IntRet vals callee_s' /\
    bind_outputs inst.inst_outputs vals (merge_callee_state s callee_s') = SOME v
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  ASM_REWRITE_TAC[step_inst_def] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >>
  CASE_TAC
QED

(* Shared tactic for non-OK step_inst results in run_block_cross_ctx.
   Used for Halt, Abort, IntRet, Error cases. Assumes step_inst result
   is known (from Cases_on) and callee_hyp is available. *)
val vs_inst_idx_update = prove(
  ``!(v:venom_state) x. (v with vs_inst_idx := x).vs_inst_idx = x``,
  simp[]);
val exec_result_distinct_sym = GSYM exec_result_distinct;
val RB_NON_OK_TAC =
  ASM_REWRITE_TAC[] >>
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
  Cases_on `inst.inst_opcode = INVOKE` >| [
    mp_tac (Q.SPECL [`fuel`, `ctx`, `ctx'`, `inst`, `s`,
      `step_inst fuel ctx inst s`] step_inst_invoke_non_ok_cross_ctx) >>
    (impl_tac >- (
      rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      ASM_REWRITE_TAC[exec_result_distinct, exec_result_distinct_sym])) >>
    strip_tac >> qexists_tac `fuel'` >>
    (* Rewrite lift_result to use constructor form, then case-split right *)
    qpat_x_assum `lift_result _ _ _ (step_inst _ ctx' _ _)` mp_tac >>
    ASM_REWRITE_TAC[] >>
    Cases_on `step_inst fuel' ctx' inst s` >>
    REWRITE_TAC[lift_result_def, exec_result_case_def] >> BETA_TAC >>
    REWRITE_TAC[lift_result_def, shared_globals_np_refl]
  ,
    mp_tac (Q.SPECL [`fuel`, `0`, `ctx`, `ctx'`, `inst`, `s`]
      step_inst_cross_ctx) >>
    ASM_REWRITE_TAC[] >>
    DISCH_THEN (ASSUME_TAC o SYM) >>
    qexists_tac `0` >> ASM_REWRITE_TAC[] >>
    REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
    REWRITE_TAC[lift_result_def, shared_globals_np_refl]
  ];

val is_terminator_invoke = EVAL ``is_terminator INVOKE``;

Triviality run_block_cross_ctx:
  !n fuel ctx ctx' bb s.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    (!h_name h callee_s.
      lookup_function h_name ctx.ctx_functions = SOME h ==>
      ?h'.
        lookup_function h_name ctx'.ctx_functions = SOME h' /\
        ~NULL h.fn_blocks /\ ~NULL h'.fn_blocks /\
        (HD h.fn_blocks).bb_label = (HD h'.fn_blocks).bb_label /\
        ?fuel_h.
          lift_result (=) shared_globals_np
            (run_function fuel ctx h callee_s)
            (run_function fuel_h ctx' h' callee_s)) ==>
    ?fuel'.
      lift_result (=) shared_globals_np
        (run_block fuel ctx bb s)
        (run_block fuel' ctx' bb s)
Proof
  completeInduct_on `n` >>
  rpt strip_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qexists_tac `0` >>
      REWRITE_TAC[optionTheory.option_case_def] >> BETA_TAC >>
      REWRITE_TAC[lift_result_def]) >>
  rename [`get_instruction _ _ = SOME inst`] >>
  (* Establish index bound from get_instruction *)
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by (
    qpat_assum `get_instruction _ _ = SOME _` mp_tac >>
    REWRITE_TAC[get_instruction_def] >>
    CASE_TAC >> REWRITE_TAC[]) >>
  (* Reduce option case *)
  REWRITE_TAC[optionTheory.option_case_def] >> BETA_TAC >>
  (* Case split on left step_inst result *)
  Cases_on `step_inst fuel ctx inst s` >> (
    TRY RB_NON_OK_TAC) >>
  (* Only OK case remains *)
  Cases_on `inst.inst_opcode = INVOKE` >- (
    (* INVOKE OK case *)
    REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
    ASM_REWRITE_TAC[] >>
    (* Step 1: Decompose INVOKE OK and specialize callee hyp *)
    drule_all step_inst_invoke_ok_decompose >> strip_tac >>
    first_assum (qspecl_then [`h_name`, `h`, `callee_s`] mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    strip_tac >>
    (* Step 2: setup_callee equality — forward reasoning, no by-block *)
    mp_tac (Q.SPECL [`h`, `h'`, `args`, `s`] setup_callee_entry_eq) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    DISCH_TAC >>
    (* Now have: setup_callee h args s = setup_callee h' args s *)
    (* Derive: setup_callee h' args s = SOME callee_s *)
    `setup_callee h' args s = SOME callee_s` by metis_tac[] >>
    (* Step 3: cross-ctx step_inst — forward reasoning *)
    mp_tac (Q.SPECL [`fuel`, `fuel_h`, `ctx`, `ctx'`, `inst`, `s`,
                      `h`, `h'`, `callee_s`, `h_name`, `arg_ops`, `args`]
      step_inst_invoke_cross_ctx_general) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    (* lift_result (=) shared_globals_np (step_inst fuel ...) (step_inst fuel_h ...) *)
    qpat_x_assum `step_inst fuel ctx inst s = OK v`
      (fn th => ASSUME_TAC th >> REWRITE_TAC[th]) >>
    (* Now goal becomes: lift_result ... (OK v) (step_inst fuel_h ctx' inst s) ==> ... *)
    Cases_on `step_inst fuel_h ctx' inst s` >>
    REWRITE_TAC[lift_result_def, exec_result_distinct, exec_result_distinct_sym] >>
    (* Only OK case survives. v = v' from equality, step_inst fuel_h ctx' inst s = OK v' *)
    DISCH_TAC >>
    (* Substitute v' = v *)
    qpat_x_assum `v = v'` (SUBST_ALL_TAC o SYM) >>
    (* Step 4: IH for continuation — keep callee hyp with first_assum *)
    qpat_x_assum `!m. m < n ==> _`
      (fn ih => ASSUME_TAC ih >>
        mp_tac (Q.SPEC `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` ih)) >>
    (impl_tac >- DECIDE_TAC) >>
    disch_then (qspecl_then [`fuel`, `ctx`, `ctx'`, `bb`,
      `v with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
    REWRITE_TAC[vs_inst_idx_update] >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    strip_tac >>
    (* Step 5: Error/non-Error case split *)
    Cases_on `?e. run_block fuel' ctx' bb
                (v with vs_inst_idx := SUC s.vs_inst_idx) = Error e` >- (
      (* Error case: fuel 0 trick *)
      pop_assum strip_assume_tac >>
      qexists_tac `0` >>
      mp_tac (Q.SPECL [`ctx'`, `inst`, `s`] step_inst_invoke_zero_error) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      strip_tac >> ASM_REWRITE_TAC[] >>
      REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
      REWRITE_TAC[is_terminator_invoke] >>
      qpat_x_assum `lift_result _ _ (run_block fuel _ _ _) _` mp_tac >>
      ASM_REWRITE_TAC[] >>
      Cases_on `run_block fuel ctx bb (v with vs_inst_idx := SUC s.vs_inst_idx)` >>
      REWRITE_TAC[lift_result_def]) >>
    (* Non-Error: use MAX fuel_h fuel' *)
    qexists_tac `MAX fuel_h fuel'` >>
    (* step_inst (MAX fuel_h fuel') = step_inst fuel_h = OK v *)
    mp_tac (Q.SPECL [`fuel_h`, `MAX fuel_h fuel'`, `ctx'`, `inst`, `s`]
      step_inst_fuel_mono_ge) >>
    (impl_tac >- (
      conj_tac >- (
        REWRITE_TAC[arithmeticTheory.MAX_DEF] >> DECIDE_TAC) >>
      ASM_REWRITE_TAC[exec_result_distinct])) >>
    DISCH_TAC >> ASM_REWRITE_TAC[] >>
    REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
    REWRITE_TAC[is_terminator_invoke] >>
    (* run_block (MAX ..) = run_block fuel' *)
    mp_tac (Q.SPECL [`fuel'`, `MAX fuel_h fuel'`, `ctx'`, `bb`,
      `v with vs_inst_idx := SUC s.vs_inst_idx`] run_block_fuel_mono_ge) >>
    (impl_tac >- (
      conj_tac >- (
        REWRITE_TAC[arithmeticTheory.MAX_DEF] >> DECIDE_TAC) >>
      metis_tac[])) >>
    DISCH_TAC >> ASM_REWRITE_TAC[]) >>
  (* Non-INVOKE OK: step_inst is ctx-independent *)
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[] >>
  Cases_on `is_terminator inst.inst_opcode` >- (
    (* Terminator *)
    qexists_tac `0` >>
    mp_tac (Q.SPECL [`0`, `fuel`, `ctx'`, `ctx`, `inst`, `s`]
      step_inst_cross_ctx) >>
    ASM_REWRITE_TAC[] >>
    DISCH_TAC >> ASM_REWRITE_TAC[] >>
    REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
    ASM_REWRITE_TAC[lift_result_eq_sgnp_refl]) >>
  (* Non-terminator: use IH for continuation, step_inst_cross_ctx for step *)
  ASM_REWRITE_TAC[] >>
  (* Instantiate IH *)
  qpat_x_assum `!m. m < n ==> _`
    (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- DECIDE_TAC) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `ctx'`, `bb`,
    `v with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  REWRITE_TAC[vs_inst_idx_update] >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  qexists_tac `fuel'` >>
  mp_tac (Q.SPECL [`fuel'`, `fuel`, `ctx'`, `ctx`, `inst`, `s`]
    step_inst_cross_ctx) >>
  ASM_REWRITE_TAC[] >>
  DISCH_TAC >> ASM_REWRITE_TAC[] >>
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[]
QED



(* Main ctx-replacement: same function g, different contexts.
   Hypothesis (strengthened): every function in ctx has a corresponding
   function in ctx' with matching entry labels and related behavior. *)
(* Unfold run_function at SUC fuel with lookup_block = SOME bb in assumptions.
   Produces: case run_block fuel ctx bb s of OK ... | Halt ... | ... *)
val UNFOLD_RF_SUC_TAC =
  ONCE_REWRITE_TAC[run_function_def] >>
  REWRITE_TAC[arithmeticTheory.num_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[] >>
  REWRITE_TAC[optionTheory.option_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[] >>
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC;

Triviality run_function_cross_ctx_ok_case:
  !fuel ctx ctx' g s bb v fuel_b.
    run_block fuel ctx bb s = OK v /\
    run_block fuel_b ctx' bb s = OK v /\
    lookup_block s.vs_current_bb g.fn_blocks = SOME bb /\
    (!f h_name h callee_s.
      f < SUC fuel /\
      lookup_function h_name ctx.ctx_functions = SOME h ==>
      ?h'.
        lookup_function h_name ctx'.ctx_functions = SOME h' /\
        ~NULL h.fn_blocks /\ ~NULL h'.fn_blocks /\
        (HD h.fn_blocks).bb_label = (HD h'.fn_blocks).bb_label /\
        ?fuel_h.
          lift_result (=) shared_globals_np
            (run_function f ctx h callee_s)
            (run_function fuel_h ctx' h' callee_s)) /\
    (!ctx ctx' g s.
      (!f h_name h callee_s.
        f < fuel /\
        lookup_function h_name ctx.ctx_functions = SOME h ==>
        ?h'.
          lookup_function h_name ctx'.ctx_functions = SOME h' /\
          ~NULL h.fn_blocks /\ ~NULL h'.fn_blocks /\
          (HD h.fn_blocks).bb_label = (HD h'.fn_blocks).bb_label /\
          ?fuel_h.
            lift_result (=) shared_globals_np
              (run_function f ctx h callee_s)
              (run_function fuel_h ctx' h' callee_s)) ==>
      ?fuel'.
        lift_result (=) shared_globals_np
          (run_function fuel ctx g s)
          (run_function fuel' ctx' g s)) ==>
    ?fuel'.
      lift_result (=) shared_globals_np
        (run_function (SUC fuel) ctx g s)
        (run_function fuel' ctx' g s)
Proof
  rpt strip_tac >>
  Cases_on `v.vs_halted`
  >- (
    qexists_tac `SUC fuel_b` >> UNFOLD_RF_SUC_TAC >>
    ASM_REWRITE_TAC[lift_result_def, shared_globals_np_refl])
  >> (
  (* not halted: apply IH *)
  first_x_assum (qspecl_then [`ctx`, `ctx'`, `g`, `v`] mp_tac) >>
  (impl_tac >- (
    rpt strip_tac >>
    first_x_assum (qspecl_then [`f`, `h_name`, `h`, `callee_s`] mp_tac) >>
    simp[])) >>
  strip_tac >>
  rename [`lift_result _ _ (run_function fuel ctx g v)
                           (run_function fuel_c ctx' g v)`] >>
  Cases_on `terminates (run_function fuel_c ctx' g v)`
  >- (
    (* terminates: use MAX for both *)
    qexists_tac `SUC (MAX fuel_b fuel_c)` >>
    `run_block (MAX fuel_b fuel_c) ctx' bb s = OK v` by (
      `run_block (MAX fuel_b fuel_c) ctx' bb s = run_block fuel_b ctx' bb s`
        suffices_by ASM_REWRITE_TAC[] >>
      irule run_block_fuel_mono_ge >>
      conj_tac >- simp[] >>
      rpt strip_tac >> gvs[]) >>
    `run_function (MAX fuel_b fuel_c) ctx' g v =
     run_function fuel_c ctx' g v` by (
      irule run_function_fuel_mono_ge >> ASM_REWRITE_TAC[] >> simp[]) >>
    UNFOLD_RF_SUC_TAC >> ASM_REWRITE_TAC[])
  >> (
  (* not terminates: both sides Error, choose fuel'=0 *)
  gvs[terminates_def] >>
  Cases_on `run_function fuel_c ctx' g v` >> gvs[] >>
  qpat_x_assum `lift_result _ _ _ (Error _)` mp_tac >>
  Cases_on `run_function fuel ctx g v` >>
  REWRITE_TAC[lift_result_def] >>
  qexists_tac `0` >>
  ONCE_REWRITE_TAC[run_function_def] >>
  REWRITE_TAC[arithmeticTheory.num_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[] >>
  REWRITE_TAC[optionTheory.option_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[] >>
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[lift_result_def]))
QED

Theorem run_function_cross_ctx:
  !fuel ctx ctx' g s.
    (!f h_name h callee_s.
      f < fuel /\
      lookup_function h_name ctx.ctx_functions = SOME h ==>
      ?h'.
        lookup_function h_name ctx'.ctx_functions = SOME h' /\
        ~NULL h.fn_blocks /\ ~NULL h'.fn_blocks /\
        (HD h.fn_blocks).bb_label = (HD h'.fn_blocks).bb_label /\
        ?fuel_h.
          lift_result (=) shared_globals_np
            (run_function f ctx h callee_s)
            (run_function fuel_h ctx' h' callee_s)) ==>
    ?fuel'.
      lift_result (=) shared_globals_np
        (run_function fuel ctx g s)
        (run_function fuel' ctx' g s)
Proof
  Induct_on `fuel`
  >- (
    rpt strip_tac >> qexists_tac `0` >>
    ONCE_REWRITE_TAC[run_function_def] >> simp[lift_result_def])
  >> (
  rpt strip_tac >>
  Cases_on `lookup_block s.vs_current_bb g.fn_blocks`
  >- (
    qexists_tac `0` >>
    ONCE_REWRITE_TAC[run_function_def] >> simp[lift_result_def])
  >>
  rename [`lookup_block _ _ = SOME bb`] >>
  mp_tac (Q.SPECL [`LENGTH bb.bb_instructions - s.vs_inst_idx`,
                    `fuel`, `ctx`, `ctx'`, `bb`, `s`] run_block_cross_ctx) >>
  (impl_tac >- (
    conj_tac >- simp[] >>
    rpt strip_tac >>
    first_x_assum (qspecl_then [`fuel`, `h_name`, `h`, `callee_s`] mp_tac) >>
    (impl_tac >- simp[]) >> metis_tac[])) >>
  strip_tac >>
  rename [`lift_result _ _ (run_block fuel ctx bb s)
                           (run_block fuel_b ctx' bb s)`] >>
  Cases_on `run_block fuel ctx bb s` >>
  Cases_on `run_block fuel_b ctx' bb s` >>
  gvs[lift_result_def]
  (* OK / OK: use helper *)
  >- (mp_tac (Q.SPECL [`fuel`, `ctx`, `ctx'`, `g`, `s`, `bb`, `v`, `fuel_b`]
        run_function_cross_ctx_ok_case) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      strip_tac >> qexists_tac `fuel'` >> ASM_REWRITE_TAC[])
  (* Halt / Halt *)
  >- (
    qexists_tac `SUC fuel_b` >> UNFOLD_RF_SUC_TAC >>
    REWRITE_TAC[lift_result_def] >> ASM_REWRITE_TAC[])
  (* Abort / Abort *)
  >- (
    qexists_tac `SUC fuel_b` >> UNFOLD_RF_SUC_TAC >>
    REWRITE_TAC[lift_result_def] >> ASM_REWRITE_TAC[])
  (* IntRet / IntRet *)
  >- (
    qexists_tac `SUC fuel_b` >> UNFOLD_RF_SUC_TAC >>
    REWRITE_TAC[lift_result_def] >> ASM_REWRITE_TAC[])
  >>
  (* Error / Error *)
  qexists_tac `0` >>
  ONCE_REWRITE_TAC[run_function_def] >> simp[lift_result_def])
QED

(* ================================================================
   FOLDL CORRESPONDENCE: inline_candidate maps each function
   through inline_at_sites, preserving names and order.
   ================================================================ *)

(* For each function in ctx, there is a corresponding function in ctx'
   produced by inline_at_sites *)
Triviality exists_find_some:
  !P l. EXISTS P l ==> ?x. FIND P l = SOME x
Proof
  Induct_on `l` >> simp[listTheory.FIND_thm] >> rw[]
QED

(* Local version of inline_candidate_fn_names — same proof pattern *)
Triviality inline_candidate_fn_names_local:
  !ctx callee ist ctx' ist'.
    inline_candidate ctx callee ist = (ctx', ist') ==>
    MAP (\f. f.fn_name) ctx'.ctx_functions =
    MAP (\f. f.fn_name) ctx.ctx_functions
Proof
  rw[inline_candidate_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_abbrev_tac `fns = ctx.ctx_functions` >>
  `!acc ist0 fns0 result ist1.
     FOLDL (\(fns_acc, st) caller_fn.
       let max_sites = LENGTH (fn_insts caller_fn) in
       let (caller', st') = inline_at_sites max_sites caller_fn callee st in
       (SNOC caller' fns_acc, st'))
       (acc, ist0) fns0 = (result, ist1) ==>
     MAP (\f. f.fn_name) result =
     MAP (\f. f.fn_name) acc ++ MAP (\f. f.fn_name) fns0` suffices_by
    (disch_then (qspecl_then [`[]`, `ist`, `fns`] mp_tac) >>
     simp[]) >>
  Induct_on `fns0` >- simp[] >>
  rpt strip_tac >>
  gvs[LET_THM] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  imp_res_tac inline_at_sites_fn_name >>
  gvs[listTheory.MAP_SNOC, listTheory.SNOC_APPEND]
QED

Theorem inline_candidate_fn_correspondence:
  !ctx callee ist ctx' ist' name g.
    inline_candidate ctx callee ist = (ctx', ist') /\
    lookup_function name ctx.ctx_functions = SOME g ==>
    ?g'. lookup_function name ctx'.ctx_functions = SOME g'
Proof
  rpt strip_tac >>
  drule inline_candidate_fn_names_local >> strip_tac >>
  fs[lookup_function_def] >>
  imp_res_tac FIND_pred >> fs[] >>
  imp_res_tac (REWRITE_RULE [lookup_function_def] lookup_function_MEM) >>
  `MEM name (MAP (\f. f.fn_name) ctx.ctx_functions)` by
    (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
  `MEM name (MAP (\f. f.fn_name) ctx'.ctx_functions)` by metis_tac[] >>
  pop_assum mp_tac >> simp[listTheory.MEM_MAP] >> strip_tac >>
  `EXISTS (\f. f.fn_name = name) ctx'.ctx_functions` by
    (simp[listTheory.EXISTS_MEM] >> metis_tac[]) >>
  metis_tac[exists_find_some]
QED

(* --- Entry label preservation chain --- *)

(* renumber_fn_inst_ids preserves entry label *)
Triviality renumber_entry_label:
  !f. ~NULL f.fn_blocks ==>
    ~NULL (renumber_fn_inst_ids f).fn_blocks /\
    (HD (renumber_fn_inst_ids f).fn_blocks).bb_label =
    (HD f.fn_blocks).bb_label
Proof
  gen_tac >> strip_tac >>
  `LENGTH (renumber_fn_inst_ids f).fn_blocks =
   LENGTH f.fn_blocks` by simp[renumber_fn_inst_ids_length] >>
  `fn_labels (renumber_fn_inst_ids f) = fn_labels f` by
    simp[renumber_fn_inst_ids_fn_labels] >>
  Cases_on `f.fn_blocks` >> fs[fn_labels_def] >>
  Cases_on `(renumber_fn_inst_ids f).fn_blocks` >> fs[]
QED

(* fix_inline_phis preserves entry label *)
Triviality fix_phis_entry_label:
  !ol nl rb f. ~NULL f.fn_blocks ==>
    ~NULL (fix_inline_phis ol nl rb f).fn_blocks /\
    (HD (fix_inline_phis ol nl rb f).fn_blocks).bb_label =
    (HD f.fn_blocks).bb_label
Proof
  rw[fix_inline_phis_def, LET_THM] >>
  Cases_on `f.fn_blocks` >> fs[] >> rw[]
QED

(* inline_call_site preserves entry label *)
Triviality inline_call_site_entry_label:
  !prefix ret_lbl caller callee_fn bb_lbl idx.
    ~NULL caller.fn_blocks ==>
    ~NULL (inline_call_site prefix ret_lbl caller callee_fn bb_lbl idx).fn_blocks /\
    (HD (inline_call_site prefix ret_lbl caller callee_fn bb_lbl idx).fn_blocks).bb_label =
    (HD caller.fn_blocks).bb_label
Proof
  rw[inline_call_site_def, LET_THM] >>
  Cases_on `lookup_block bb_lbl caller.fn_blocks` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `caller.fn_blocks` >> fs[replace_block_def] >>
  rw[] >> fs[lookup_block_def] >> imp_res_tac FIND_pred >> fs[]
QED

(* inline_one_site preserves entry label *)
Triviality inline_one_site_entry_label:
  !caller callee_fn ist caller' ist'.
    inline_one_site caller callee_fn ist = SOME (caller', ist') ==>
    ~NULL caller.fn_blocks ==>
    ~NULL caller'.fn_blocks /\
    (HD caller'.fn_blocks).bb_label = (HD caller.fn_blocks).bb_label
Proof
  rpt gen_tac >>
  simp[inline_one_site_def, LET_THM] >>
  Cases_on `find_invoke_site callee_fn.fn_name caller.fn_blocks` >> simp[] >>
  Cases_on `x` >> simp[] >>
  qabbrev_tac `ics = inline_call_site
    (inline_prefix ist.is_inline_count)
    (return_block_label (inline_prefix ist.is_inline_count)
       ist.is_label_counter)
    caller callee_fn q r` >>
  Cases_on `lookup_block
    (return_block_label (inline_prefix ist.is_inline_count)
       ist.is_label_counter) ics.fn_blocks` >>
  simp[] >> strip_tac >> gvs[] >> strip_tac >>
  (`~NULL ics.fn_blocks /\
   (HD ics.fn_blocks).bb_label = (HD caller.fn_blocks).bb_label` by
    (qunabbrev_tac `ics` >> metis_tac[inline_call_site_entry_label])) >>
  metis_tac[renumber_entry_label, fix_phis_entry_label]
QED

(* inline_at_sites preserves entry label *)
Triviality inline_at_sites_entry_label:
  !n caller callee_fn ist caller' ist'.
    inline_at_sites n caller callee_fn ist = (caller', ist') ==>
    ~NULL caller.fn_blocks ==>
    ~NULL caller'.fn_blocks /\
    (HD caller'.fn_blocks).bb_label = (HD caller.fn_blocks).bb_label
Proof
  Induct_on `n` >> simp[inline_at_sites_def] >>
  rpt gen_tac >>
  Cases_on `inline_one_site caller callee_fn ist` >> simp[] >>
  Cases_on `x` >> simp[] >> strip_tac >> strip_tac >>
  imp_res_tac inline_one_site_entry_label >>
  metis_tac[]
QED

(* FIND over SNOC: first match in original list wins, else check new element *)
Triviality FIND_SNOC:
  !P x l. FIND P (SNOC x l) =
    case FIND P l of SOME y => SOME y | NONE => if P x then SOME x else NONE
Proof
  Induct_on `l` >> simp[listTheory.FIND_thm, listTheory.SNOC] >> rw[]
QED

(* FOLDL preserves existing FIND result in accumulator.
   Key insight: each step SNOCs to acc, and FIND_SNOC says SOME in prefix wins. *)
Triviality foldl_inline_find_preserved:
  !fns0 acc ist0 result ist1 name g0.
    FOLDL (\(fns_acc, st) caller_fn.
      let max_sites = LENGTH (fn_insts caller_fn) in
      let (caller', st') = inline_at_sites max_sites caller_fn callee st in
      (SNOC caller' fns_acc, st'))
      (acc, ist0) fns0 = (result, ist1) /\
    FIND (\f. f.fn_name = name) acc = SOME g0 ==>
    FIND (\f. f.fn_name = name) result = SOME g0
Proof
  Induct_on `fns0`
  >- (rpt strip_tac >> gvs[])
  >> (rpt gen_tac >> simp[] >> strip_tac >>
      gvs[LET_THM] >> pairarg_tac >> gvs[] >>
      first_x_assum (qspecl_then [`SNOC caller' acc`, `st'`,
        `result`, `ist1`, `name`, `g0`] mp_tac) >>
      simp[FIND_SNOC] >>
      REWRITE_TAC[optionTheory.option_case_def] >> BETA_TAC >>
      ASM_REWRITE_TAC[])
QED

(* inline_at_sites never decreases is_inline_count *)
Triviality inline_at_sites_count_mono:
  !n fn callee ist fn' ist'.
    inline_at_sites n fn callee ist = (fn', ist') ==>
    ist.is_inline_count <= ist'.is_inline_count
Proof
  Induct >> rw[inline_at_sites_def] >>
  Cases_on `inline_one_site fn callee ist` >> gvs[] >>
  Cases_on `x` >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  gvs[inline_one_site_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* Strong FOLDL lemma: relates FIND in input to inline_at_sites relationship in output.
   For each function g found in the input list, the output contains g' = inline_at_sites(g)
   at some intermediate inline state, with count monotonicity. *)
Triviality foldl_inline_find_entry:
  !fns0 acc ist0 result ist1 name g.
    FOLDL (\(fns_acc, st) caller_fn.
      let max_sites = LENGTH (fn_insts caller_fn) in
      let (fn_out, ist_out) = inline_at_sites max_sites caller_fn callee st in
      (SNOC fn_out fns_acc, ist_out))
      (acc, ist0) fns0 = (result, ist1) /\
    FIND (\f. f.fn_name = name) acc = NONE /\
    FIND (\f. f.fn_name = name) fns0 = SOME g ==>
    ?g' ist_i ist_i'.
      FIND (\f. f.fn_name = name) result = SOME g' /\
      inline_at_sites (LENGTH (fn_insts g)) g callee ist_i = (g', ist_i') /\
      ist0.is_inline_count <= ist_i.is_inline_count
Proof
  Induct_on `fns0` >- simp[FIND_thm] >>
  rpt gen_tac >> simp[FIND_thm] >> strip_tac >>
  gvs[LET_THM] >> pairarg_tac >> gvs[] >>
  imp_res_tac inline_at_sites_fn_name >>
  imp_res_tac inline_at_sites_count_mono >>
  Cases_on `h.fn_name = name` >> gvs[]
  >- ((* h IS the match: g = h, name = fn_out.fn_name *)
   `FIND (\f. f.fn_name = fn_out.fn_name) (SNOC fn_out acc) = SOME fn_out`
     by simp[FIND_SNOC] >>
   drule_all (SRULE [LET_THM] foldl_inline_find_preserved) >>
   strip_tac >>
   metis_tac[arithmeticTheory.LESS_EQ_REFL])
  >> ((* h is NOT the match — use IH *)
   first_x_assum drule >>
   disch_then (qspecl_then [`name`, `g`] mp_tac) >>
   (impl_tac >- simp[FIND_SNOC]) >>
   strip_tac >>
   metis_tac[arithmeticTheory.LESS_EQ_TRANS])
QED

(* The FOLDL preserves entry block label for each function *)
Theorem inline_candidate_entry_label_preserved:
  !ctx callee ist ctx' ist' name g g'.
    inline_candidate ctx callee ist = (ctx', ist') /\
    lookup_function name ctx.ctx_functions = SOME g /\
    lookup_function name ctx'.ctx_functions = SOME g' /\
    ~NULL g.fn_blocks ==>
    ~NULL g'.fn_blocks /\
    (HD g'.fn_blocks).bb_label = (HD g.fn_blocks).bb_label
Proof
  rpt gen_tac >> strip_tac >>
  gvs[inline_candidate_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  gvs[lookup_function_def] >>
  mp_tac (Q.SPECL [`ctx.ctx_functions`, `[]:ir_function list`, `ist`,
    `fns'`, `ist'`, `name`, `g`] foldl_inline_find_entry) >>
  simp[listTheory.FIND_thm] >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  metis_tac[inline_at_sites_entry_label]
QED

(* run_function_cross_ctx_static DELETED — unprovable with just entry-label
   correspondence. The combined cross-ctx + per-fn argument is done directly
   inside inline_candidate_correct using run_function_cross_ctx +
   lift_result_change_ok + inline_at_sites_fn_correct. *)

(* ================================================================
   MAIN THEOREM: inline_candidate_correct

   Composition:
   1. run_function fuel ctx g s
        ~ (cross-ctx) run_function F1 ctx' g s   [via run_function_cross_ctx_static]
        ~ (per-fn)    run_function F2 ctx' g' s   [via inline_at_sites_fn_correct]
   2. Compose via lift_result_eq_then
   3. Lift to run_context
   ================================================================ *)

(* Combined cross-ctx + per-fn equivalence for all fuel levels.
   Key insight: run_function never returns OK, so lift_result_change_ok
   converts state_equiv to (=) for R_ok — only R_term (shared_globals_np)
   matters for run_function results.

   Proof by strong induction on fuel. At each level:
   (a) Cross-ctx: get run_function fuel ctx h s ≈ run_function F1 ctx' h s
       via run_function_cross_ctx, callee hyp by IH
   (b) Per-fn: get run_function F1 ctx' h s ≈ run_function F2 ctx' h' s
       via inline_at_sites_fn_correct
   (c) Compose via lift_result_trans

   The callee hypothesis of run_function_cross_ctx has universal callee_s,
   but the IH requires init_conds. This is resolved because callee_s in
   run_function_cross_ctx comes from setup_callee, which satisfies
   init_conds when the parent state has FDOM vs_labels = {}.
   We restrict callee_s in the callee hyp using a custom wrapper. *)

(* Helper: setup_callee produces states satisfying init_conds *)
Triviality setup_callee_init_conds:
  !fn args s callee_s.
    setup_callee fn args s = SOME callee_s /\
    FDOM s.vs_labels = {} ==>
    callee_s.vs_prev_bb = NONE /\
    callee_s.vs_inst_idx = 0 /\
    FDOM callee_s.vs_labels = {} /\
    ~callee_s.vs_halted
Proof
  rpt gen_tac >> simp[setup_callee_def] >> rw[] >> simp[]
QED

(* Helper: vs_inst_idx update preserves vs_labels *)
val vs_labels_inst_idx_update = prove(
  ``!(v:venom_state) x. (v with vs_inst_idx := x).vs_labels = v.vs_labels``,
  simp[]);

(* Restricted step_inst_invoke_non_ok_cross_ctx: callee hypothesis requires
   init_conds, plus FDOM s.vs_labels = {} to derive init_conds from setup_callee.
   Proof identical to unrestricted version except for callee hyp discharge. *)
Triviality step_inst_invoke_non_ok_cross_ctx_restricted:
  !fuel ctx ctx' inst s r.
    step_inst fuel ctx inst s = r /\
    (!v. r <> OK v) /\
    inst.inst_opcode = INVOKE /\
    FDOM s.vs_labels = {} /\
    (!h_name h callee_s.
      lookup_function h_name ctx.ctx_functions = SOME h /\
      callee_s.vs_prev_bb = NONE /\
      callee_s.vs_inst_idx = 0 /\
      FDOM callee_s.vs_labels = {} /\
      ~callee_s.vs_halted ==>
      ?h'.
        lookup_function h_name ctx'.ctx_functions = SOME h' /\
        ~NULL h.fn_blocks /\ ~NULL h'.fn_blocks /\
        (HD h.fn_blocks).bb_label = (HD h'.fn_blocks).bb_label /\
        ?fuel_h.
          lift_result (=) shared_globals_np
            (run_function fuel ctx h callee_s)
            (run_function fuel_h ctx' h' callee_s)) ==>
    ?fuel'.
      lift_result (=) shared_globals_np r (step_inst fuel' ctx' inst s)
Proof
  rpt strip_tac >>
  Cases_on `decode_invoke inst`
  >- (
    qexists_tac `0` >>
    `?e. step_inst 0 ctx' inst s = Error e` by
      metis_tac[step_inst_invoke_zero_error] >>
    `?e'. r = Error e'` by (
      qpat_x_assum `step_inst _ _ _ _ = r` (SUBST_ALL_TAC o SYM) >>
      simp[step_inst_def]) >>
    ASM_REWRITE_TAC[lift_result_def])
  >>
  PairCases_on `x` >> rename [`SOME (h_name, arg_ops)`] >>
  Cases_on `lookup_function h_name ctx.ctx_functions`
  >- (
    qexists_tac `0` >>
    `?e. step_inst 0 ctx' inst s = Error e` by
      metis_tac[step_inst_invoke_zero_error] >>
    `?e'. r = Error e'` by (
      qpat_x_assum `step_inst _ _ _ _ = r` (SUBST_ALL_TAC o SYM) >>
      simp[step_inst_def]) >>
    ASM_REWRITE_TAC[lift_result_def])
  >>
  rename [`lookup_function _ ctx.ctx_functions = SOME h`] >>
  Cases_on `eval_operands arg_ops s`
  >- (
    qexists_tac `0` >>
    `?e. step_inst 0 ctx' inst s = Error e` by
      metis_tac[step_inst_invoke_zero_error] >>
    `?e'. r = Error e'` by (
      qpat_x_assum `step_inst _ _ _ _ = r` (SUBST_ALL_TAC o SYM) >>
      simp[step_inst_def]) >>
    ASM_REWRITE_TAC[lift_result_def])
  >>
  rename [`eval_operands _ _ = SOME args`] >>
  Cases_on `setup_callee h args s`
  >- (
    qexists_tac `0` >>
    `?e. step_inst 0 ctx' inst s = Error e` by
      metis_tac[step_inst_invoke_zero_error] >>
    `?e'. r = Error e'` by (
      qpat_x_assum `step_inst _ _ _ _ = r` (SUBST_ALL_TAC o SYM) >>
      simp[step_inst_def]) >>
    ASM_REWRITE_TAC[lift_result_def])
  >>
  rename [`setup_callee h _ _ = SOME callee_s`] >>
  (* Derive init_conds for callee_s from setup_callee + FDOM s.vs_labels = {} *)
  mp_tac (Q.SPECL [`h`, `args`, `s`, `callee_s`] setup_callee_init_conds) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  (* Now specialize restricted callee_hyp *)
  first_x_assum (qspecl_then [`h_name`, `h`, `callee_s`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  (* setup_callee h' args s = SOME callee_s via forward reasoning *)
  mp_tac (Q.SPECL [`h`, `h'`, `args`, `s`] setup_callee_entry_eq) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  DISCH_TAC >>
  qpat_x_assum `setup_callee h args s = setup_callee h' args s` mp_tac >>
  ASM_REWRITE_TAC[] >>
  DISCH_THEN (ASSUME_TAC o SYM) >>
  (* All SOME: use step_inst_invoke_cross_ctx_general *)
  qexists_tac `fuel_h` >>
  mp_tac (Q.SPECL [`fuel`, `fuel_h`, `ctx`, `ctx'`, `inst`, `s`,
    `h`, `h'`, `callee_s`, `h_name`, `arg_ops`, `args`]
    step_inst_invoke_cross_ctx_general) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = r` (SUBST_ALL_TAC o SYM) >>
  ASM_REWRITE_TAC[]
QED

(* Restricted RB_NON_OK_TAC: uses restricted callee hyp + FDOM s.vs_labels = {} *)
val RB_NON_OK_TAC_R =
  ASM_REWRITE_TAC[] >>
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
  Cases_on `inst.inst_opcode = INVOKE` >| [
    mp_tac (Q.SPECL [`fuel`, `ctx`, `ctx'`, `inst`, `s`,
      `step_inst fuel ctx inst s`] step_inst_invoke_non_ok_cross_ctx_restricted) >>
    (impl_tac >- (
      rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      ASM_REWRITE_TAC[exec_result_distinct, exec_result_distinct_sym])) >>
    strip_tac >> qexists_tac `fuel'` >>
    qpat_x_assum `lift_result _ _ _ (step_inst _ ctx' _ _)` mp_tac >>
    ASM_REWRITE_TAC[] >>
    Cases_on `step_inst fuel' ctx' inst s` >>
    REWRITE_TAC[lift_result_def, exec_result_case_def] >> BETA_TAC >>
    REWRITE_TAC[lift_result_def, shared_globals_np_refl]
  ,
    mp_tac (Q.SPECL [`fuel`, `0`, `ctx`, `ctx'`, `inst`, `s`]
      step_inst_cross_ctx) >>
    ASM_REWRITE_TAC[] >>
    DISCH_THEN (ASSUME_TAC o SYM) >>
    qexists_tac `0` >> ASM_REWRITE_TAC[] >>
    REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
    REWRITE_TAC[lift_result_def, shared_globals_np_refl]
  ];

(* Restricted run_block_cross_ctx: callee hypothesis has init_conds.
   Adds FDOM s.vs_labels = {} to track the invariant through OK continuations. *)
Triviality run_block_cross_ctx_restricted:
  !n fuel ctx ctx' bb s.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    (!h_name h callee_s.
      lookup_function h_name ctx.ctx_functions = SOME h /\
      callee_s.vs_prev_bb = NONE /\
      callee_s.vs_inst_idx = 0 /\
      FDOM callee_s.vs_labels = {} /\
      ~callee_s.vs_halted ==>
      ?h'.
        lookup_function h_name ctx'.ctx_functions = SOME h' /\
        ~NULL h.fn_blocks /\ ~NULL h'.fn_blocks /\
        (HD h.fn_blocks).bb_label = (HD h'.fn_blocks).bb_label /\
        ?fuel_h.
          lift_result (=) shared_globals_np
            (run_function fuel ctx h callee_s)
            (run_function fuel_h ctx' h' callee_s)) /\
    FDOM s.vs_labels = {} ==>
    ?fuel'.
      lift_result (=) shared_globals_np
        (run_block fuel ctx bb s)
        (run_block fuel' ctx' bb s)
Proof
  completeInduct_on `n` >>
  rpt strip_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qexists_tac `0` >>
      REWRITE_TAC[optionTheory.option_case_def] >> BETA_TAC >>
      REWRITE_TAC[lift_result_def]) >>
  rename [`get_instruction _ _ = SOME inst`] >>
  (* Establish index bound from get_instruction *)
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by (
    qpat_assum `get_instruction _ _ = SOME _` mp_tac >>
    REWRITE_TAC[get_instruction_def] >>
    CASE_TAC >> REWRITE_TAC[]) >>
  (* Reduce option case *)
  REWRITE_TAC[optionTheory.option_case_def] >> BETA_TAC >>
  (* Case split on left step_inst result *)
  Cases_on `step_inst fuel ctx inst s` >> (
    TRY RB_NON_OK_TAC_R) >>
  (* Only OK case remains *)
  Cases_on `inst.inst_opcode = INVOKE` >- (
    (* INVOKE OK case *)
    REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
    ASM_REWRITE_TAC[] >>
    (* Step 1: Decompose INVOKE OK and specialize callee hyp *)
    drule_all step_inst_invoke_ok_decompose >> strip_tac >>
    (* Prove callee_s satisfies init_conds *)
    mp_tac (Q.SPECL [`h`, `args`, `s`, `callee_s`] setup_callee_init_conds) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    strip_tac >>
    (* Now specialize callee hyp with init_conds *)
    first_assum (qspecl_then [`h_name`, `h`, `callee_s`] mp_tac) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    strip_tac >>
    (* Step 2: setup_callee equality — forward reasoning *)
    mp_tac (Q.SPECL [`h`, `h'`, `args`, `s`] setup_callee_entry_eq) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    (* Derive setup_callee h' args s = SOME callee_s:
       grab equation, mp_tac, ASM_REWRITE rewrites h-side→SOME, SYM gives h'=SOME *)
    DISCH_TAC >>
    qpat_x_assum `setup_callee h args s = setup_callee h' args s` mp_tac >>
    ASM_REWRITE_TAC[] >>
    DISCH_THEN (ASSUME_TAC o SYM) >>
    (* Step 3: cross-ctx step_inst *)
    mp_tac (Q.SPECL [`fuel`, `fuel_h`, `ctx`, `ctx'`, `inst`, `s`,
                      `h`, `h'`, `callee_s`, `h_name`, `arg_ops`, `args`]
      step_inst_invoke_cross_ctx_general) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    qpat_x_assum `step_inst fuel ctx inst s = OK v`
      (fn th => ASSUME_TAC th >> REWRITE_TAC[th]) >>
    Cases_on `step_inst fuel_h ctx' inst s` >>
    REWRITE_TAC[lift_result_def, exec_result_distinct, exec_result_distinct_sym] >>
    DISCH_TAC >>
    qpat_x_assum `v = v'` (SUBST_ALL_TAC o SYM) >>
    (* vs_labels preserved through OK step_inst — forward reasoning *)
    mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s`, `v`]
      step_inst_preserves_labels_always) >>
    ASM_REWRITE_TAC[] >> DISCH_TAC >>
    (* Step 4: IH for continuation *)
    qpat_x_assum `!m. m < n ==> _`
      (fn ih => ASSUME_TAC ih >>
        mp_tac (Q.SPEC `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` ih)) >>
    (impl_tac >- DECIDE_TAC) >>
    disch_then (qspecl_then [`fuel`, `ctx`, `ctx'`, `bb`,
      `v with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
    REWRITE_TAC[vs_inst_idx_update, vs_labels_inst_idx_update] >>
    (impl_tac >- (
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      ASM_REWRITE_TAC[])) >>
    strip_tac >>
    (* Step 5: Error/non-Error case split *)
    Cases_on `?e. run_block fuel' ctx' bb
                (v with vs_inst_idx := SUC s.vs_inst_idx) = Error e` >- (
      pop_assum strip_assume_tac >>
      qexists_tac `0` >>
      mp_tac (Q.SPECL [`ctx'`, `inst`, `s`] step_inst_invoke_zero_error) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      strip_tac >> ASM_REWRITE_TAC[] >>
      REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
      REWRITE_TAC[is_terminator_invoke] >>
      qpat_x_assum `lift_result _ _ (run_block fuel _ _ _) _` mp_tac >>
      ASM_REWRITE_TAC[] >>
      Cases_on `run_block fuel ctx bb (v with vs_inst_idx := SUC s.vs_inst_idx)` >>
      REWRITE_TAC[lift_result_def]) >>
    (* Non-Error: use MAX fuel_h fuel' *)
    qexists_tac `MAX fuel_h fuel'` >>
    mp_tac (Q.SPECL [`fuel_h`, `MAX fuel_h fuel'`, `ctx'`, `inst`, `s`]
      step_inst_fuel_mono_ge) >>
    (impl_tac >- (
      conj_tac >- (
        REWRITE_TAC[arithmeticTheory.MAX_DEF] >> DECIDE_TAC) >>
      ASM_REWRITE_TAC[exec_result_distinct])) >>
    DISCH_TAC >> ASM_REWRITE_TAC[] >>
    REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
    REWRITE_TAC[is_terminator_invoke] >>
    mp_tac (Q.SPECL [`fuel'`, `MAX fuel_h fuel'`, `ctx'`, `bb`,
      `v with vs_inst_idx := SUC s.vs_inst_idx`] run_block_fuel_mono_ge) >>
    (impl_tac >- (
      conj_tac >- (
        REWRITE_TAC[arithmeticTheory.MAX_DEF] >> DECIDE_TAC) >>
      metis_tac[])) >>
    DISCH_TAC >> ASM_REWRITE_TAC[]) >>
  (* Non-INVOKE OK: step_inst is ctx-independent *)
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[] >>
  (* vs_labels preserved — forward reasoning *)
  mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s`, `v`]
    step_inst_preserves_labels_always) >>
  ASM_REWRITE_TAC[] >> DISCH_TAC >>
  Cases_on `is_terminator inst.inst_opcode` >- (
    qexists_tac `0` >>
    mp_tac (Q.SPECL [`0`, `fuel`, `ctx'`, `ctx`, `inst`, `s`]
      step_inst_cross_ctx) >>
    ASM_REWRITE_TAC[] >>
    DISCH_TAC >> ASM_REWRITE_TAC[] >>
    REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
    ASM_REWRITE_TAC[lift_result_eq_sgnp_refl]) >>
  ASM_REWRITE_TAC[] >>
  qpat_x_assum `!m. m < n ==> _`
    (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- DECIDE_TAC) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `ctx'`, `bb`,
    `v with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  REWRITE_TAC[vs_inst_idx_update, vs_labels_inst_idx_update] >>
  (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    ASM_REWRITE_TAC[])) >>
  strip_tac >>
  qexists_tac `fuel'` >>
  mp_tac (Q.SPECL [`fuel'`, `fuel`, `ctx'`, `ctx`, `inst`, `s`]
    step_inst_cross_ctx) >>
  ASM_REWRITE_TAC[] >>
  DISCH_TAC >> ASM_REWRITE_TAC[] >>
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[]
QED

(* OK case helper for restricted run_function *)
Triviality run_function_cross_ctx_ok_case_restricted:
  !fuel ctx ctx' g s bb v fuel_b.
    run_block fuel ctx bb s = OK v /\
    run_block fuel_b ctx' bb s = OK v /\
    lookup_block s.vs_current_bb g.fn_blocks = SOME bb /\
    FDOM s.vs_labels = {} /\
    (!f h_name h callee_s.
      f < SUC fuel /\
      lookup_function h_name ctx.ctx_functions = SOME h /\
      callee_s.vs_prev_bb = NONE /\
      callee_s.vs_inst_idx = 0 /\
      FDOM callee_s.vs_labels = {} /\
      ~callee_s.vs_halted ==>
      ?h'.
        lookup_function h_name ctx'.ctx_functions = SOME h' /\
        ~NULL h.fn_blocks /\ ~NULL h'.fn_blocks /\
        (HD h.fn_blocks).bb_label = (HD h'.fn_blocks).bb_label /\
        ?fuel_h.
          lift_result (=) shared_globals_np
            (run_function f ctx h callee_s)
            (run_function fuel_h ctx' h' callee_s)) /\
    (!ctx ctx' g s.
      (!f h_name h callee_s.
        f < fuel /\
        lookup_function h_name ctx.ctx_functions = SOME h /\
        callee_s.vs_prev_bb = NONE /\
        callee_s.vs_inst_idx = 0 /\
        FDOM callee_s.vs_labels = {} /\
        ~callee_s.vs_halted ==>
        ?h'.
          lookup_function h_name ctx'.ctx_functions = SOME h' /\
          ~NULL h.fn_blocks /\ ~NULL h'.fn_blocks /\
          (HD h.fn_blocks).bb_label = (HD h'.fn_blocks).bb_label /\
          ?fuel_h.
            lift_result (=) shared_globals_np
              (run_function f ctx h callee_s)
              (run_function fuel_h ctx' h' callee_s)) /\
      FDOM s.vs_labels = {} ==>
      ?fuel'.
        lift_result (=) shared_globals_np
          (run_function fuel ctx g s)
          (run_function fuel' ctx' g s)) ==>
    ?fuel'.
      lift_result (=) shared_globals_np
        (run_function (SUC fuel) ctx g s)
        (run_function fuel' ctx' g s)
Proof
  rpt strip_tac >>
  Cases_on `v.vs_halted`
  >- (
    qexists_tac `SUC fuel_b` >> UNFOLD_RF_SUC_TAC >>
    ASM_REWRITE_TAC[lift_result_def, shared_globals_np_refl])
  >> (
  (* not halted: apply IH — need FDOM v.vs_labels = {} *)
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`, `v`]
    run_block_preserves_labels) >>
  ASM_REWRITE_TAC[] >> DISCH_TAC >>
  first_x_assum (qspecl_then [`ctx`, `ctx'`, `g`, `v`] mp_tac) >>
  (impl_tac >- (
    conj_tac >- (
      rpt strip_tac >>
      first_x_assum (qspecl_then [`f`, `h_name`, `h`, `callee_s`] mp_tac) >>
      simp[]) >>
    ASM_REWRITE_TAC[])) >>
  strip_tac >>
  rename [`lift_result _ _ (run_function fuel ctx g v)
                           (run_function fuel_c ctx' g v)`] >>
  Cases_on `terminates (run_function fuel_c ctx' g v)`
  >- (
    qexists_tac `SUC (MAX fuel_b fuel_c)` >>
    `run_block (MAX fuel_b fuel_c) ctx' bb s = OK v` by (
      `run_block (MAX fuel_b fuel_c) ctx' bb s = run_block fuel_b ctx' bb s`
        suffices_by ASM_REWRITE_TAC[] >>
      irule run_block_fuel_mono_ge >>
      conj_tac >- simp[] >>
      rpt strip_tac >> gvs[]) >>
    `run_function (MAX fuel_b fuel_c) ctx' g v =
     run_function fuel_c ctx' g v` by (
      irule run_function_fuel_mono_ge >> ASM_REWRITE_TAC[] >> simp[]) >>
    UNFOLD_RF_SUC_TAC >> ASM_REWRITE_TAC[])
  >> (
  gvs[terminates_def] >>
  Cases_on `run_function fuel_c ctx' g v` >> gvs[] >>
  qpat_x_assum `lift_result _ _ _ (Error _)` mp_tac >>
  Cases_on `run_function fuel ctx g v` >>
  REWRITE_TAC[lift_result_def] >>
  qexists_tac `0` >>
  ONCE_REWRITE_TAC[run_function_def] >>
  REWRITE_TAC[arithmeticTheory.num_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[] >>
  REWRITE_TAC[optionTheory.option_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[] >>
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[lift_result_def]))
QED

(* Restricted cross-ctx: callee hypothesis only for states satisfying
   init_conds. This is sufficient because callee states come from
   setup_callee which produces init_cond-satisfying states. *)
Triviality run_function_cross_ctx_restricted:
  !fuel ctx ctx' g s.
    (!f h_name h callee_s.
      f < fuel /\
      lookup_function h_name ctx.ctx_functions = SOME h /\
      callee_s.vs_prev_bb = NONE /\
      callee_s.vs_inst_idx = 0 /\
      FDOM callee_s.vs_labels = {} /\
      ~callee_s.vs_halted ==>
      ?h'.
        lookup_function h_name ctx'.ctx_functions = SOME h' /\
        ~NULL h.fn_blocks /\ ~NULL h'.fn_blocks /\
        (HD h.fn_blocks).bb_label = (HD h'.fn_blocks).bb_label /\
        ?fuel_h.
          lift_result (=) shared_globals_np
            (run_function f ctx h callee_s)
            (run_function fuel_h ctx' h' callee_s)) /\
    FDOM s.vs_labels = {} ==>
    ?fuel'.
      lift_result (=) shared_globals_np
        (run_function fuel ctx g s)
        (run_function fuel' ctx' g s)
Proof
  Induct_on `fuel`
  >- (
    rpt strip_tac >> qexists_tac `0` >>
    ONCE_REWRITE_TAC[run_function_def] >> simp[lift_result_def])
  >> (
  rpt strip_tac >>
  Cases_on `lookup_block s.vs_current_bb g.fn_blocks`
  >- (
    qexists_tac `0` >>
    ONCE_REWRITE_TAC[run_function_def] >> simp[lift_result_def])
  >>
  rename [`lookup_block _ _ = SOME bb`] >>
  mp_tac (Q.SPECL [`LENGTH bb.bb_instructions - s.vs_inst_idx`,
                    `fuel`, `ctx`, `ctx'`, `bb`, `s`]
    run_block_cross_ctx_restricted) >>
  (impl_tac >- (
    rpt conj_tac >> TRY REFL_TAC >> TRY (first_assum ACCEPT_TAC) >>
    rpt strip_tac >>
    first_x_assum (qspecl_then [`fuel`, `h_name`, `h`, `callee_s`] mp_tac) >>
    (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])) >>
    metis_tac[])) >>
  strip_tac >>
  rename [`lift_result _ _ (run_block fuel ctx bb s)
                           (run_block fuel_b ctx' bb s)`] >>
  Cases_on `run_block fuel ctx bb s` >>
  Cases_on `run_block fuel_b ctx' bb s` >>
  gvs[lift_result_def]
  (* OK / OK: use helper *)
  >- (mp_tac (Q.SPECL [`fuel`, `ctx`, `ctx'`, `g`, `s`, `bb`, `v`, `fuel_b`]
        run_function_cross_ctx_ok_case_restricted) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      strip_tac >> qexists_tac `fuel'` >> ASM_REWRITE_TAC[])
  (* Halt / Halt *)
  >- (
    qexists_tac `SUC fuel_b` >> UNFOLD_RF_SUC_TAC >>
    REWRITE_TAC[lift_result_def] >> ASM_REWRITE_TAC[])
  (* Abort / Abort *)
  >- (
    qexists_tac `SUC fuel_b` >> UNFOLD_RF_SUC_TAC >>
    REWRITE_TAC[lift_result_def] >> ASM_REWRITE_TAC[])
  (* IntRet / IntRet *)
  >- (
    qexists_tac `SUC fuel_b` >> UNFOLD_RF_SUC_TAC >>
    REWRITE_TAC[lift_result_def] >> ASM_REWRITE_TAC[])
  >>
  (* Error / Error *)
  qexists_tac `0` >>
  ONCE_REWRITE_TAC[run_function_def] >> simp[lift_result_def])
QED

(* Combined: for any function h in ctx, ∃h' in ctx' s.t.
   run_function at any fuel gives equivalent results.
   Strengthened conclusion includes ¬NULL + entry label for IH. *)
Triviality callee_equiv_all_fuel:
  !fuel ctx callee ist ctx' ist' h_name h s.
    inline_candidate ctx callee ist = (ctx', ist') /\
    lookup_function callee.fn_name ctx.ctx_functions = SOME callee /\
    fn_no_invoke callee.fn_name callee /\
    invoke_targets_extern callee /\
    ALL_DISTINCT (fn_labels callee) /\
    labels_no_inline_return callee /\
    fn_no_alloca callee /\
    EVERY bb_well_formed callee.fn_blocks /\
    EVERY (\bb. params_sequential bb.bb_instructions 0) callee.fn_blocks /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions)
      (TL callee.fn_blocks) /\
    fn_has_entry callee /\
    label_ops_closed callee /\
    EVERY (\f. ALL_DISTINCT (fn_labels f)) ctx.ctx_functions /\
    EVERY (\f. labels_fresh_above ist.is_inline_count f) ctx.ctx_functions /\
    EVERY (\f. fn_no_alloca f) ctx.ctx_functions /\
    EVERY (\f. EVERY bb_well_formed f.fn_blocks) ctx.ctx_functions /\
    EVERY (\f. label_ops_closed f) ctx.ctx_functions /\
    EVERY (\f. vars_fresh_above ist.is_inline_count f) ctx.ctx_functions /\
    EVERY (\f. fn_has_entry f) ctx.ctx_functions /\
    EVERY (\f. EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
      bb.bb_instructions) f.fn_blocks) ctx.ctx_functions /\
    EVERY (\f. EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      EVERY (\blk. count_params blk.bb_instructions <=
                   LENGTH (TL inst.inst_operands)) callee.fn_blocks)
      bb.bb_instructions) f.fn_blocks) ctx.ctx_functions /\
    EVERY (\f. EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      ALL_DISTINCT inst.inst_outputs)
      bb.bb_instructions) f.fn_blocks) ctx.ctx_functions /\
    EVERY (\f. EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      EVERY (\op. !v. op = Var v ==> ~MEM v inst.inst_outputs)
        (TL inst.inst_operands))
      bb.bb_instructions) f.fn_blocks) ctx.ctx_functions /\
    lookup_function h_name ctx.ctx_functions = SOME h /\
    s.vs_prev_bb = NONE /\
    s.vs_inst_idx = 0 /\
    FDOM s.vs_labels = {} /\
    ~s.vs_halted ==>
    ?h' fuel'.
      lookup_function h_name ctx'.ctx_functions = SOME h' /\
      ~NULL h.fn_blocks /\ ~NULL h'.fn_blocks /\
      (HD h.fn_blocks).bb_label = (HD h'.fn_blocks).bb_label /\
      lift_result (=) shared_globals_np
        (run_function fuel ctx h s)
        (run_function fuel' ctx' h' s)
Proof
  completeInduct_on `fuel` >>
  rpt gen_tac >> strip_tac >>
  (* Get g' from fn_correspondence (specialize with h to discharge) *)
  mp_tac (Q.SPECL [`ctx`, `callee`, `ist`, `ctx'`, `ist'`,
    `h_name`, `h`] inline_candidate_fn_correspondence) >>
  ASM_REWRITE_TAC[] >>
  DISCH_THEN (CHOOSE_THEN ASSUME_TAC) >>
  (* Now: lookup_function h_name ctx'.ctx_functions = SOME g' *)
  qexists_tac `g'` >>
  (* Hide lookup g' IMMEDIATELY to prevent gvs/ASM_REWRITE hangs (LEARNINGS #15) *)
  qpat_x_assum `lookup_function h_name ctx'.ctx_functions = SOME g'`
    (fn th => ASSUME_TAC (ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def] th)) >>
  (* Project all EVERY conditions to h, beta-reduce (λf. ...) h → ... h.fn_blocks *)
  imp_res_tac every_lookup >> RULE_ASSUM_TAC BETA_RULE >>
  (`~NULL h.fn_blocks` by
    gvs[fn_has_entry_def, NULL_EQ]) >>
  ASM_REWRITE_TAC[] >>
  (* Derive ~NULL g'.fn_blocks and entry label (needs lookup g' + ~NULL h) *)
  (* Temporarily restore lookup g' for entry_label_preserved *)
  qpat_x_assum `Abbrev (lookup_function _ _ = _)`
    (ASSUME_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  mp_tac (Q.SPECL [`ctx`, `callee`, `ist`, `ctx'`, `ist'`,
    `h_name`, `h`, `g'`] inline_candidate_entry_label_preserved) >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  (* Re-hide lookup g' *)
  qpat_x_assum `lookup_function h_name ctx'.ctx_functions = SOME g'`
    (fn th => ASSUME_TAC (ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def] th)) >>
  ASM_REWRITE_TAC[] >>
  (* Step (a): Cross-ctx: run fuel ctx h s ≈(=,sgnp) run F1 ctx' h s *)
  mp_tac (Q.SPECL [`fuel`, `ctx`, `ctx'`, `h`, `s`]
    run_function_cross_ctx_restricted) >>
  (impl_tac >- (
    conj_tac >- (
      (* callee hypothesis: use IH at lower fuel *)
      rpt strip_tac >>
      first_x_assum (qspec_then `f` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      (* IH: ∀ctx callee ... — match all preconditions *)
      disch_then (qspecl_then [`ctx`, `callee`, `ist`, `ctx'`, `ist'`] mp_tac) >>
      rename [`lookup_function callee_nm _ = SOME callee_fn`,
              `callee_fn_s.vs_prev_bb = NONE`] >>
      disch_then (qspecl_then [`callee_nm`, `callee_fn`, `callee_fn_s`] mp_tac) >>
      (impl_tac >- (rpt conj_tac >> TRY REFL_TAC >>
                     first_assum ACCEPT_TAC)) >>
      strip_tac >>
      rename [`lookup_function _ ctx'.ctx_functions = SOME h_c'`] >>
      qexists_tac `h_c'` >> ASM_REWRITE_TAC[] >>
      rename [`lift_result _ _ _ (run_function fuel_c _ _ _)`] >>
      qexists_tac `fuel_c` >> ASM_REWRITE_TAC[]) >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >>
  (* Step (b): Per-fn: run F1 ctx' h s ≈(se_iv,sgnp) run F2 ctx' g' s
     Use inline_at_sites_fn_correct with ctx' as context *)
  (* Get inline_at_sites relationship from FOLDL *)
  (* lookup g' is already hidden as Abbrev from line 1695 *)
  mp_tac (Q.SPECL [`ctx.ctx_functions`, `[]:ir_function list`, `ist`,
    `ctx'.ctx_functions`, `ist'`, `h_name`, `h`]
    foldl_inline_find_entry) >>
  (impl_tac >- (
    gvs[inline_candidate_def, LET_THM, lookup_function_def] >>
    pairarg_tac >> gvs[listTheory.FIND_thm])) >>
  strip_tac >>
  rename [`inline_at_sites _ h callee ist_i = (h_inl, ist_i')`] >>
  (* Restore the lookup g' fact *)
  qpat_x_assum `Abbrev (lookup_function _ _ = _)`
    (ASSUME_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  (* h_inl = g' (both are FIND result for h_name in ctx'.ctx_functions) *)
  qpat_x_assum `FIND _ ctx'.ctx_functions = SOME h_inl`
    (fn find_th => qpat_x_assum `lookup_function h_name ctx'.ctx_functions = SOME g'`
      (fn lookup_th =>
        let val eq = TRANS (SYM find_th)
              (PURE_REWRITE_RULE [lookup_function_def] lookup_th)
            val eq2 = REWRITE_RULE [optionTheory.SOME_11] eq
        in SUBST_ALL_TAC eq2 end)) >>
  (* Now h_inl is replaced by g' everywhere *)
  (* Get callee in ctx' *)
  mp_tac (Q.SPECL [`ctx`, `callee`, `ist`, `ctx'`, `ist'`]
    inline_candidate_callee_unchanged) >>
  ASM_REWRITE_TAC[] >> DISCH_TAC >>
  (* Apply inline_at_sites_fn_correct with ctx' *)
  mp_tac (Q.SPECL [`LENGTH (fn_insts h)`, `h`, `callee`, `ist_i`,
    `g'`, `ist_i'`, `fuel'`, `ctx'`, `s`]
    inline_at_sites_fn_correct) >>
  (impl_tac >- (
    ASM_REWRITE_TAC[] >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    (* fresh_above via monotonicity *)
    TRY (irule labels_fresh_above_mono >>
         qexists_tac `ist.is_inline_count` >>
         conj_tac >- (imp_res_tac lookup_function_MEM >>
           qpat_x_assum `EVERY (\f. labels_fresh_above _ _) _` mp_tac >>
           simp[EVERY_MEM]) >>
         first_assum ACCEPT_TAC) >>
    TRY (irule vars_fresh_above_mono >>
         qexists_tac `ist.is_inline_count` >>
         conj_tac >- (imp_res_tac lookup_function_MEM >>
           qpat_x_assum `EVERY (\f. vars_fresh_above _ _) _` mp_tac >>
           simp[EVERY_MEM]) >>
         first_assum ACCEPT_TAC) >>
    (* EVERY conditions from ctx EVERY projected to h *)
    imp_res_tac lookup_function_MEM >>
    TRY (qpat_x_assum `EVERY (\f. ALL_DISTINCT _) _` mp_tac >>
         simp[EVERY_MEM] >> NO_TAC) >>
    TRY (qpat_x_assum `EVERY (\f. fn_no_alloca _) _` mp_tac >>
         simp[EVERY_MEM] >> NO_TAC) >>
    TRY (qpat_x_assum `EVERY (\f. EVERY bb_well_formed _) _` mp_tac >>
         simp[EVERY_MEM] >> NO_TAC) >>
    TRY (qpat_x_assum `EVERY (\f. label_ops_closed _) _` mp_tac >>
         simp[EVERY_MEM] >> NO_TAC) >>
    (* inst_targets EVERY conditions: now beta-reduced by RULE_ASSUM_TAC *)
    first_assum ACCEPT_TAC)) >>
  strip_tac >>
  (* Compose: cross-ctx gives (=,sgnp), per-fn gives (se_iv,sgnp)
     Change per-fn R_ok from se_iv to (=) via lift_result_change_ok
     (run_function never returns OK), then compose via lift_result_trans *)
  (* Step 1: change R_ok from se_iv to = *)
  mp_tac (Q.SPECL [`state_equiv inline_vars`, `$=`,
    `shared_globals_np`,
    `run_function fuel' ctx' h s`,
    `run_function fuel'' ctx' g' s`] lift_result_change_ok) >>
  (impl_tac >- metis_tac[run_function_not_ok]) >>
  disch_then (fn imp => first_assum (ASSUME_TAC o MATCH_MP imp)) >>
  (* Step 2: compose via transitivity *)
  mp_tac (Q.SPECL [`$=`, `shared_globals_np`,
    `run_function fuel ctx h s`,
    `run_function fuel' ctx' h s`,
    `run_function fuel'' ctx' g' s`] lift_result_trans) >>
  (impl_tac >- simp[]) >>
  (impl_tac >- ACCEPT_TAC shared_globals_np_trans) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  DISCH_TAC >>
  qexists_tac `fuel''` >> ASM_REWRITE_TAC[]
QED

Triviality inline_candidate_preserves_ctx_entry:
  !ctx callee ist ctx' ist'.
    inline_candidate ctx callee ist = (ctx', ist') ==>
    ctx'.ctx_entry = ctx.ctx_entry
Proof
  rpt strip_tac >>
  qpat_x_assum `_ = _` mp_tac >>
  PURE_REWRITE_TAC[inline_candidate_def, LET_THM] >> BETA_TAC >>
  pairarg_tac >> strip_tac >> gvs[]
QED

Theorem inline_candidate_correct:
  !ctx callee ist ctx' ist' fuel s.
    inline_candidate ctx callee ist = (ctx', ist') /\
    lookup_function callee.fn_name ctx.ctx_functions = SOME callee /\
    fn_no_invoke callee.fn_name callee /\
    invoke_targets_extern callee /\
    ALL_DISTINCT (fn_labels callee) /\
    labels_no_inline_return callee /\
    fn_no_alloca callee /\
    EVERY bb_well_formed callee.fn_blocks /\
    EVERY (\bb. params_sequential bb.bb_instructions 0) callee.fn_blocks /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions)
      (TL callee.fn_blocks) /\
    fn_has_entry callee /\
    label_ops_closed callee /\
    FDOM s.vs_labels = {} /\
    ~s.vs_halted /\
    EVERY (\f. ALL_DISTINCT (fn_labels f)) ctx.ctx_functions /\
    EVERY (\f. labels_fresh_above ist.is_inline_count f) ctx.ctx_functions /\
    EVERY (\f. fn_no_alloca f) ctx.ctx_functions /\
    EVERY (\f. EVERY bb_well_formed f.fn_blocks) ctx.ctx_functions /\
    EVERY (\f. label_ops_closed f) ctx.ctx_functions /\
    EVERY (\f. vars_fresh_above ist.is_inline_count f) ctx.ctx_functions /\
    EVERY (\f. fn_has_entry f) ctx.ctx_functions /\
    EVERY (\f. EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
      bb.bb_instructions) f.fn_blocks) ctx.ctx_functions /\
    EVERY (\f. EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      EVERY (\blk. count_params blk.bb_instructions <=
                   LENGTH (TL inst.inst_operands)) callee.fn_blocks)
      bb.bb_instructions) f.fn_blocks) ctx.ctx_functions /\
    EVERY (\f. EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      ALL_DISTINCT inst.inst_outputs)
      bb.bb_instructions) f.fn_blocks) ctx.ctx_functions /\
    EVERY (\f. EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      EVERY (\op. !v. op = Var v ==> ~MEM v inst.inst_outputs)
        (TL inst.inst_operands))
      bb.bb_instructions) f.fn_blocks) ctx.ctx_functions ==>
    ?fuel'.
      lift_result (state_equiv inline_vars) shared_globals_np
        (run_context fuel ctx s)
        (run_context fuel' ctx' s)
Proof
  rpt gen_tac >> strip_tac >>
  ONCE_REWRITE_TAC[run_context_def] >>
  mp_tac inline_candidate_preserves_ctx_entry >>
  disch_then drule >> DISCH_TAC >>
  qpat_x_assum `ctx'.ctx_entry = ctx.ctx_entry` SUBST_ALL_TAC >>
  Cases_on `ctx.ctx_entry`
  >- (qexists_tac `0` >> simp[lift_result_def])
  >>
  simp[] >>
  Cases_on `lookup_function x ctx.ctx_functions`
  >- (qexists_tac `0` >>
      Cases_on `lookup_function x ctx'.ctx_functions` >> simp[lift_result_def] >>
      Cases_on `entry_block x'` >> simp[lift_result_def] >>
      ONCE_REWRITE_TAC[run_function_def] >> simp[lift_result_def])
  >>
  simp[] >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `callee`, `ist`, `ctx'`, `ist'`,
    `x`, `x'`,
    `s with <| vs_current_bb := (HD x'.fn_blocks).bb_label;
               vs_inst_idx := 0; vs_prev_bb := NONE |>`]
    callee_equiv_all_fuel) >>
  (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY (simp [])))
  >>
  strip_tac >>
  imp_res_tac every_lookup >> RULE_ASSUM_TAC BETA_RULE >>
  (`entry_block x' = SOME (HD x'.fn_blocks)` by (
    simp[entry_block_def] >>
    `~NULL x'.fn_blocks` by gvs[fn_has_entry_def, NULL_EQ] >>
    Cases_on `x'.fn_blocks` >> gvs[])) >>
  ASM_REWRITE_TAC[] >>
  (`entry_block h' = SOME (HD h'.fn_blocks)` by (
    simp[entry_block_def] >>
    Cases_on `h'.fn_blocks` >> gvs[])) >>
  ASM_REWRITE_TAC[] >>
  qexists_tac `fuel'` >>
  simp[] >>
  qpat_x_assum `(HD x'.fn_blocks).bb_label = _` (SUBST_ALL_TAC) >>
  irule lift_result_weaken_ok >>
  conj_tac >- simp[state_equiv_refl] >>
  qpat_x_assum `lift_result _ _ (run_function _ _ x' _)
                                (run_function _ _ h' _)` mp_tac >>
  simp[]
QED

val _ = export_theory();
