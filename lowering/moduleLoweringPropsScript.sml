(*
 * Module Lowering Properties
 *
 * TOP-LEVEL:
 *   compile_selector_dispatch_linear_correct — linear dispatch: partial CFG
 *   compile_selector_dispatch_sparse_correct — sparse dispatch: partial CFG
 *   compile_entry_point_kwargs_correct — kwargs init + JMP: partial CFG
 *   compile_entry_checks_correct — nonpayable/calldatasize checks (single-block)
 *   compile_entry_checks_nonpayable_revert — nonpayable revert (derived)
 *   compile_constructor_epilogue_correct — runtime code copy + RETURN (single-block)
 *   compile_generate_runtime_correct — top-level module correctness (stitching)
 *
 * Definitions:
 *   runtime_input_labels — labels the caller must supply as external
 *   runtime_inputs_ok — well-formed runtime compilation inputs
 *   dispatch_labels_covered — selector labels ⊆ external fn entry labels
 *
 * Helper (no standalone correctness — always composed):
 *   compile_decode_args_nil   — empty arg list is no-op
 *   compile_init_kwargs_nil   — empty kwargs list is no-op
 *
 * Source: module.py (VenomModuleCompiler)
 * Lowering: moduleLoweringScript.sml
 *
 * NOTE on execution models:
 *   - Selector dispatch and entry_point_kwargs create partial CFGs that
 *     jump to external labels (fn bodies, fallback, common body).
 *     These use run_compiled_fragment which treats exit to a non-assembled
 *     label as OK (returning the state at the exit point).
 *   - Entry checks and constructor epilogue stay within a single block,
 *     so they use the simpler run_inst_seq/emitted_insts pattern.
 *   - compile_decode_args and compile_init_kwargs are fragments (no terminator)
 *     always composed within a larger compilation. No standalone theorem;
 *     correctness is proved at the wrapper level (entry_point_kwargs for
 *     kwargs, compile_external_function_body for positional args).
 *)

Theory moduleLoweringProps
Ancestors
  stmtLoweringProps
  emitHelperProps
  exprLoweringProps
  moduleLowering compileEnv context
  venomExecSemantics venomState venomInst
  abiEncoder
Libs
  wordsLib

(* ===== Fragment Execution Model ===== *)

(* Like run_blocks, but treats "block not found" as successful exit
   to an external label. Returns OK ss where ss.vs_current_bb is
   the external label reached. *)
Definition run_fragment_blocks_def:
  run_fragment_blocks 0 ctx fn ss = Error "out of fuel" ∧
  run_fragment_blocks (SUC fuel) ctx fn ss =
    case lookup_block ss.vs_current_bb fn.fn_blocks of
      NONE => OK ss
    | SOME bb =>
        case exec_block fuel ctx bb (ss with vs_inst_idx := 0) of
          OK ss' =>
            if ss'.vs_halted then Halt ss'
            else run_fragment_blocks fuel ctx fn ss'
        | IntRet vals ss' => IntRet vals ss'
        | Halt ss' => Halt ss'
        | Abort a ss' => Abort a ss'
        | Error e => Error e
End

(* Run a compiled fragment (partial CFG). Like run_compiled_blocks but
   uses run_fragment_blocks: exits with OK when execution reaches a
   label not in the assembled blocks. *)
Definition run_compiled_fragment_def:
  run_compiled_fragment ctx st st' ss fuel =
    let fn = assemble_function st st' in
    let entry_lbl = st.cs_current_bb in
    let entry_idx = LENGTH st.cs_current_insts in
    case lookup_block entry_lbl fn.fn_blocks of
      NONE => Error "entry block not found"
    | SOME bb =>
        case exec_block fuel ctx bb
               (ss with <| vs_current_bb := entry_lbl;
                            vs_inst_idx := entry_idx |>) of
          OK ss' =>
            if ss'.vs_halted then Halt ss'
            else run_fragment_blocks fuel ctx fn ss'
        | IntRet vals ss' => IntRet vals ss'
        | Halt ss' => Halt ss'
        | Abort a ss' => Abort a ss'
        | Error e => Error e
End

(* ===== Selector Dispatch ===== *)

(* Linear dispatch creates blocks that jump to fallback_lbl or fn_labels
   from the selector list. These are external labels (fn bodies, fallback
   handler) assembled separately. The fragment exits to one of them.

   HYPOTHESES (added 2026-04-17 after counterexample):
   - compile_state_ok st: pre-state has well-formed label bindings
   - label_external st fallback_lbl: fallback label is not already bound
     in st and wasn't allocated by a future fresh_label (so
     compile_selector_dispatch_linear cannot reuse it for an internal
     @dispatch_/@match_/@next_ label)
   - EVERY (label_external st) (MAP SND selectors): same for per-fn labels
   - ALL_DISTINCT (fallback_lbl :: MAP SND selectors): no two external
     labels collide (so JNZ to one doesn't accidentally equal another) *)
Theorem compile_selector_dispatch_linear_correct:
  ∀ selectors fallback_lbl ss st st' ctx.
    compile_selector_dispatch_linear selectors fallback_lbl st = ((), st') ∧
    compile_state_ok st ∧
    label_external st fallback_lbl ∧
    EVERY (label_external st) (MAP SND selectors) ∧
    ALL_DISTINCT (fallback_lbl :: MAP SND selectors) ∧
    fresh_vars_wrt st ss ∧
    ¬ss.vs_halted
    ⇒
    ∃ fuel ss'.
      run_compiled_fragment ctx st st' ss fuel = OK ss' ∧
      (ss'.vs_current_bb = fallback_lbl ∨
       MEM ss'.vs_current_bb (MAP SND selectors))
Proof
  (* Original proof attempt (pre-hypothesis-fix). Preserved for reference;
     the chain through emit_op_*_correct + exec_block_inst_seq_jnz is the
     intended shape after the new hypotheses discharge the label-collision
     case in run_fragment_blocks.

  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_selector_dispatch_linear _ _ _ = _` mp_tac >>
  simp[compile_selector_dispatch_linear_def, comp_ignore_bind_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >>
  strip_tac >>
  drule_all emit_op_CALLDATASIZE_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st cs') ss = OK ss1` >>
  drule_at (Pos last) emit_op_LT_correct >>
  disch_then drule >> disch_then drule >>
  disch_then (qspec_then `4w` mp_tac) >>
  simp[eval_operand_lit] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs' cs'') ss1 = OK ss2` >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_inst >>
  imp_res_tac fresh_label_props >>
  drule_at (Pos last) emit_op_ISZERO_correct >>
  disch_then drule >> disch_then drule >> strip_tac >>
  ... (Step 3: exec_block_inst_seq_jnz, case split on JNZ cond,
       induction on selectors for dispatch branch) ...
  *)
  cheat
QED

(* Sparse dispatch: like linear dispatch but uses bucket-based matching
   with selectors that carry a trailing-zeroes flag. Exits to
   fallback_lbl or one of the per-fn labels in selectors.
   Same label-space hypotheses as linear dispatch. *)
Theorem compile_selector_dispatch_sparse_correct:
  ∀ selectors bucket_count fallback_lbl ss st st' ctx.
    compile_selector_dispatch_sparse selectors bucket_count fallback_lbl st =
      ((), st') ∧
    compile_state_ok st ∧
    label_external st fallback_lbl ∧
    EVERY (label_external st) (MAP (FST o SND) selectors) ∧
    ALL_DISTINCT (fallback_lbl :: MAP (FST o SND) selectors) ∧
    fresh_vars_wrt st ss ∧
    ¬ss.vs_halted
    ⇒
    ∃ fuel ss'.
      run_compiled_fragment ctx st st' ss fuel = OK ss' ∧
      (ss'.vs_current_bb = fallback_lbl ∨
       MEM ss'.vs_current_bb (MAP (FST o SND) selectors))
Proof
  cheat
QED

(* ===== Kwargs Entry Point ===== *)

(* compile_entry_point_kwargs: inits kwargs + JMP to common_label.
   Replaces standalone compile_init_kwargs_correct — init_kwargs is a
   fragment (no terminator) always composed within entry_point_kwargs
   or similar wrapper.

   Label-space hypothesis: common_label is external to st (not yet bound
   and outside the future fresh_label co-domain). *)
Theorem compile_entry_point_kwargs_correct:
  ∀ cenv kwarg_vars calldata_offset kwargs_from_calldata common_label
    ss st st' ctx.
    compile_entry_point_kwargs cenv kwarg_vars calldata_offset
                               kwargs_from_calldata common_label st = ((), st') ∧
    compile_state_ok st ∧
    label_external st common_label ∧
    fresh_vars_wrt st ss ∧
    ¬ss.vs_halted
    ⇒
    ∃ fuel.
      (∃ ss'. run_compiled_fragment ctx st st' ss fuel = OK ss' ∧
              ss'.vs_current_bb = common_label) ∨
      (∃ ss'. run_compiled_fragment ctx st st' ss fuel =
                Abort Revert_abort ss')
Proof
  cheat
QED

(* Needed for Holmake: mark incomplete theorems *)
val _ = Feedback.set_trace "Theory.allow_rebinds" 1;

(* ===== Argument Decoding (helpers only) ===== *)

Theorem compile_decode_args_nil:
  ∀ cenv offset load_opc hi_op base_adj st.
    compile_decode_args cenv [] offset load_opc hi_op base_adj st = ((), st)
Proof
  simp[compile_decode_args_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

Theorem compile_init_kwargs_nil:
  ∀ cenv offset from_cd hi_op st.
    compile_init_kwargs cenv [] offset from_cd hi_op st = ((), st)
Proof
  simp[compile_init_kwargs_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

(* ===== Entry Checks ===== *)

(* Helper: the calldatasize sub-check (4 instructions: CDS, LT, ISZERO, ASSERT)
   Either succeeds (OK) or reverts. Used in both entry_checks_correct cases. *)
Theorem compile_cds_check_ok_or_revert:
  ∀ min_cds st0 st1 st2 st3 st4 cds_v lt_v ok_v ss0.
    emit_op CALLDATASIZE [] st0 = (cds_v, st1) ∧
    emit_op LT [cds_v; Lit (n2w min_cds)] st1 = (lt_v, st2) ∧
    emit_op ISZERO [lt_v] st2 = (ok_v, st3) ∧
    emit_void ASSERT [ok_v] st3 = ((), st4) ∧
    fresh_vars_wrt st0 ss0
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st0 st4) ss0 = OK ss') ∨
      (run_inst_seq (emitted_insts st0 st4) ss0 = Abort Revert_abort ss')
Proof
  rpt strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  (* Step 1: CALLDATASIZE → OK ss1 *)
  drule_all emit_op_CALLDATASIZE_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st0 st1) ss0 = OK ss1` >>
  (* Step 2: LT → OK ss2 *)
  drule emit_op_LT_correct >> disch_then drule >>
  disch_then (qspec_then `n2w min_cds` mp_tac) >>
  (impl_tac >- gvs[eval_operand_lit]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st1 st2) ss1 = OK ss2` >>
  (* Extend: st0→st2 *)
  `run_inst_seq (emitted_insts st0 st2) ss0 = OK ss2`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  (* Step 3: ISZERO → OK ss3 *)
  drule emit_op_ISZERO_correct >> disch_then drule >>
  (impl_tac >- gvs[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st2 st3) ss2 = OK ss3` >>
  (* Extend: st0→st3 *)
  `run_inst_seq (emitted_insts st0 st3) ss0 = OK ss3`
    by (`inst_extends st0 st2` by metis_tac[inst_extends_trans] >>
        imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  (* Step 4: ASSERT → OK or Abort *)
  drule emit_void_ASSERT_ok_or_revert >> disch_then drule >>
  (impl_tac >- gvs[]) >> strip_tac >> gvs[]
  (* OK case *)
  >- (`inst_extends st0 st3` by metis_tac[inst_extends_trans] >>
      imp_res_tac run_inst_seq_emit_extend >> gvs[] >> metis_tac[])
  (* Abort case *)
  >> (`inst_extends st0 st3` by metis_tac[inst_extends_trans] >>
      imp_res_tac run_inst_seq_emit_extend >> gvs[])
QED

(* Helper: the payable sub-check (3 instructions: CALLVALUE, ISZERO, ASSERT).
   OK branch: callvalue = 0w, fresh_vars preserved.
   Abort branch: callvalue ≠ 0w. *)
Theorem compile_payable_check_ok_or_revert:
  ∀ st0 st1 st2 st3 cv_v nv_v ss0.
    emit_op CALLVALUE [] st0 = (cv_v, st1) ∧
    emit_op ISZERO [cv_v] st1 = (nv_v, st2) ∧
    emit_void ASSERT [nv_v] st2 = ((), st3) ∧
    fresh_vars_wrt st0 ss0
    ⇒
    (∃ ss'. run_inst_seq (emitted_insts st0 st3) ss0 = OK ss' ∧
     fresh_vars_wrt st3 ss' ∧ same_blocks st0 st3 ∧
     ss0.vs_call_ctx.cc_callvalue = 0w) ∨
    (∃ ss'.
       run_inst_seq (emitted_insts st0 st3) ss0 = Abort Revert_abort ss' ∧
       ss0.vs_call_ctx.cc_callvalue ≠ 0w)
Proof
  rpt strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  (* Step 1: CALLVALUE → OK ss1 *)
  drule_all emit_op_CALLVALUE_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st0 st1) ss0 = OK ss1` >>
  (* Step 2: ISZERO → OK ss2 *)
  drule emit_op_ISZERO_correct >> disch_then drule >>
  (impl_tac >- gvs[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st1 st2) ss1 = OK ss2` >>
  (* Extend: st0→st2 *)
  `run_inst_seq (emitted_insts st0 st2) ss0 = OK ss2`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  (* Step 3: ASSERT → OK or Abort *)
  drule emit_void_ASSERT_ok_or_revert >> disch_then drule >>
  (impl_tac >- gvs[]) >> strip_tac >> gvs[]
  (* OK case: ASSERT succeeds, callvalue = 0w *)
  >- suspend "ok_case"
  (* Abort case: callvalue ≠ 0w *)
  >> suspend "abort_case"
QED

Resume compile_payable_check_ok_or_revert[ok_case]:
  `inst_extends st0 st2` by metis_tac[inst_extends_trans] >>
  imp_res_tac run_inst_seq_emit_extend >> gvs[] >>
  conj_tac >- metis_tac[same_blocks_trans] >>
  Cases_on `ss0.vs_call_ctx.cc_callvalue = 0w` >>
  gvs[bool_to_word_def]
QED

Resume compile_payable_check_ok_or_revert[abort_case]:
  `inst_extends st0 st2` by metis_tac[inst_extends_trans] >>
  imp_res_tac run_inst_seq_emit_extend >> gvs[] >>
  Cases_on `ss0.vs_call_ctx.cc_callvalue = 0w` >>
  gvs[bool_to_word_def]
QED

Finalise compile_payable_check_ok_or_revert

Theorem compile_entry_checks_correct:
  ∀ min_cds is_payable ss st st'.
    compile_entry_checks min_cds is_payable st = ((), st') ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       (is_payable ∨ ss.vs_call_ctx.cc_callvalue = 0w)) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  gvs[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, LET_THM] >>
  Cases_on `is_payable` >> gvs[] >>
  rpt (pairarg_tac >> gvs[])
  >- suspend "payable_case"
  >> suspend "nonpayable_case"
QED

Resume compile_entry_checks_correct[payable_case]:
  gvs[comp_return_def] >>
  Cases_on `min_cds > 4` >> gvs[comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM]
  >- (
    rpt (pairarg_tac >> gvs[]) >>
    drule_all compile_cds_check_ok_or_revert >>
    strip_tac >> metis_tac[]
  ) >>
  qexists `ss` >> DISJ1_TAC >>
  simp[emitted_insts_def, run_inst_seq_def]
QED

Resume compile_entry_checks_correct[nonpayable_case]:
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
      LET_THM, pairTheory.PAIR] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_all compile_payable_check_ok_or_revert >> strip_tac
  >- suspend "nonpayable_ok"
  >> suspend "nonpayable_abort"
QED

(* Payable OK: callvalue = 0w, payable prefix gives OK ss' *)
Resume compile_entry_checks_correct[nonpayable_ok]:
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  qpat_x_assum `emit_op CALLVALUE _ _ = _` kall_tac >>
  qpat_x_assum `emit_op ISZERO _ _ = _` kall_tac >>
  qpat_x_assum `emit_void ASSERT _ _ = _` kall_tac >>
  Cases_on `min_cds > 4` >> gvs[comp_return_def] >>
  gvs[comp_bind_def, comp_ignore_bind_def, LET_THM, pairTheory.PAIR] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_all compile_cds_check_ok_or_revert >> strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  irule run_inst_seq_compose_ok_or_abort >>
  qexistsl [`ss'`, `cs'`] >> gvs[] >>
  metis_tac[inst_extends_trans]
QED

(* Payable Abort: callvalue ≠ 0w *)
Resume compile_entry_checks_correct[nonpayable_abort]:
  qexists `ss'` >> disj2_tac >>
  irule run_inst_seq_abort_extends >>
  qexists `cs'` >> rpt conj_tac
  (* abort assumption *)
  >- first_assum ACCEPT_TAC
  (* inst_extends st cs' from payable emit chain *)
  >- metis_tac[inst_extends_emit_op, inst_extends_emit_void,
               inst_extends_trans]
  (* inst_extends cs' st' from CDS conditional *)
  >> (qpat_x_assum `emit_op CALLVALUE _ _ = _` kall_tac >>
      qpat_x_assum `emit_op ISZERO [cv] _ = _` kall_tac >>
      qpat_x_assum `emit_void ASSERT [no_value] _ = _` kall_tac >>
      Cases_on `min_cds > 4` >> gvs[comp_return_def, inst_extends_refl] >>
      gvs[comp_bind_def, comp_ignore_bind_def, LET_THM, pairTheory.PAIR] >>
      rpt (pairarg_tac >> gvs[]) >>
      imp_res_tac inst_extends_emit_op >>
      imp_res_tac inst_extends_emit_void >>
      metis_tac[inst_extends_trans])
QED

Finalise compile_entry_checks_correct

(* Derive nonpayable revert from the general theorem *)
Theorem compile_entry_checks_nonpayable_revert:
  ∀ min_cds ss st st'.
    compile_entry_checks min_cds F st = ((), st') ∧
    fresh_vars_wrt st ss ∧
    ss.vs_call_ctx.cc_callvalue ≠ 0w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  drule_all compile_entry_checks_correct >> strip_tac >> gvs[]
QED

(* ===== Constructor Epilogue ===== *)

(* Both branches use Label "runtime_begin" via OFFSET, needing vs_labels.
   The immutables_len > 0 branch also uses immutables_buf in MCOPY.
   fresh_vars_wrt only constrains vs_vars, not vs_labels. *)
Theorem compile_constructor_epilogue_correct:
  ∀ runtime_size immutables_len immutables_buf ss st st'.
    compile_constructor_epilogue runtime_size immutables_len immutables_buf st =
      ((), st') ∧
    fresh_vars_wrt st ss ∧
    (∃ v. FLOOKUP ss.vs_labels "runtime_begin" = SOME v) ∧
    (immutables_len > 0 ⇒ ∃ v. eval_operand immutables_buf ss = SOME v)
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = Halt ss'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_constructor_epilogue _ _ _ _ = _` mp_tac >>
  simp[compile_constructor_epilogue_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, LET_THM] >>
  Cases_on `immutables_len > 0` >> gvs[]
  (* immutables_len > 0 branch *)
  >- suspend "imm_pos"
  (* immutables_len = 0 branch *)
  >> suspend "imm_zero"
QED

Resume compile_constructor_epilogue_correct[imm_pos]:
  strip_tac >> gvs[comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  (* Step 1: ALLOCA *)
  drule_all emit_op_ALLOCA_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st cs1) ss = OK ss1` >>
  (* Step 2: ADD — deploy_buf evaluable in ss1, Lit always evaluable *)
  drule emit_op_ADD_correct >>
  disch_then drule >>
  disch_then (qspec_then `n2w runtime_size` mp_tac) >>
  (impl_tac >- gvs[eval_operand_lit]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs1 cs2) ss1 = OK ss2` >>
  (* Step 3: MCOPY — imm_dst from ADD, immutables_buf from hypothesis (preserved), Lit *)
  drule emit_void_MCOPY_correct >>
  disch_then drule >>
  disch_then (qspecl_then [`v'`, `n2w immutables_len`] mp_tac) >>
  (impl_tac >- gvs[eval_operand_lit]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs2 cs3) ss2 = OK ss3` >>
  (* Step 4: OFFSET — Lit 0w always evaluable, Label "runtime_begin" preserved *)
  `eval_operand (Label "runtime_begin") ss3 = SOME v`
    by (gvs[eval_operand_def] >>
        `FLOOKUP ss1.vs_labels "runtime_begin" = SOME v`
          by gvs[] >>
        `FLOOKUP ss2.vs_labels "runtime_begin" = SOME v`
          by (Cases_on `Label "runtime_begin"` >>
              gvs[eval_operand_def] >>
              first_x_assum (qspecl_then [`Label "runtime_begin"`, `v`] mp_tac) >>
              simp[eval_operand_def]) >>
        gvs[mcopy_def, write_memory_with_expansion_def, LET_THM]) >>
  `eval_operand (Lit 0w) ss3 = SOME 0w` by simp[eval_operand_def] >>
  drule_all emit_op_OFFSET_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs3 cs4) ss3 = OK ss4` >>
  (* Step 5: CODECOPY — deploy_buf preserved, rt_begin from OFFSET, Lit *)
  `eval_operand deploy_buf ss4 = SOME (n2w offset)` by metis_tac[] >>
  `eval_operand rt_begin ss4 = SOME (0w + v)` by first_assum ACCEPT_TAC >>
  `eval_operand (Lit (n2w runtime_size)) ss4 = SOME (n2w runtime_size)`
    by simp[eval_operand_def] >>
  drule_all emit_void_CODECOPY_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs4 cs5) ss4 = OK ss5` >>
  (* Step 6: RETURN → Halt *)
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  imp_res_tac inst_extends_emit_inst >>
  (* Compose all OK segments: st→cs1→cs2→cs3→cs4→cs5 *)
  `run_inst_seq (emitted_insts st cs2) ss = OK ss2`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  `inst_extends st cs2` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st cs3) ss = OK ss3`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  `inst_extends st cs3` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st cs4) ss = OK ss4`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  `inst_extends st cs4` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st cs5) ss = OK ss5`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  `inst_extends st cs5` by metis_tac[inst_extends_trans] >>
  (* Final: RETURN → Halt *)
  `eval_operand deploy_buf ss5 = SOME (n2w offset)` by metis_tac[] >>
  `eval_operand (Lit (n2w (immutables_len + runtime_size))) ss5 =
     SOME (n2w (immutables_len + runtime_size))`
    by simp[eval_operand_def] >>
  drule_all emit_inst_RETURN_halt >> strip_tac >>
  `inst_extends cs5 st'` by metis_tac[inst_extends_emit_inst] >>
  drule_all run_inst_seq_emit_extend >> gvs[]
QED

Resume compile_constructor_epilogue_correct[imm_zero]:
  strip_tac >>
  gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  (* Step 1: ALLOCA *)
  drule_all emit_op_ALLOCA_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st cs1) ss = OK ss1` >>
  (* Step 2: OFFSET — Label "runtime_begin" evaluable in ss1 *)
  `eval_operand (Label "runtime_begin") ss1 = SOME v`
    by (gvs[eval_operand_def]) >>
  `eval_operand (Lit 0w) ss1 = SOME 0w` by simp[eval_operand_def] >>
  drule_all emit_op_OFFSET_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs1 cs2) ss1 = OK ss2` >>
  (* Step 3: CODECOPY *)
  `eval_operand op ss2 = SOME (n2w offset)` by metis_tac[] >>
  `eval_operand rt_begin ss2 = SOME (0w + v)` by first_assum ACCEPT_TAC >>
  `eval_operand (Lit (n2w runtime_size)) ss2 = SOME (n2w runtime_size)`
    by simp[eval_operand_def] >>
  drule_all emit_void_CODECOPY_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs2 cs3) ss2 = OK ss3` >>
  (* Step 4: RETURN → Halt *)
  `eval_operand op ss3 = SOME (n2w offset)` by metis_tac[] >>
  `eval_operand (Lit (n2w runtime_size)) ss3 = SOME (n2w runtime_size)`
    by simp[eval_operand_def] >>
  drule_all emit_inst_RETURN_halt >> strip_tac >>
  (* Compose *)
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  imp_res_tac inst_extends_emit_inst >>
  `run_inst_seq (emitted_insts st cs2) ss = OK ss2`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  `inst_extends st cs2` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st cs3) ss = OK ss3`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  `inst_extends st cs3` by metis_tac[inst_extends_trans] >>
  `inst_extends cs3 st'` by metis_tac[inst_extends_emit_inst] >>
  drule_all run_inst_seq_emit_extend >> gvs[]
QED

Finalise compile_constructor_epilogue_correct

Theorem run_inst_seq_ok_not_halted:
  ∀ is ss ss'.
    run_inst_seq is ss = OK ss' ∧
    (∀i ss1 ss2. MEM i is ∧ step_inst_base i ss1 = OK ss2 ⇒ (ss2.vs_halted ⇔ ss1.vs_halted)) ∧
    ¬ss.vs_halted
    ⇒
    ¬ss'.vs_halted
Proof
  rpt strip_tac >>
  drule_at (Pos hd) (Q.ISPEC `\s. s.vs_halted` run_inst_seq_preserves_field) >>
  (impl_tac >- (rpt strip_tac >> res_tac >> fs[])) >>
  simp[]
QED

(* ===== Top-Level Module Correctness ===== *)

(* Labels the caller must supply as external: selector fn targets,
   external entry labels, internal fn labels. These must be pairwise
   distinct and external to st (not already bound, not in future
   fresh_label co-domain). In practice the frontend allocates these
   via fresh_label before calling compile_generate_runtime, and
   cs_next_label is advanced past all of them. *)
Definition runtime_input_labels_def:
  runtime_input_labels selectors external_fns internal_fns =
    MAP (λ(sel,lbl,has_tz). lbl) selectors ++
    MAP (λ(entry_lbl, cenv, pos_args, min_cds, is_payable,
            is_nr, nkey, use_trans, is_view, body, ret_type).
           entry_lbl) external_fns ++
    MAP (λ(fn_lbl, cenv, params, has_ret_buf, is_nr, nkey, use_trans,
            is_view, is_ctor, imm_len, body, ret_type).
           fn_lbl) internal_fns
End

(* Selector-declared function labels must match up with external_fn
   entry labels so that a JMP from dispatch lands on an emitted block. *)
Definition dispatch_labels_covered_def:
  dispatch_labels_covered selectors external_fns ⇔
    set (MAP (λ(sel,lbl,_). lbl) selectors) ⊆
      set (MAP (λ(entry_lbl,_,_,_,_,_,_,_,_,_,_). entry_lbl) external_fns)
End

Definition runtime_inputs_ok_def:
  runtime_inputs_ok selectors external_fns internal_fns st ⇔
    compile_state_ok st ∧
    EVERY (label_external st)
          (runtime_input_labels selectors external_fns internal_fns) ∧
    ALL_DISTINCT (runtime_input_labels selectors external_fns internal_fns) ∧
    dispatch_labels_covered selectors external_fns
End

(* Top-level correctness of compile_generate_runtime.
   Under well-formed inputs (frontend-allocated labels are fresh wrt st,
   pairwise distinct, selector labels match external_fn labels), the
   assembled runtime function executes to one of:
   - Halt ss'              (normal RETURN/STOP from a function body)
   - Abort Revert_abort    (entry-check failure or explicit REVERT)
   - IntRet vals ss'       (unusual: an internal function returned to
                             top level; shouldn't happen for well-typed
                             modules, but is a legal exec_result shape
                             given the semantics we have)

   Explicitly excludes Error "out of fuel" (we quantify ∃fuel).

   NOTE: This is the module-level stitching theorem. It consumes the
   three fragment-level correctness theorems for dispatch/kwargs plus
   correctness theorems for external/internal function bodies (stated
   separately; several are still cheated upstream). *)
Theorem compile_generate_runtime_correct:
  ∀ selectors external_fns internal_fns fallback_fn dispatch_strategy
    bucket_count fn_metadata_bytes dense_buckets entry_info
    st st' ss ctx.
    compile_generate_runtime selectors external_fns internal_fns
        fallback_fn dispatch_strategy bucket_count fn_metadata_bytes
        dense_buckets entry_info st = ((), st') ∧
    runtime_inputs_ok selectors external_fns internal_fns st ∧
    fresh_vars_wrt st ss ∧
    ¬ss.vs_halted
    ⇒
    ∃ fuel result.
      run_blocks fuel ctx (assemble_function st st')
        (ss with <| vs_current_bb := st.cs_current_bb;
                     vs_inst_idx := LENGTH st.cs_current_insts |>) = result ∧
      ((∃ ss'. result = Halt ss') ∨
       (∃ ss'. result = Abort Revert_abort ss') ∨
       (∃ vals ss'. result = IntRet vals ss'))
Proof
  cheat
QED
