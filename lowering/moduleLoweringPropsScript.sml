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
   handler) assembled separately. The fragment exits to one of them. *)
Theorem compile_selector_dispatch_linear_correct:
  ∀ selectors fallback_lbl ss st st' ctx.
    compile_selector_dispatch_linear selectors fallback_lbl st = ((), st') ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ fuel ss'.
      run_compiled_fragment ctx st st' ss fuel = OK ss' ∧
      (ss'.vs_current_bb = fallback_lbl ∨
       MEM ss'.vs_current_bb (MAP SND selectors))
Proof
  cheat
QED

(* Sparse dispatch: same pattern, selectors have trailing-zeroes flag. *)
Theorem compile_selector_dispatch_sparse_correct:
  ∀ selectors bucket_count fallback_lbl ss st st' ctx.
    compile_selector_dispatch_sparse selectors bucket_count fallback_lbl st =
      ((), st') ∧
    fresh_vars_wrt st ss
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
   or similar wrapper. *)
Theorem compile_entry_point_kwargs_correct:
  ∀ cenv kwarg_vars calldata_offset kwargs_from_calldata common_label
    ss st st' ctx.
    compile_entry_point_kwargs cenv kwarg_vars calldata_offset
                               kwargs_from_calldata common_label st = ((), st') ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ fuel.
      (∃ ss'. run_compiled_fragment ctx st st' ss fuel = OK ss' ∧
              ss'.vs_current_bb = common_label) ∨
      (∃ ss'. run_compiled_fragment ctx st st' ss fuel =
                Abort Revert_abort ss')
Proof
  cheat
QED

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
  cheat
QED
