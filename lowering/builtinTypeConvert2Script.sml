Theory builtinTypeConvert2
Ancestors
  builtinTypeConvert1 builtinConvertPrefix builtinIntClamp exprLoweringProps exprLowering emitHelperProps emitHelper
  context compileEnv venomExecSemantics venomState venomInst
Libs
  dep_rewrite

(* ===== Shared infrastructure ===== *)

Theorem eval_operand_update_not_none[local]:
  ∀ op ss v (w:bytes32).
    eval_operand op ss ≠ NONE ⇒
    eval_operand op (update_var v w ss) ≠ NONE
Proof
  Cases_on `op` >>
  simp[eval_operand_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> Cases_on `s = v` >> simp[]
QED

val compile_defs = [emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
  comp_return_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def,
  LET_THM, contextTheory.compile_alloc_buffer_def];

val emitted_insts_tac =
  simp[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM listTheory.APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND];

Theorem eval_operand_update_var_if[local]:
  ∀ v v' (w:bytes32) ss.
    eval_operand (Var v) (update_var v' w ss) =
    if v = v' then SOME w else eval_operand (Var v) ss
Proof
  simp[eval_operand_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >> rw[]
QED

Theorem eval_operand_mstore_not_none[local]:
  ∀ op addr (val:bytes32) ss.
    eval_operand op ss ≠ NONE ⇒
    eval_operand op (mstore addr val ss) ≠ NONE
Proof
  Cases_on `op` >>
  simp[eval_operand_def, mstore_def, lookup_var_def, LET_THM]
QED

Theorem eval_operand_alloca_fields[local]:
  ∀ op ss a n.
    eval_operand op (ss with <| vs_allocas := a;
                                vs_alloca_next := n |>) =
    eval_operand op ss
Proof
  Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def]
QED

Theorem step_ALLOCA[local]:
  ∀ id size out ss.
    ∃ ss'.
      step_inst_base (mk_inst id ALLOCA [Lit size] [out]) ss = OK ss' ∧
      (∀ op v. eval_operand op ss = SOME v ∧ (∀ x. op = Var x ⇒ x ≠ out) ⇒
               eval_operand op ss' = SOME v) ∧
      eval_operand (Var out) ss' ≠ NONE
Proof
  rw[step_inst_base_def, exec_alloca_def, mk_inst_def, LET_THM] >>
  Cases_on `FLOOKUP ss.vs_allocas id` >>
  simp[eval_operand_alloca_fields, eval_operand_update_var] >>
  TRY (rename1 `SOME p` >> PairCases_on `p` >>
       simp[eval_operand_alloca_fields, eval_operand_update_var]) >>
  rw[] >> Cases_on `op` >>
  gvs[eval_operand_def, update_var_def, lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE]
QED

val peel_alloca_impl_tac =
  simp[] >> rpt strip_tac >> CCONTR_TAC >> gvs[] >>
  qpat_x_assum `eval_operand _ ss = SOME _` mp_tac >>
  simp[eval_operand_def, lookup_var_def] >>
  gvs[fresh_vars_wrt_def] >>
  first_x_assum (qspec_then `st.cs_next_var` mp_tac) >>
  simp[finite_mapTheory.FLOOKUP_DEF];

(* One-instruction stages preserve the old arm_tac proof while allowing
   bounded feedback for long bytestring conversion chains. *)
Theorem fresh_var_name_eq[local]:
  !m n. (STRING #"%" (toString m) = STRING #"%" (toString n)) <=> (m = n)
Proof
  metis_tac[fresh_var_distinct]
QED

Theorem conversion_mload_step[local]:
  !id ops outs ss. step_inst_base (mk_inst id MLOAD ops outs) ss =
    exec_read1 (\w ss. mload (w2n w) ss) (mk_inst id MLOAD ops outs) ss
Proof
  pure_rewrite_tac[step_inst_base_def, mk_inst_def, instruction_accfupds,
    instruction_accessors, combinTheory.K_THM, opcode_case_def] >> simp[]
QED

Theorem conversion_memory_steps[local]:
  (!id ops outs ss. step_inst_base (mk_inst id ADD ops outs) ss =
    exec_pure2 word_add (mk_inst id ADD ops outs) ss) /\
  (!id ops outs ss. step_inst_base (mk_inst id MSTORE ops outs) ss =
    exec_write2 (\a v ss. mstore (w2n a) v ss) (mk_inst id MSTORE ops outs) ss)
Proof
  pure_rewrite_tac[step_inst_base_def, mk_inst_def, instruction_accfupds,
    instruction_accessors, combinTheory.K_THM, opcode_case_def] >> simp[]
QED

val weak_spec_step_tac =
  rewrite_tac[GSYM mk_inst_def] >>
  simp[Once run_inst_seq_def, conversion_memory_steps, conversion_mload_step, conversion_step_equations, clamp_step_equations, clamp_assert_step,
       exec_pure2_def, exec_pure1_def, exec_read1_def,
       exec_write2_def, mk_inst_def, eval_operand_def,
       lookup_var_update_var, eval_operand_update_var_if, fresh_var_name_eq];

val weak_spec_close_tac =
  rpt (BasicProvers.FULL_CASE_TAC >>
       TRY (metis_tac[eval_operand_update_not_none,
                     optionTheory.NOT_NONE_SOME])) >>
  gvs[eval_operand_update_var_if, lookup_var_update_var,
      fresh_var_name_eq, SF SFY_ss] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  TRY (Cases_on `op` >>
       gvs[eval_operand_def, lookup_var_update_var] >>
       rpt (IF_CASES_TAC >> gvs[]) >> NO_TAC);

val weak_spec_chain_tac =
  simp[run_inst_seq_def, step_inst_base_def,
       exec_pure2_def, exec_pure1_def, exec_read1_def,
       exec_write2_def, mk_inst_def,
       eval_operand_lit, eval_operand_update_var_if] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       TRY (metis_tac[eval_operand_update_not_none,
                       optionTheory.NOT_NONE_SOME])) >>
  gvs[eval_operand_update_var_if, SF SFY_ss] >>
  TRY (
    Cases_on `op` >>
    gvs[eval_operand_def, lookup_var_update_var] >>
    rpt (IF_CASES_TAC >> gvs[]) >>
    NO_TAC
  );

val unfold_tac =
  (* The bytestring preamble rereads the input after writing its length.
     Establish that read directly instead of splitting the input operand
     and duplicating every subsequent instruction case. *)
  `!n z. st.cs_next_var <= n ==>
     eval_operand v (update_var (STRING #"%" (toString n)) z ss) = SOME w` by
    (rpt strip_tac >>
     qspecl_then [`v`,`w`,`z`,`STRING #"%" (toString n)`,`n`,`ss`,`st`]
       mp_tac eval_operand_update_fresh >> simp[]) >>
  fs[compile_type_convert_def, load_bytestring_as_word_def,
     contextTheory.compile_alloc_buffer_def, LET_THM];

val arm_tac =
  rpt strip_tac >>
  fs[compile_type_convert_def, load_bytestring_as_word_def,
     contextTheory.compile_alloc_buffer_def, LET_THM] >>
  rpt (BasicProvers.FULL_CASE_TAC >> fs[]) >>
  gvs compile_defs >>
  TRY (gvs[emitted_insts_def, run_inst_seq_def, SF SFY_ss] >> NO_TAC) >>
  emitted_insts_tac >>
  weak_spec_chain_tac;

(* ===== Arms 11-20 ===== *)

Theorem compile_type_convert_11:
  ∀ v a b c d w ss st op st'.
    compile_type_convert v (ConvBytesMToDecimal a b c d) st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  (* Original proof: arm_tac; its definition is preserved above. *)
  rpt strip_tac >> unfold_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> fs[]) >> gvs compile_defs >>
  TRY (gvs[emitted_insts_def, run_inst_seq_def, SF SFY_ss] >> NO_TAC) >>
  emitted_insts_tac >>
  rewrite_tac[GSYM mk_inst_def] >>
  simp[run_inst_seq_def, conversion_step_equations, clamp_step_equations,
       clamp_assert_step, exec_pure2_def, exec_pure1_def, mk_inst_def,
       eval_operand_def, lookup_var_update_var, fresh_var_name_eq] >>
  pure_rewrite_tac[conversion_result_case_id] >>
  TRY (simp[lookup_var_update_var, SF SFY_ss] >> NO_TAC) >>
  ho_match_mp_tac conversion_assert_outcome >>
  simp[lookup_var_update_var, fresh_var_name_eq, SF SFY_ss]
QED

Theorem compile_type_convert_12:
  ∀ v a b w ss st op st'.
    compile_type_convert v (ConvBytesMToBytesM a b) st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  (* Original proof: arm_tac; its definition is preserved above. *)
  rpt strip_tac >> unfold_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> fs[]) >> gvs compile_defs >>
  TRY (gvs[emitted_insts_def, run_inst_seq_def, SF SFY_ss] >> NO_TAC) >>
  emitted_insts_tac >>
  weak_spec_step_tac >> weak_spec_step_tac >>
  weak_spec_step_tac >> weak_spec_step_tac >>
  weak_spec_step_tac >> weak_spec_step_tac >>
  weak_spec_step_tac >> weak_spec_step_tac >>
  weak_spec_step_tac >> weak_spec_step_tac >>
  weak_spec_step_tac >> weak_spec_step_tac >>
  weak_spec_close_tac
QED

Theorem compile_type_convert_13:
  ∀ v w ss st op st'.
    compile_type_convert v ConvBytestringToBool st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
  simp_tac pure_ss [compile_type_convert_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule load_bytestring_as_word_exec >>
  disch_then (qspecl_then [`ss`,`w`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `ss1` strip_assume_tac) >>
  gvs[comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op ISZERO [r] st1 = (z,st2)` >>
  drule emit_op_ISZERO_correct >>
  disch_then (qspecl_then [`x`,`ss1`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `ss2` strip_assume_tac) >>
  qpat_assum `emit_op ISZERO [z] _ = _` (mp_then Any mp_tac emit_op_ISZERO_correct) >>
  disch_then (qspecl_then [`bool_to_word (x = 0w)`,`ss2`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `ss3` strip_assume_tac) >>
  imp_res_tac inst_extends_load_bytestring_as_word >>
  imp_res_tac inst_extends_emit_op >>
  `inst_extends st st2` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st st2) ss = OK ss2` by
    (irule run_inst_seq_compose_ok >> qexistsl [`ss1`,`st1`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st') ss = OK ss3` by
    (irule run_inst_seq_compose_ok >> qexistsl [`ss2`,`st2`] >> simp[]) >>
  metis_tac[]
QED

Theorem compile_type_convert_14:
  !v a b n w ss st op st'.
    compile_type_convert v (ConvBytestringToInt a b n) st = (op,st') /\
    eval_operand v ss = SOME w /\ fresh_vars_wrt st ss ==>
    ?ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' /\
       eval_operand op ss' = SOME result) \/
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >> Cases_on `a` >>
  qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
  simp_tac pure_ss [compile_type_convert_def, comp_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule load_bytestring_as_word_exec >>
  disch_then (qspecl_then [`ss`,`w`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `ss1` strip_assume_tac) >>
  imp_res_tac inst_extends_load_bytestring_as_word >>
  (Cases_on `n * 8 > b` >> gvs[comp_return_def]
   >- (imp_res_tac inst_extends_compile_int_clamp >>
       drule_all prefix_compile_int_clamp_exec >> simp[]) >>
   metis_tac[])
QED

Theorem compile_type_convert_16:
  ∀ v a b c n w ss st op st'.
    compile_type_convert v (ConvBytestringToDecimal a b c n) st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
  simp_tac pure_ss [compile_type_convert_def, comp_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule load_bytestring_as_word_exec >>
  disch_then (qspecl_then [`ss`,`w`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `ss1` strip_assume_tac) >>
  imp_res_tac inst_extends_load_bytestring_as_word >>
  Cases_on `n * 8 <= 168` >- (gvs[comp_return_def] >> metis_tac[]) >>
  gvs[comp_return_def] >>
  rename1 `load_bytestring_as_word v SAR st = ((r,k),st1)` >>
  `inst_extends st1 st'` by
    (gvs compile_defs >> simp[inst_extends_def, emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND]) >>
  drule_all run_inst_seq_emit_extend >> disch_then SUBST1_TAC >>
  gvs compile_defs >> emitted_insts_tac >>
  qspecl_then [`st1`,`ss1`,`op`,`x`] mp_tac fresh_vars_wrt_eval_operand >>
  simp[] >> disch_tac >> Cases_on `op` >> gvs[eval_operand_def] >>
  TRY (rename1 `lookup_var input_name ss1 = SOME value` >>
       `!j. st1.cs_next_var <= j ==> input_name <> STRING #"%" (toString j)` by
         (rpt strip_tac >> first_x_assum drule >> simp[])) >>
  rewrite_tac[GSYM mk_inst_def] >>
  simp[run_inst_seq_def, conversion_step_equations, clamp_step_equations,
       clamp_assert_step, exec_pure2_def, exec_pure1_def, mk_inst_def,
       eval_operand_def, lookup_var_update_var, fresh_var_name_eq] >>
  pure_rewrite_tac[conversion_result_case_id] >>
  ho_match_mp_tac conversion_assert_outcome >>
  simp[lookup_var_update_var, update_var_def, SF SFY_ss]
QED

Theorem compile_type_convert_17:
  ∀ v a w ss st op st'.
    compile_type_convert v (ConvBytestringToBytesM a) st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  (* Original proof: arm_tac; its definition is preserved above. *)
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
  simp_tac pure_ss [compile_type_convert_def, comp_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule load_bytestring_as_word_exec >>
  disch_then (qspecl_then [`ss`,`w`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `ss1` strip_assume_tac) >>
  drule emit_conversion_shift_exec >>
  disch_then (qspecl_then [`ss1`,`y`,`x`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `ss2` strip_assume_tac) >>
  imp_res_tac inst_extends_load_bytestring_as_word >>
  imp_res_tac inst_extends_emit_op >>
  rename1 `load_bytestring_as_word v SHR st = ((r,k),st1)` >>
  `run_inst_seq (emitted_insts st st') ss = OK ss2` by
    (irule run_inst_seq_compose_ok >> qexistsl [`ss1`,`st1`] >> simp[]) >>
  metis_tac[]
QED

Theorem compile_type_convert_18:
  ∀ v a n w ss st op st'.
    compile_type_convert v (ConvBytestringCast a n) st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >> fs[compile_type_convert_def, LET_THM] >>
  rpt (BasicProvers.FULL_CASE_TAC >> fs[]) >> gvs compile_defs >>
  TRY (gvs[emitted_insts_def, run_inst_seq_def, SF SFY_ss] >> NO_TAC) >>
  emitted_insts_tac >>
  qspecl_then [`st`,`ss`,`op`,`w`] mp_tac fresh_vars_wrt_eval_operand >>
  simp[] >> disch_tac >> Cases_on `op` >> gvs[eval_operand_def] >>
  TRY (rename1 `lookup_var input_name ss = SOME value` >>
       `!j. st.cs_next_var <= j ==> input_name <> STRING #"%" (toString j)` by
         (rpt strip_tac >> first_x_assum drule >> simp[])) >>
  rewrite_tac[GSYM mk_inst_def] >>
  simp[run_inst_seq_def, conversion_mload_step, clamp_step_equations,
       clamp_assert_step, exec_read1_def, exec_pure2_def, exec_pure1_def,
       mk_inst_def, eval_operand_def, lookup_var_update_var, fresh_var_name_eq] >>
  pure_rewrite_tac[conversion_result_case_id] >>
  ho_match_mp_tac conversion_assert_outcome >>
  simp[lookup_var_update_var, update_var_def, SF SFY_ss]
QED

(* ConvFixedToBytestring — needs ALLOCA + MSTORE, separate proof *)
Theorem compile_type_convert_19:
  ∀ v a w ss st op st'.
    compile_type_convert v (ConvFixedToBytestring a) st = (op, st') ∧
    eval_operand v ss = SOME w ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  fs[compile_type_convert_def, load_bytestring_as_word_def,
     contextTheory.compile_alloc_buffer_def] >>
  gvs compile_defs >>
  emitted_insts_tac >>
  qspecl_then [`st.cs_next_id`, `64w`,
    `STRING #"%" (toString st.cs_next_var)`, `ss`]
    strip_assume_tac step_ALLOCA >>
  rename1 `step_inst_base _ ss = OK ss1` >>
  drule run_inst_seq_cons_ok >>
  disch_then (fn th => rewrite_tac[th]) >>
  pop_assum mp_tac >>
  pop_assum (qspecl_then [`v`, `w`] mp_tac) >>
  (impl_tac >- peel_alloca_impl_tac) >>
  rpt strip_tac >>
  (* Original whole-chain simplifier exceeded the 10s tactic bound:
  simp[run_inst_seq_def, step_inst_base_def,
       exec_pure2_def, exec_pure1_def, exec_read1_def,
       exec_write2_def, mk_inst_def,
       eval_operand_lit, eval_operand_update_var_if] >>
  *)
  weak_spec_step_tac >> weak_spec_step_tac >> weak_spec_step_tac >>
  simp[Once run_inst_seq_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       TRY (metis_tac[eval_operand_update_not_none,
                       eval_operand_mstore_not_none,
                       optionTheory.NOT_NONE_SOME])) >>
  (* Original finish (preserved):
  gvs[eval_operand_update_var_if, eval_operand_mstore,
      ASCIInumbersTheory.toString_11] >>
  metis_tac[eval_operand_mstore, eval_operand_update_var_if,
            ASCIInumbersTheory.toString_11,
            arithmeticTheory.ADD1, numTheory.NOT_SUC]
  *)
  gvs[eval_operand_def, lookup_var_update_var, lookup_var_mstore,
      fresh_var_name_eq, SF SFY_ss] >>
  simp[EXISTS_OR_THM, lookup_var_update_var, fresh_var_name_eq]
QED

Theorem compile_type_convert_20:
  ∀ v w ss st op st'.
    compile_type_convert v ConvIdentity st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  arm_tac
QED
