Theory builtinTypeConvert2
Ancestors
  exprLoweringProps exprLowering emitHelperProps emitHelper
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
  arm_tac
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
  arm_tac
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
  arm_tac
QED

Theorem compile_type_convert_14:
  ∀ v a b w ss st op st'.
    compile_type_convert v (ConvBytestringToInt a b) st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  arm_tac
QED

Theorem compile_type_convert_15:
  ∀ v w ss st op st'.
    compile_type_convert v ConvBytestringToAddress st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  arm_tac
QED

Theorem compile_type_convert_16:
  ∀ v a b c w ss st op st'.
    compile_type_convert v (ConvBytestringToDecimal a b c) st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  arm_tac
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
  arm_tac
QED

Theorem compile_type_convert_18:
  ∀ v a w ss st op st'.
    compile_type_convert v (ConvBytestringCast a) st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  arm_tac
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
  simp[run_inst_seq_def, step_inst_base_def,
       exec_pure2_def, exec_pure1_def, exec_read1_def,
       exec_write2_def, mk_inst_def,
       eval_operand_lit, eval_operand_update_var_if] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       TRY (metis_tac[eval_operand_update_not_none,
                       eval_operand_mstore_not_none,
                       optionTheory.NOT_NONE_SOME])) >>
  gvs[eval_operand_update_var_if, eval_operand_mstore,
      ASCIInumbersTheory.toString_11] >>
  metis_tac[eval_operand_mstore, eval_operand_update_var_if,
            ASCIInumbersTheory.toString_11,
            arithmeticTheory.ADD1, numTheory.NOT_SUC]
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
