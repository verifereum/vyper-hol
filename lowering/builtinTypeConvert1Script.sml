Theory builtinTypeConvert1
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

(* ===== Arms 1-10 ===== *)
(* 1:ConvToBool 2:ConvIntToInt 3:ConvBytesToInt 4:ConvIntToBytesM
   5:ConvIntToDecimal 6:ConvDecimalToInt 7:ConvBoolToDecimal
   8:ConvToAddress 9:ConvBytesToAddress 10:ConvToFlag *)

Theorem compile_type_convert_1:
  ∀ v w ss st op st'.
    compile_type_convert v ConvToBool st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  arm_tac
QED

Theorem compile_type_convert_2:
  ∀ v a b c d w ss st op st'.
    compile_type_convert v (ConvIntToInt a b c d) st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  arm_tac
QED

Theorem compile_type_convert_3:
  ∀ v a b c w ss st op st'.
    compile_type_convert v (ConvBytesToInt a b c) st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  arm_tac
QED

Theorem compile_type_convert_4:
  ∀ v a b c w ss st op st'.
    compile_type_convert v (ConvIntToBytesM a b c) st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  arm_tac
QED

Theorem compile_type_convert_5:
  ∀ v a b c d e w ss st op st'.
    compile_type_convert v (ConvIntToDecimal a b c d e) st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  arm_tac
QED

Theorem compile_type_convert_6:
  ∀ v a b c d e f w ss st op st'.
    compile_type_convert v (ConvDecimalToInt a b c d e f) st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  arm_tac
QED

Theorem compile_type_convert_7:
  ∀ v a w ss st op st'.
    compile_type_convert v (ConvBoolToDecimal a) st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  arm_tac
QED

Theorem compile_type_convert_8:
  ∀ v w ss st op st'.
    compile_type_convert v ConvToAddress st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  arm_tac
QED

Theorem compile_type_convert_9:
  ∀ v a w ss st op st'.
    compile_type_convert v (ConvBytesToAddress a) st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  arm_tac
QED

Theorem compile_type_convert_10:
  ∀ v a w ss st op st'.
    compile_type_convert v (ConvToFlag a) st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  arm_tac
QED
