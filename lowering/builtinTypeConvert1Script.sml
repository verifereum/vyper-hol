Theory builtinTypeConvert1
Ancestors
  builtinConvertPrefix builtinIntClamp exprLoweringProps exprLowering emitHelperProps emitHelper
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

(* Unconditional equality avoids repeatedly proving the conditional
   distinctness premise while simplifying generated-variable reads. *)
Theorem fresh_var_name_eq[local]:
  !m n. (STRING #"%" (toString m) = STRING #"%" (toString n)) <=> (m = n)
Proof
  metis_tac[fresh_var_distinct]
QED

Theorem conversion_step_equations:
  (!id ops outs ss. step_inst_base (mk_inst id SHL ops outs) ss =
    exec_pure2 (\n w. word_lsl w (w2n n)) (mk_inst id SHL ops outs) ss) /\
  (!id ops outs ss. step_inst_base (mk_inst id SHR ops outs) ss =
    exec_pure2 (\n w. word_lsr w (w2n n)) (mk_inst id SHR ops outs) ss) /\
  (!id ops outs ss. step_inst_base (mk_inst id SAR ops outs) ss =
    exec_pure2 (\n w. word_asr w (w2n n)) (mk_inst id SAR ops outs) ss) /\
  (!id ops outs ss. step_inst_base (mk_inst id SIGNEXTEND ops outs) ss =
    exec_pure2 sign_extend (mk_inst id SIGNEXTEND ops outs) ss) /\
  (!id ops outs ss. step_inst_base (mk_inst id EQ ops outs) ss =
    exec_pure2 (\x y. bool_to_word (x = y)) (mk_inst id EQ ops outs) ss) /\
  (!id ops outs ss. step_inst_base (mk_inst id MUL ops outs) ss =
    exec_pure2 word_mul (mk_inst id MUL ops outs) ss) /\
  (!id ops outs ss. step_inst_base (mk_inst id SDIV ops outs) ss =
    exec_pure2 safe_sdiv (mk_inst id SDIV ops outs) ss)
Proof
  pure_rewrite_tac[step_inst_base_def, mk_inst_def, instruction_accfupds,
    instruction_accessors, combinTheory.K_THM, opcode_case_def] >> simp[]
QED

val weak_spec_step_tac =
  rewrite_tac[GSYM mk_inst_def] >>
  simp[Once run_inst_seq_def, conversion_step_equations, clamp_step_equations, clamp_assert_step,
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

val unfold_tac =
  fs[compile_type_convert_def, load_bytestring_as_word_def,
     contextTheory.compile_alloc_buffer_def, LET_THM];

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
  rpt strip_tac >> unfold_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> fs[]) >>
  gvs compile_defs >> emitted_insts_tac >>
  weak_spec_step_tac >> weak_spec_step_tac >>
  weak_spec_step_tac >> weak_spec_step_tac >> weak_spec_close_tac >>
  qmatch_goalsub_abbrev_tac `update_var out_var out_val rest` >>
  qexistsl [`update_var out_var out_val rest`,`out_val`] >>
  simp[lookup_var_update_var]
QED

val clamp_raw_step_tac =
  rewrite_tac[GSYM mk_inst_def] >>
  simp[run_inst_seq_def, clamp_step_equations, clamp_assert_step,
       exec_pure2_def, exec_pure1_def, mk_inst_def, eval_operand_def,
       lookup_var_update_var, eval_operand_update_var_if, fresh_var_name_eq];

Theorem conversion_result_case_id:
  !r. (case r of OK s => OK s | Halt x => Halt x |
         Abort a s => Abort a s | IntRet x s => IntRet x s | Error e => Error e) = r
Proof
  Cases >> simp[]
QED

Theorem conversion_assert_outcome:
  !b bad good P. (?w. P good w) ==>
    ?s w. ((if b then Abort Revert_abort bad else OK good) = OK s /\ P s w) \/
          (if b then Abort Revert_abort bad else OK good) = Abort Revert_abort s
Proof
  rpt gen_tac >> strip_tac >> Cases_on `b` >> simp[] >> metis_tac[]
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
  rpt strip_tac >> Cases_on `a` >> Cases_on `c` >> unfold_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> fs[]) >>
  TRY (drule_all compile_int_clamp_exec >> simp[] >> NO_TAC) >>
  gvs compile_defs >>
  TRY (gvs[emitted_insts_def, run_inst_seq_def, SF SFY_ss] >> NO_TAC) >>
  emitted_insts_tac >>
  qspecl_then [`st`,`ss`,`op`,`w`] mp_tac fresh_vars_wrt_eval_operand >>
  simp[] >> disch_tac >> Cases_on `op` >> gvs[eval_operand_def] >>
  TRY (rename1 `lookup_var input_name ss = SOME value` >>
       `!n. st.cs_next_var <= n ==> input_name <> STRING #"%" (toString n)` by
         (rpt strip_tac >> first_x_assum drule >> simp[])) >>
  clamp_raw_step_tac >> clamp_raw_step_tac >>
  clamp_raw_step_tac >> clamp_raw_step_tac >>
  clamp_raw_step_tac >> clamp_raw_step_tac >>
  clamp_raw_step_tac >> clamp_raw_step_tac >>
  clamp_raw_step_tac >> clamp_raw_step_tac >>
  pure_rewrite_tac[conversion_result_case_id] >>
  ho_match_mp_tac conversion_assert_outcome >>
  simp[lookup_var_update_var, eval_operand_update_var_if, update_var_def, SF SFY_ss]
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
  rpt gen_tac >> strip_tac >> Cases_on `b` >>
  qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
  simp_tac pure_ss [compile_type_convert_def, comp_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule emit_conversion_shift_exec >>
  disch_then (qspecl_then [`ss`,`n2w ((32-a)*8)`,`w`] mp_tac) >>
  (impl_tac >- simp[eval_operand_lit]) >>
  disch_then (qx_choose_then `ss1` strip_assume_tac) >>
  imp_res_tac inst_extends_emit_op >>
  (Cases_on `a * 8 > c` >> gvs[comp_return_def]
   >- (imp_res_tac inst_extends_compile_int_clamp >>
       drule_all prefix_compile_int_clamp_exec >> simp[]) >>
   metis_tac[])
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
  weak_spec_step_tac >> weak_spec_step_tac >>
  weak_spec_step_tac >> weak_spec_step_tac >>
  weak_spec_close_tac
QED

(* Both decimal directions emit optional bounds checks followed by scaling. *)
val decimal_input_tac =
  qspecl_then [`st`,`ss`,`v`,`w`] mp_tac fresh_vars_wrt_eval_operand >>
  simp[] >> disch_tac >> Cases_on `v` >> gvs[eval_operand_def] >>
  TRY (rename1 `lookup_var input_name ss = SOME value` >>
       `!n. st.cs_next_var <= n ==> input_name <> STRING #"%" (toString n)` by
         (rpt strip_tac >> first_x_assum drule >> simp[]));

val decimal_bound_tac =
  weak_spec_step_tac >> weak_spec_step_tac >> weak_spec_step_tac >>
  TRY (IF_CASES_TAC >> simp[]);

val decimal_scale_tac =
  weak_spec_step_tac >> weak_spec_step_tac >>
  rewrite_tac[GSYM mk_inst_def] >>
  simp[run_inst_seq_def, conversion_step_equations, clamp_step_equations,
       clamp_assert_step, exec_pure2_def, exec_pure1_def, mk_inst_def,
       eval_operand_def, lookup_var_update_var, fresh_var_name_eq, SF SFY_ss];

Theorem compile_type_convert_5:
  ∀ v a b c d e w ss st op st'.
    compile_type_convert v (ConvIntToDecimal a b c d e) st = (op, st') ∧
    eval_operand v ss = SOME w ∧ fresh_vars_wrt st ss ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >> unfold_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> fs[]) >> gvs compile_defs >>
  TRY (gvs[emitted_insts_def, run_inst_seq_def, SF SFY_ss] >> NO_TAC) >>
  emitted_insts_tac >>
  decimal_input_tac >>
  decimal_bound_tac >> decimal_bound_tac >> decimal_scale_tac
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
  rpt strip_tac >> unfold_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> fs[]) >> gvs compile_defs >>
  TRY (gvs[emitted_insts_def, run_inst_seq_def, SF SFY_ss] >> NO_TAC) >>
  emitted_insts_tac >>
  decimal_input_tac >>
  decimal_bound_tac >> decimal_bound_tac >> decimal_scale_tac
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
  rpt strip_tac >> unfold_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> fs[]) >>
  gvs compile_defs >> emitted_insts_tac >>
  weak_spec_step_tac >> weak_spec_step_tac >>
  weak_spec_step_tac >> weak_spec_step_tac >> weak_spec_close_tac >>
  qmatch_goalsub_abbrev_tac `update_var out_var out_val rest` >>
  qexistsl [`update_var out_var out_val rest`,`out_val`] >>
  simp[lookup_var_update_var]
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
  `!v. compile_type_convert v ConvToAddress = compile_int_clamp F 160 v` by
    simp[compile_type_convert_def, compile_int_clamp_def, LET_THM] >>
  rpt strip_tac >> gvs[] >> drule_all compile_int_clamp_exec >> simp[]
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
  weak_spec_step_tac >> weak_spec_step_tac >>
  weak_spec_step_tac >> weak_spec_step_tac >>
  weak_spec_close_tac
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
  rpt strip_tac >> fs[compile_type_convert_def] >>
  Cases_on `a < 256` >> gvs[]
  >- (irule compile_int_clamp_exec >> metis_tac[]) >>
  gvs[comp_return_def, emitted_insts_def, run_inst_seq_def, SF SFY_ss]
QED
