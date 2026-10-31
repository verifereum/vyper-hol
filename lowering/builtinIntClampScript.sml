Theory builtinIntClamp
Ancestors
  exprLoweringProps exprLowering emitHelperProps emitHelper context compileEnv
  venomExecSemantics venomState venomInst

Theorem eval_operand_update_var_if[local]:
  !v v' (w:bytes32) ss.
    eval_operand (Var v) (update_var v' w ss) =
    if v = v' then SOME w else eval_operand (Var v) ss
Proof
  simp[eval_operand_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >> rw[]
QED

Theorem fresh_var_name_eq[local]:
  !m n. (STRING #"%" (toString m) = STRING #"%" (toString n)) <=> (m = n)
Proof
  metis_tac[fresh_var_distinct]
QED

Theorem clamp_assert_step:
  !id a ss.
    step_inst_base (mk_inst id ASSERT [a] []) ss =
      (case eval_operand a ss of
         SOME c => if c = 0w then Abort Revert_abort (revert_state (set_returndata [] ss)) else OK ss
       | NONE => Error "undefined operand")
Proof
  pure_rewrite_tac[step_inst_base_def, mk_inst_def, instruction_accfupds,
    instruction_accessors, combinTheory.K_THM, opcode_case_def] >> simp[]
QED

Theorem clamp_step_equations:
  (!id a b dst ss. step_inst_base (mk_inst id SLT [a;b] [dst]) ss =
    exec_pure2 (\x y. bool_to_word (x < y)) (mk_inst id SLT [a;b] [dst]) ss) /\
  (!id a b dst ss. step_inst_base (mk_inst id SGT [a;b] [dst]) ss =
    exec_pure2 (\x y. bool_to_word (x > y)) (mk_inst id SGT [a;b] [dst]) ss) /\
  (!id a b dst ss. step_inst_base (mk_inst id GT [a;b] [dst]) ss =
    exec_pure2 (\x y. bool_to_word (w2n x > w2n y)) (mk_inst id GT [a;b] [dst]) ss) /\
  (!id a b dst ss. step_inst_base (mk_inst id AND [a;b] [dst]) ss =
    exec_pure2 ($&&) (mk_inst id AND [a;b] [dst]) ss) /\
  (!id a dst ss. step_inst_base (mk_inst id ISZERO [a] [dst]) ss =
    exec_pure1 (\x. bool_to_word (x = 0w)) (mk_inst id ISZERO [a] [dst]) ss)
Proof
  pure_rewrite_tac[step_inst_base_def, mk_inst_def, instruction_accfupds,
    instruction_accessors, combinTheory.K_THM, opcode_case_def] >> simp[]
QED

val clamp_step_tac =
  rewrite_tac[GSYM mk_inst_def] >>
  simp[Once run_inst_seq_def, clamp_step_equations, clamp_assert_step,
       exec_pure2_def, exec_pure1_def, mk_inst_def,
       eval_operand_def, lookup_var_update_var, eval_operand_update_var_if,
       fresh_var_name_eq];

val clamp_close_tac =
  rpt (BasicProvers.FULL_CASE_TAC >>
    gvs[eval_operand_update_var_if, lookup_var_update_var, fresh_var_name_eq, SF SFY_ss]);

Theorem compile_int_clamp_exec:
  !s b v w ss st op st'.
    compile_int_clamp s b v st = (op, st') /\
    eval_operand v ss = SOME w /\ fresh_vars_wrt st ss ==>
    ?ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' /\
       eval_operand op ss' = SOME result) \/
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  gvs[compile_int_clamp_def, LET_THM] >>
  rpt (BasicProvers.FULL_CASE_TAC >> fs[]) >>
  gvs[emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
      comp_return_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def] >>
  simp[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM listTheory.APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  TRY (qabbrev_tac `lo : bytes32 = i2w (- &(2 ** (b - 1)))` >>
       qabbrev_tac `hi : bytes32 = i2w (&(2 ** (b - 1) - 1))`) >>
  qspecl_then [`st`,`ss`,`op`,`w`] mp_tac fresh_vars_wrt_eval_operand >>
  simp[] >> disch_tac >>
  Cases_on `op` >> gvs[eval_operand_def] >>
  clamp_step_tac >> clamp_step_tac >>
  clamp_step_tac >> clamp_step_tac >>
  clamp_step_tac >> clamp_step_tac >>
  clamp_step_tac >> clamp_step_tac >>
  clamp_step_tac >> clamp_step_tac >>
  clamp_step_tac >> clamp_step_tac >>
  clamp_step_tac >> clamp_step_tac >> clamp_close_tac
QED
