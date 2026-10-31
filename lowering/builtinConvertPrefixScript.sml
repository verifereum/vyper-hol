Theory builtinConvertPrefix
Ancestors
  exprLoweringProps exprLowering compileEnv emitHelper emitHelperProps builtinIntClamp
Libs
  dep_rewrite

Theorem emit_conversion_shift_exec:
  !opc a b st r st' ss x y.
    emit_op opc [a;b] st = (r,st') /\
    (opc = SHR \/ opc = SAR \/ opc = SHL) /\
    eval_operand a ss = SOME x /\ eval_operand b ss = SOME y /\
    fresh_vars_wrt st ss ==>
    ?ss' z. run_inst_seq (emitted_insts st st') ss = OK ss' /\
      eval_operand r ss' = SOME z /\ fresh_vars_wrt st' ss' /\
      (!p u. eval_operand p ss = SOME u ==> eval_operand p ss' = SOME u)
Proof
  rpt strip_tac >> gvs[]
  >- (drule_all emit_op_SHR_correct >> metis_tac[])
  >- (qspecl_then [`SAR`, `\x y. word_asr y (w2n x)`]
        (mp_tac o BETA_RULE) emit_op_pure2_correct >>
      disch_then drule >>
      disch_then (qspecl_then [`x`,`y`,`ss`] mp_tac) >>
      (impl_tac >- (simp[] >> irule step_SAR >> simp[])) >> metis_tac[])
  >> qspecl_then [`SHL`, `\x y. word_lsl y (w2n x)`]
        (mp_tac o BETA_RULE) emit_op_pure2_correct >>
     disch_then drule >>
     disch_then (qspecl_then [`x`,`y`,`ss`] mp_tac) >>
     (impl_tac >- (simp[] >> irule step_SHL >> simp[])) >> metis_tac[]
QED

Theorem prefix_compile_int_clamp_exec:
  !st0 st1 st2 ss0 ss1 s b v op w.
    run_inst_seq (emitted_insts st0 st1) ss0 = OK ss1 /\
    inst_extends st0 st1 /\ inst_extends st1 st2 /\
    compile_int_clamp s b v st1 = (op,st2) /\
    eval_operand v ss1 = SOME w /\ fresh_vars_wrt st1 ss1 ==>
    ?ss2 result.
      (run_inst_seq (emitted_insts st0 st2) ss0 = OK ss2 /\
       eval_operand op ss2 = SOME result) \/
      run_inst_seq (emitted_insts st0 st2) ss0 = Abort Revert_abort ss2
Proof
  rpt strip_tac >> drule_all compile_int_clamp_exec >>
  drule_all run_inst_seq_emit_extend >> metis_tac[]
QED

Theorem emit_conversion_load_exec[local]:
  !a st r st'. emit_op MLOAD [a] st = (r,st') ==>
  !ss. (?x. eval_operand a ss = SOME x) /\ fresh_vars_wrt st ss ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    (?z. eval_operand r ss' = SOME z) /\ fresh_vars_wrt st' ss' /\
    (!p u. eval_operand p ss = SOME u ==> eval_operand p ss' = SOME u)
Proof
  rpt strip_tac >> drule_all emit_op_MLOAD_correct >> metis_tac[]
QED

Theorem emit_conversion_arith_exec[local]:
  !opc a b st r st'. emit_op opc [a;b] st = (r,st') ==>
  !ss. (opc = ADD \/ opc = SUB \/ opc = MUL) /\
    (?x. eval_operand a ss = SOME x) /\
    (?y. eval_operand b ss = SOME y) /\ fresh_vars_wrt st ss ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    (?z. eval_operand r ss' = SOME z) /\ fresh_vars_wrt st' ss' /\
    (!p u. eval_operand p ss = SOME u ==> eval_operand p ss' = SOME u)
Proof
  rpt strip_tac >> gvs[]
  >- (drule_all emit_op_ADD_correct >> metis_tac[])
  >- (drule_all emit_op_SUB_correct >> metis_tac[]) >>
  drule_all emit_op_MUL_correct >> metis_tac[]
QED

Theorem emit_conversion_shift_weak[local]:
  !opc a b st r st'. emit_op opc [a;b] st = (r,st') ==>
  !ss. (opc = SHR \/ opc = SAR \/ opc = SHL) /\
    (?x. eval_operand a ss = SOME x) /\
    (?y. eval_operand b ss = SOME y) /\ fresh_vars_wrt st ss ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    (?z. eval_operand r ss' = SOME z) /\ fresh_vars_wrt st' ss' /\
    (!p u. eval_operand p ss = SOME u ==> eval_operand p ss' = SOME u)
Proof
  rpt strip_tac >> gvs[] >> drule emit_conversion_shift_exec >>
  disch_then (qspecl_then [`ss`,`x`,`y`] mp_tac) >> simp[] >> metis_tac[]
QED

Theorem load_bytestring_as_word_exec:
  !v opc st r k st' ss w.
    load_bytestring_as_word v opc st = ((r,k),st') /\
    (opc = SHR \/ opc = SAR) /\ eval_operand v ss = SOME w /\
    fresh_vars_wrt st ss ==>
    ?ss' x y. run_inst_seq (emitted_insts st st') ss = OK ss' /\
      eval_operand r ss' = SOME x /\ eval_operand k ss' = SOME y /\
      fresh_vars_wrt st' ss' /\
      (!p u. eval_operand p ss = SOME u ==> eval_operand p ss' = SOME u)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `load_bytestring_as_word _ _ _ = _` mp_tac >>
  simp_tac pure_ss [load_bytestring_as_word_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [v] st = (len,st1)` >>
  rename1 `emit_op ADD [v; Lit 32w] st1 = (dp,st2)` >>
  rename1 `emit_op MLOAD [dp] st2 = (data,st3)` >>
  rename1 `emit_op SUB [Lit 32w; len] st3 = (sub,st4)` >>
  rename1 `emit_op MUL [sub; Lit 8w] st4 = (k,st5)` >>
  rev_drule emit_conversion_load_exec >>
  disch_then (qspec_then `ss` mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qx_choose_then `ss1` strip_assume_tac) >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac emit_conversion_arith_exec) >>
  disch_then (qspec_then `ss1` mp_tac) >>
  (impl_tac >- metis_tac[eval_operand_lit]) >>
  disch_then (qx_choose_then `ss2` strip_assume_tac) >>
  qpat_assum `emit_op MLOAD [dp] _ = _` (mp_then Any mp_tac emit_conversion_load_exec) >>
  disch_then (qspec_then `ss2` mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qx_choose_then `ss3` strip_assume_tac) >>
  qpat_assum `emit_op SUB _ _ = _` (mp_then Any mp_tac emit_conversion_arith_exec) >>
  disch_then (qspec_then `ss3` mp_tac) >>
  (impl_tac >- metis_tac[eval_operand_lit]) >>
  disch_then (qx_choose_then `ss4` strip_assume_tac) >>
  qpat_assum `emit_op MUL _ _ = _` (mp_then Any mp_tac emit_conversion_arith_exec) >>
  disch_then (qspec_then `ss4` mp_tac) >>
  (impl_tac >- metis_tac[eval_operand_lit]) >>
  disch_then (qx_choose_then `ss5` strip_assume_tac) >>
  qpat_assum `emit_op _ [k; data] _ = _` (mp_then Any mp_tac emit_conversion_shift_weak) >>
  disch_then (qspec_then `ss5` mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qx_choose_then `ss6` strip_assume_tac) >>
  rename1 `emit_op _ [k; data] st5 = (r,st6)` >>
  imp_res_tac inst_extends_emit_op >>
  `inst_extends st st2` by metis_tac[inst_extends_trans] >>
  `inst_extends st st3` by metis_tac[inst_extends_trans] >>
  `inst_extends st st4` by metis_tac[inst_extends_trans] >>
  `inst_extends st st5` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st st2) ss = OK ss2` by
    (irule run_inst_seq_compose_ok >> qexistsl [`ss1`,`st1`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st3) ss = OK ss3` by
    (irule run_inst_seq_compose_ok >> qexistsl [`ss2`,`st2`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st4) ss = OK ss4` by
    (irule run_inst_seq_compose_ok >> qexistsl [`ss3`,`st3`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st5) ss = OK ss5` by
    (irule run_inst_seq_compose_ok >> qexistsl [`ss4`,`st4`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st6) ss = OK ss6` by
    (irule run_inst_seq_compose_ok >> qexistsl [`ss5`,`st5`] >> simp[]) >>
  qexists_tac `ss6` >> simp[SF SFY_ss] >>
  rename1 `eval_operand k ss5 = SOME kval` >> qexists_tac `kval` >>
  (conj_tac >- (first_assum irule >> simp[])) >>
  rpt strip_tac >> rpt (first_assum irule)
QED

Theorem inst_extends_compile_int_clamp:
  !s b v st op st'. compile_int_clamp s b v st = (op,st') ==>
    inst_extends st st'
Proof
  rpt strip_tac >>
  gvs[compile_int_clamp_def, LET_THM] >>
  rpt (BasicProvers.FULL_CASE_TAC >> fs[]) >>
  gvs[emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
      comp_return_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def,
      inst_extends_def, emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM listTheory.APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem inst_extends_load_bytestring_as_word:
  !v opc st r k st'. load_bytestring_as_word v opc st = ((r,k),st') ==>
    inst_extends st st'
Proof
  rpt gen_tac >>
  simp_tac pure_ss [load_bytestring_as_word_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  imp_res_tac inst_extends_emit_op >>
  metis_tac[inst_extends_trans]
QED
