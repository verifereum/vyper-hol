Theory bodyPtrSignedConvertClamp
Ancestors
  bodyPtrSignedConvertScalarOps bodyPtrSignedConvertBool bodyPtrSignedConvertIszero
  venomExecSemantics exprSendPtr fragGasSeqPtr bodyPtrSignedConvertScalarTransfer list
  instSeqComposePtr fragExec instIdxIndep exprLowering exprLoweringProps emitHelperProps
  compileEnv loweringStateRelDefs ASCIInumbers rich_list ptrDiscipline finite_map venomState venomInst

Theorem int_clamp_unsigned_code:
  compile_int_clamp F bits x sa = (out,sb) ==>
  ?a b.
    out = x /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id GT [x; Lit (n2w (2 ** bits - 1))] [a];
       mk_inst (sa.cs_next_id+1) ISZERO [Var a] [b];
       mk_inst (sa.cs_next_id+2) ASSERT [Var b] []] /\
    a <> b /\
    (!p. not_fresh_at sa p ==> p <> a /\ p <> b) /\
    sb.cs_next_var = sa.cs_next_var+2 /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts+3
Proof
  simp[compile_int_clamp_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  strip_tac >> gvs[] >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  gvs[same_blocks_def, not_fresh_at_def, toString_inj] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
                `STRING #"%" (toString (sa.cs_next_var+1))`] >> simp[toString_inj]
QED

Theorem int_clamp_signed_code:
  compile_int_clamp T bits x sa = (out,sb) ==>
  ?a b c d e.
    out = x /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id SLT [x; Lit (i2w (- &(2 ** (bits-1))))] [a];
       mk_inst (sa.cs_next_id+1) ISZERO [Var a] [b];
       mk_inst (sa.cs_next_id+2) SGT [x; Lit (i2w (&(2 ** (bits-1)-1)))] [c];
       mk_inst (sa.cs_next_id+3) ISZERO [Var c] [d];
       mk_inst (sa.cs_next_id+4) AND [Var b; Var d] [e];
       mk_inst (sa.cs_next_id+5) ASSERT [Var e] []] /\
    ALL_DISTINCT [a;b;c;d;e] /\
    (!p. not_fresh_at sa p ==> ~MEM p [a;b;c;d;e]) /\
    sb.cs_next_var = sa.cs_next_var+5 /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts+6
Proof
  simp[compile_int_clamp_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  strip_tac >> gvs[] >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  gvs[same_blocks_def, not_fresh_at_def, toString_inj] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
                `STRING #"%" (toString (sa.cs_next_var+1))`,
                `STRING #"%" (toString (sa.cs_next_var+2))`,
                `STRING #"%" (toString (sa.cs_next_var+3))`,
                `STRING #"%" (toString (sa.cs_next_var+4))`] >> simp[toString_inj]
QED

Theorem unsigned_clamp_runtime_frame:
  run_inst_seq
    [mk_inst id GT [x; Lit hi] [a];
     mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) ASSERT [Var b] []] s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. p <> a /\ p <> b ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >> gvs[run_inst_seq_def, AllCaseEqs()] >>
  qpat_assum `step_inst_base (mk_inst id GT _ _) _ = _`
    (mp_then Any mp_tac convert_scalar_run_shape) >> simp[] >> strip_tac >> gvs[] >>
  drule iszero_run_shape >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def, mk_inst_def, AllCaseEqs()] >>
  strip_tac >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem scalar_double_check_runtime_frame:
  MEM opc1 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  MEM opc2 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  run_inst_seq
    [mk_inst id opc1 [x; Lit lo] [a];
     mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) opc2 [x; Lit hi] [c];
     mk_inst (id+3) ISZERO [Var c] [d];
     mk_inst (id+4) AND [Var b; Var d] [e];
     mk_inst (id+5) ASSERT [Var e] []] s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. ~MEM p [a;b;c;d;e] ==> lookup_var p t = lookup_var p s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `step_inst_base (mk_inst id opc1 _ _) _ = _`
    (mp_then Any mp_tac convert_scalar_run_shape) >> simp[] >>
  disch_then (qx_choose_then `w1` SUBST_ALL_TAC) >>
  qpat_x_assum `step_inst_base (mk_inst _ opc2 _ _) _ = _`
    (mp_then Any mp_tac convert_scalar_run_shape) >> simp[] >>
  disch_then (qx_choose_then `w2` SUBST_ALL_TAC) >>
  qpat_x_assum `MEM opc1 _` kall_tac >> qpat_x_assum `MEM opc2 _` kall_tac >>
  qpat_x_assum `step_inst_base (mk_inst _ ISZERO _ _) _ = _`
    (mp_then Any strip_assume_tac iszero_run_shape) >> gvs[] >>
  qpat_x_assum `step_inst_base (mk_inst _ ISZERO _ _) _ = _`
    (mp_then Any strip_assume_tac iszero_run_shape) >> gvs[] >>
  qpat_x_assum `step_inst_base (mk_inst _ AND _ _) _ = _`
    (mp_then Any mp_tac convert_scalar_run_shape) >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  CONV_TAC (LAND_CONV (LAND_CONV (REWRITE_CONV
    [step_inst_base_def, mk_inst_def, instruction_accessors,
     instruction_accfupds, combinTheory.K_THM, opcode_case_def]))) >>
  simp[AllCaseEqs()] >>
  strip_tac >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> simp[]
QED

Theorem int_clamp_runtime_frame:
  compile_int_clamp signed bits x sa = (out,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >> Cases_on `signed`
  >- (drule int_clamp_signed_code >> strip_tac >> gvs[] >>
      drule (SIMP_RULE (srw_ss()) [] (Q.INST
        [`opc1` |-> `SLT`, `opc2` |-> `SGT`] (SPEC_ALL scalar_double_check_runtime_frame))) >> strip_tac >> simp[] >> metis_tac[]) >>
  drule int_clamp_unsigned_code >> strip_tac >> gvs[] >>
  drule unsigned_clamp_runtime_frame >> strip_tac >> simp[] >> metis_tac[]
QED

Theorem scalar_iszero_certificate:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  op_prov G x = NONE /\ op_prov G y = NONE /\
  op_taint tn x = {} /\ op_taint tn y = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst id opc [x;y] [a];
                mk_inst (id+1) ISZERO [Var a] [b]] s = OK t ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id opc [x;y] [a]; mk_inst (id+1) ISZERO [Var a] [b]] s
    (DRESTRICT (DRESTRICT G (COMPL {a})) (COMPL {b}))
    (tn with t_var := tn.t_var |+ (a,{}) |+ (b,{}))
Proof
  strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  qpat_assum `step_inst_base (mk_inst id _ _ _) _ = _`
    (mp_then Any mp_tac convert_scalar_run_shape) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule iszero_run_shape >> strip_tac >>
  simp[inst_seq_ptr_def] >> conj_tac
  >- (irule convert_scalar_ptr_inst_ok >> simp[] >> goal_assum (drule_at Any)) >>
  `step_prov PG G (mk_inst id opc [x;y] [a]) (update_var a w s) =
     DRESTRICT G (COMPL {a})` by
    (simp[step_prov_def, set_prov_def, mk_inst_def] >>
     `out_prov PG G (mk_inst id opc [x;y] [a]) (update_var a w s) = NONE` by
       (irule out_prov_clearing_none >> gvs[MEM, mk_inst_def]) >>
     gvs[mk_inst_def]) >>
  `step_taint (mk_inst id opc [x;y] [a]) s (update_var a w s) tn =
    (tn with t_var := tn.t_var |+ (a,{}))` by
    (irule convert_scalar_ghost_update >> simp[] >> goal_assum (drule_at Any)) >>
  simp[] >>
  `step_inst_base (mk_inst (id+1) ISZERO [Var a] [b])
    (update_var a w s with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (update_var b (bool_to_word (w = 0w))
      (update_var a w s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule emitHelperPropsTheory.step_ISZERO >>
     simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  conj_tac
  >- (irule iszero_ptr_inst_ok >> simp[allocas_from_def, op_taint_def, FLOOKUP_UPDATE] >>
      goal_assum (drule_at Any)) >>
  simp[] >> drule iszero_ghost_update >> strip_tac >>
  gvs[DRESTRICT_DRESTRICT, eval_operand_def, lookup_var_def,
      update_var_def, FLOOKUP_UPDATE] >>
  qpat_assum `step_inst_base (mk_inst _ ISZERO _ _) _ = _`
    (mp_then Any strip_assume_tac iszero_ghost_update) >> simp[]
QED

Theorem clamp_assert_certificate:
  ~ctx_has_dalloca ctx /\ op_taint tn op = {} /\
  eval_operand op s = SOME w ==>
  inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id ASSERT [op] []] s G tn
Proof
  strip_tac >> simp[inst_seq_ptr_def] >> conj_tac
  >- (irule ptr_inst_ok_assert >> goal_assum (drule_at Any) >> simp[]) >>
  `step_inst_base (mk_inst id ASSERT [op] []) s =
    if w = 0w then Abort Revert_abort (revert_state (set_returndata [] s))
    else OK s` by
    (simp[mk_inst_def] >> irule venomExecProofsTheory.step_assert_behavior >>
     first_assum ACCEPT_TAC) >>
  Cases_on `w = 0w` >> simp[assert_ghost_unchanged, inst_seq_ptr_def]
QED

Theorem scalar_iszero_assert_certificate:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  op_prov G x = NONE /\ op_prov G y = NONE /\
  op_taint tn x = {} /\ op_taint tn y = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst id opc [x;y] [a];
                mk_inst (id+1) ISZERO [Var a] [b]] s = OK t ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    ([mk_inst id opc [x;y] [a]; mk_inst (id+1) ISZERO [Var a] [b]] ++
     [mk_inst (id+2) ASSERT [Var b] []]) s
    (DRESTRICT (DRESTRICT G (COMPL {a})) (COMPL {b}))
    (tn with t_var := tn.t_var |+ (a,{}) |+ (b,{}))
Proof
  strip_tac >> irule inst_seq_ptr_append >> conj_tac
  >- (gvs[MEM] >> simp[mk_inst_def, is_terminator_def]) >>
  qexistsl_tac [`DRESTRICT (DRESTRICT G (COMPL {a})) (COMPL {b})`,
               `t`, `tn with t_var := tn.t_var |+ (a,{}) |+ (b,{})`] >>
  reverse conj_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      irule scalar_iszero_certificate >> simp[] >> goal_assum (drule_at Any)) >>
  gen_tac >> irule clamp_assert_certificate >>
  simp[op_taint_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  drule iszero_run_shape >> strip_tac >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem unsigned_clamp_success_prefix:
  run_inst_seq
    [mk_inst id GT [x; Lit hi] [a];
     mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) ASSERT [Var b] []] s = OK t ==>
  ?u. run_inst_seq
    [mk_inst id GT [x; Lit hi] [a];
     mk_inst (id+1) ISZERO [Var a] [b]] s = OK u
Proof
  simp[run_inst_seq_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem unsigned_clamp_abort_prefix:
  run_inst_seq
    [mk_inst id GT [x; Lit hi] [a];
     mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) ASSERT [Var b] []] s = Abort err t ==>
  ?u. run_inst_seq
    [mk_inst id GT [x; Lit hi] [a];
     mk_inst (id+1) ISZERO [Var a] [b]] s = OK u
Proof
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac
  >~ [`step_inst_base (mk_inst _ ASSERT _ _) _ = Abort _ _`]
  >- metis_tac[] >>
  qpat_x_assum `step_inst_base _ _ = Abort _ _` mp_tac >>
  CONV_TAC (LAND_CONV (LAND_CONV (REWRITE_CONV
    [step_inst_base_def, mk_inst_def, instruction_accessors,
     instruction_accfupds, combinTheory.K_THM, opcode_case_def]))) >>
  simp[exec_pure2_def, exec_pure1_def, AllCaseEqs()]
QED

Theorem int_clamp_unsigned_fixed_certificate:
  compile_int_clamp F bits x sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq (emitted_insts sa sb) s = OK t \/
   run_inst_seq (emitted_insts sa sb) s = Abort err t) ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> (drule int_clamp_unsigned_code >> strip_tac >> gvs[] >>
  imp_res_tac unsigned_clamp_success_prefix >>
  imp_res_tac unsigned_clamp_abort_prefix >>
  qexistsl_tac [`DRESTRICT (DRESTRICT G (COMPL {a})) (COMPL {b})`,
    `tn with t_var := tn.t_var |+ (a,{}) |+ (b,{})`] >>
  conj_tac
  >- (irule (PURE_REWRITE_RULE [APPEND] scalar_iszero_assert_certificate) >>
      simp[op_prov_def, op_taint_def] >> goal_assum (drule_at Any)) >>
  simp[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  Cases_on `out` >> gvs[op_prov_def, op_taint_def] >>
  rpt IF_CASES_TAC >> simp[])
QED

Theorem scalar_iszero_clean_frame_certificate:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  op_prov G x = NONE /\ op_prov G y = NONE /\
  op_taint tn x = {} /\ op_taint tn y = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst id opc [x;y] [a];
                mk_inst (id+1) ISZERO [Var a] [b]] s = OK t ==>
  ?H th.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id opc [x;y] [a]; mk_inst (id+1) ISZERO [Var a] [b]]
      (s with vs_inst_idx := k) H th) /\
    op_prov H (Var b) = NONE /\ op_taint th (Var b) = {} /\
    (!op. op_prov G op = NONE /\ op_taint tn op = {} ==>
      op_prov H op = NONE /\ op_taint th op = {}) /\
    (!p. p <> a /\ p <> b ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >>
  qexistsl_tac [`DRESTRICT (DRESTRICT G (COMPL {a})) (COMPL {b})`,
    `tn with t_var := tn.t_var |+ (a,{}) |+ (b,{})`] >> conj_tac
  >- (gen_tac >> irule scalar_iszero_certificate >> simp[] >>
      qexists_tac `t with vs_inst_idx := k` >>
      `~is_terminator opc` by gvs[MEM, is_terminator_def] >>
      simp[run_inst_seq_inst_idx, GSYM mk_inst_def, is_terminator_def,
           exec_result_map_def]) >>
  simp[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  Cases >> simp[op_prov_def, op_taint_def] >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem scalar_clean_frame_certificate:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  op_prov G x = NONE /\ op_prov G y = NONE /\
  op_taint tn x = {} /\ op_taint tn y = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst id opc [x;y] [z]] s = OK t ==>
  ?H th.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id opc [x;y] [z]]
      (s with vs_inst_idx := k) H th) /\
    op_prov H (Var z) = NONE /\ op_taint th (Var z) = {} /\
    (!op. op_prov G op = NONE /\ op_taint tn op = {} ==>
      op_prov H op = NONE /\ op_taint th op = {}) /\
    (!p. p <> z ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >>
  `step_inst_base (mk_inst id opc [x;y] [z]) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  qexistsl_tac [`DRESTRICT G (COMPL {z})`,
    `tn with t_var := tn.t_var |+ (z,{})`] >> conj_tac
  >- (gen_tac >>
      `step_inst_base (mk_inst id opc [x;y] [z])
        (s with vs_inst_idx := k) = OK (t with vs_inst_idx := k)` by
        (`~is_terminator opc` by gvs[MEM, is_terminator_def] >>
         simp[step_inst_inst_idx_indep, GSYM mk_inst_def, exec_result_map_def]) >>
      simp[inst_seq_ptr_def] >> conj_tac
      >- (irule convert_scalar_ptr_inst_ok >> simp[] >> goal_assum (drule_at Any)) >>
      `step_prov PG G (mk_inst id opc [x;y] [z]) t =
        DRESTRICT G (COMPL {z})` by
        (simp[step_prov_def, set_prov_def, mk_inst_def] >>
         `out_prov PG G (mk_inst id opc [x;y] [z]) t = NONE` by
           (irule out_prov_clearing_none >> gvs[MEM, mk_inst_def]) >>
         gvs[mk_inst_def]) >>
      simp[] >> sym_tac >> irule convert_scalar_ghost_update >>
      simp[] >> goal_assum (drule_at Any)) >>
  simp[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  Cases >> simp[op_prov_def, op_taint_def] >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem checked_prefix_assert_certificate:
  EVERY (\i. ~is_terminator i.inst_opcode) xs /\
  run_inst_seq xs s = OK t /\
  (!k. inst_seq_ptr D 0 ctx fn PG G tn xs (s with vs_inst_idx := k) H th) /\
  ~ctx_has_dalloca ctx /\ op_taint th op = {} /\
  eval_operand op t = SOME w ==>
  inst_seq_ptr D 0 ctx fn PG G tn (xs ++ [mk_inst id ASSERT [op] []]) s H th
Proof
  strip_tac >> irule inst_seq_ptr_append >> simp[] >>
  qexistsl_tac [`H`,`th`] >> reverse conj_tac
  >- (simp[] >>
      first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  gen_tac >> irule clamp_assert_certificate >>
  simp[eval_operand_def, lookup_var_def] >>
  Cases_on `op` >> gvs[eval_operand_def, lookup_var_def]
QED

Theorem scalar_double_check_prefix_runs:
  MEM opc1 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  MEM opc2 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  (run_inst_seq
    [mk_inst id opc1 [x; Lit lo] [a];
     mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) opc2 [x; Lit hi] [c];
     mk_inst (id+3) ISZERO [Var c] [d];
     mk_inst (id+4) AND [Var b; Var d] [e];
     mk_inst (id+5) ASSERT [Var e] []] s = OK t \/
   run_inst_seq
    [mk_inst id opc1 [x; Lit lo] [a];
     mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) opc2 [x; Lit hi] [c];
     mk_inst (id+3) ISZERO [Var c] [d];
     mk_inst (id+4) AND [Var b; Var d] [e];
     mk_inst (id+5) ASSERT [Var e] []] s = Abort err t) ==>
  ?u v w.
    run_inst_seq [mk_inst id opc1 [x; Lit lo] [a];
                 mk_inst (id+1) ISZERO [Var a] [b]] s = OK u /\
    run_inst_seq [mk_inst (id+2) opc2 [x; Lit hi] [c];
                 mk_inst (id+3) ISZERO [Var c] [d]] u = OK v /\
    run_inst_seq [mk_inst (id+4) AND [Var b; Var d] [e]] v = OK w /\
    (?value. eval_operand (Var e) w = SOME value)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `_ \/ _` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs(), convert_scalar_no_abort,
       scalar_iszero_no_abort] >> strip_tac >> (
  qpat_assum `step_inst_base (mk_inst _ AND _ _) _ = OK _`
    (mp_then Any mp_tac convert_scalar_run_shape) >> simp[] >> strip_tac >>
  gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[])
QED

Theorem scalar_double_checked_prefix:
  MEM opc1 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  MEM opc2 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst id opc1 [x; Lit lo] [a];
               mk_inst (id+1) ISZERO [Var a] [b]] s = OK u /\
  run_inst_seq [mk_inst (id+2) opc2 [x; Lit hi] [c];
               mk_inst (id+3) ISZERO [Var c] [d]] u = OK v /\
  run_inst_seq [mk_inst (id+4) AND [Var b; Var d] [e]] v = OK w ==>
  ?H th.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id opc1 [x; Lit lo] [a];
       mk_inst (id+1) ISZERO [Var a] [b];
       mk_inst (id+2) opc2 [x; Lit hi] [c];
       mk_inst (id+3) ISZERO [Var c] [d];
       mk_inst (id+4) AND [Var b; Var d] [e]]
      (s with vs_inst_idx := k) H th) /\
    op_prov H (Var e) = NONE /\ op_taint th (Var e) = {} /\
    (!op. op_prov G op = NONE /\ op_taint tn op = {} ==>
      op_prov H op = NONE /\ op_taint th op = {}) /\
    (!p. ~MEM p [a;b;c;d;e] ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >>
  `op_prov G (Lit lo) = NONE /\ op_taint tn (Lit lo) = {}` by
    simp[op_prov_def, op_taint_def] >>
  drule_all scalar_iszero_clean_frame_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H1` (qx_choose_then `tn1` strip_assume_tac))) >>
  `op_prov H1 x = NONE /\ op_taint tn1 x = {}` by metis_tac[] >>
  `op_prov H1 (Lit hi) = NONE /\ op_taint tn1 (Lit hi) = {}` by
    simp[op_prov_def, op_taint_def] >>
  drule_all (GEN_ALL (PURE_REWRITE_RULE [GSYM arithmeticTheory.ADD_ASSOC, EVAL ``2+1:num``]
    (Q.INST [`id` |-> `id+2`] (SPEC_ALL scalar_iszero_clean_frame_certificate)))) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H2` (qx_choose_then `tn2` strip_assume_tac))) >>
  `op_prov H2 (Var b) = NONE /\ op_taint tn2 (Var b) = {}` by metis_tac[] >>
  `MEM AND [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV]` by simp[] >>
  drule_all scalar_clean_frame_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H3` (qx_choose_then `tn3` strip_assume_tac))) >>
  qexistsl_tac [`H3`,`tn3`] >> conj_tac
  >- (irule (PURE_REWRITE_RULE [APPEND] (Q.INST
        [`xs` |-> `[mk_inst id opc1 [x; Lit lo] [a];
                    mk_inst (id+1) ISZERO [Var a] [b]]`]
        (Q.INST [`lo` |-> `0:num`] (SPEC_ALL inst_seq_ptr_uniform_append)))) >>
      imp_res_tac convert_scalar_opcode_filter >>
      simp[mk_inst_def, is_terminator_def] >>
      qexistsl_tac [`H1`,`tn1`] >> simp[GSYM mk_inst_def] >>
      irule (PURE_REWRITE_RULE [APPEND] (Q.INST
        [`xs` |-> `[mk_inst (id+2) opc2 [x; Lit hi] [c];
                    mk_inst (id+3) ISZERO [Var c] [d]]`]
        (Q.INST [`lo` |-> `0:num`] (SPEC_ALL inst_seq_ptr_uniform_append)))) >>
      simp[mk_inst_def, is_terminator_def] >>
      qexistsl_tac [`H2`,`tn2`] >> simp[GSYM mk_inst_def]) >>
  simp[]
QED

Theorem scalar_double_check_certificate:
  MEM opc1 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  MEM opc2 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq
    [mk_inst id opc1 [x; Lit lo] [a]; mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) opc2 [x; Lit hi] [c]; mk_inst (id+3) ISZERO [Var c] [d];
     mk_inst (id+4) AND [Var b; Var d] [e]; mk_inst (id+5) ASSERT [Var e] []] s = OK t \/
   run_inst_seq
    [mk_inst id opc1 [x; Lit lo] [a]; mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) opc2 [x; Lit hi] [c]; mk_inst (id+3) ISZERO [Var c] [d];
     mk_inst (id+4) AND [Var b; Var d] [e]; mk_inst (id+5) ASSERT [Var e] []] s = Abort err t) ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id opc1 [x; Lit lo] [a]; mk_inst (id+1) ISZERO [Var a] [b];
       mk_inst (id+2) opc2 [x; Lit hi] [c]; mk_inst (id+3) ISZERO [Var c] [d];
       mk_inst (id+4) AND [Var b; Var d] [e]; mk_inst (id+5) ASSERT [Var e] []] s H th /\
    op_prov H x = NONE /\ op_taint th x = {} /\
    (!p. ~MEM p [a;b;c;d;e] ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all scalar_double_check_prefix_runs >> strip_tac >>
  drule_all scalar_double_checked_prefix >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >> reverse conj_tac
  >- (simp[] >> metis_tac[]) >>
  irule (PURE_REWRITE_RULE [APPEND] (Q.INST
    [`xs` |-> `[mk_inst id opc1 [x; Lit lo] [a];
     mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) opc2 [x; Lit hi] [c];
     mk_inst (id+3) ISZERO [Var c] [d];
     mk_inst (id+4) AND [Var b; Var d] [e]]`]
    (Q.INST [`id` |-> `id+5`] (SPEC_ALL checked_prefix_assert_certificate)))) >>
  imp_res_tac convert_scalar_opcode_filter >>
  simp[GSYM mk_inst_def, is_terminator_def] >>
  qexistsl_tac [`w`,`value`] >> simp[] >>
  qpat_x_assum `_ \/ _` kall_tac >>
  qpat_x_assum `MEM opc1 _` kall_tac >>
  qpat_x_assum `MEM opc2 _` kall_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem int_clamp_signed_fixed_certificate:
  compile_int_clamp T bits x sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq (emitted_insts sa sb) s = OK t \/
   run_inst_seq (emitted_insts sa sb) s = Abort err t) ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule int_clamp_signed_code >> strip_tac >> gnvs[] >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.INST
    [`opc1` |-> `SLT`, `opc2` |-> `SGT`] (SPEC_ALL scalar_double_check_certificate))) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >> simp[] >> metis_tac[]
QED

Theorem int_clamp_fixed_certificate:
  compile_int_clamp signed bits x sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq (emitted_insts sa sb) s = OK t \/
   run_inst_seq (emitted_insts sa sb) s = Abort err t) ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  Cases_on `signed`
  >- MATCH_ACCEPT_TAC int_clamp_signed_fixed_certificate >>
  MATCH_ACCEPT_TAC int_clamp_unsigned_fixed_certificate
QED

Theorem int_clamp_instruction_filter:
  compile_int_clamp signed bits x sa = (out,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  strip_tac >> Cases_on `signed`
  >- (drule int_clamp_signed_code >> strip_tac >>
      simp[mk_inst_def, is_terminator_def]) >>
  drule int_clamp_unsigned_code >> strip_tac >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem int_clamp_counted_certificate:
  compile_int_clamp signed bits x sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule_all (cj 1 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM] int_clamp_fixed_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >> simp[] >>
  drule int_clamp_instruction_filter >> strip_tac >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem int_clamp_abort_counted_certificate:
  compile_int_clamp signed bits x sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th n j.
    gas_path_ptr D 0 ctx fn PG G tn s n H th
      (Abort err (t with vs_inst_idx := j)) /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule_all (cj 2 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM] int_clamp_fixed_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  drule int_clamp_instruction_filter >> strip_tac >>
  drule_all run_inst_seq_abort_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`H`,`th`,`n`,`j`] >> simp[]
QED
