(* Scalar guard validation at a common ghost endpoint. *)
Theory decoderGuardClampCorePtr
Ancestors wordLoadStorePtr decoderCountComparisonCorePtr decoderSetupStepPtr calldataClampPtr
  decoderNavigationPtr typedCopyPtr bodyPtrDefs compileEnv emitHelper venomInst
  venomExecSemantics venomState words list rich_list arithmetic finite_map
  ptrDiscipline ptrSafeRun venomInstProofs codegenRel contextCodegenRel
  emitHelperProps exprLoweringProps fragExec decoderGhostFramePtr
  abiDecoderContract entryDispatchPtr instIdxIndep fragExecPtr

Theorem clamp_scalar_frag_ptr:
  MEM opc [SIGNEXTEND; SHR; SHL; EQ; ISZERO; ASSERT] /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ [mk_inst id opc ops outs] /\
  EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) ops /\
  step_inst_base (mk_inst id opc ops outs) s = OK t ==>
  frag_exec_ptr cx ctx PG sa sb
    (\g z v. g = G /\ z = tn /\ v = s)
    (\g z v. g = step_prov PG G (mk_inst id opc ops outs) t /\
      z = step_taint (mk_inst id opc ops outs) s t tn /\
      v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R
Proof
  strip_tac >>
  `?vars. t = s with vs_vars := vars` by
    metis_tac[clamp_scalar_state_frame] >>
  `opc <> INVOKE /\ ~is_terminator opc` by fs[MEM, is_terminator_def] >>
  irule ptr_fragment_step >> simp[mk_inst_def] >>
  rpt strip_tac >> qexists_tac `t` >>
  simp[GSYM mk_inst_def] >> rpt strip_tac >>
  `allocas_from 0 s` by simp[allocas_from_def] >>
  `ptr_safe_step (cx_dead cx) 0 fuel ctx fn PG G tn
     (mk_inst id opc ops outs) s` by
    (irule clamp_scalar_step_safe >> simp[step_inst_non_invoke, mk_inst_def] >>
     fs[MEM]) >>
  gvs[ptr_safe_step_def, mk_inst_def]
QED

Theorem emit_clamp_scalar_endpoint_ptr_core:
  emit_op opc ops sa = (out,sb) /\
  MEM opc [SIGNEXTEND; SHR; SHL; EQ; ISZERO] /\
  EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) ops /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u. op_taint u out = {} /\ op_prov H out = NONE /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\
        v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (?vars. t = s with vs_vars := vars) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower ctx' func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx' /\
      s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG H u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  `step_inst_base (mk_inst sa.cs_next_id opc ops
     ["%" ++ toString sa.cs_next_var]) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `MEM opc [SIGNEXTEND; SHR; SHL; EQ; ISZERO; ASSERT]` by fs[MEM] >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id opc ops
    ["%" ++ toString sa.cs_next_var]` >>
  `opc <> INVOKE /\ ~is_terminator opc` by fs[MEM, is_terminator_def] >>
  `!D lower ctx' func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx' /\
      s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG
        (step_prov PG G inst t) (step_taint inst s t tn)
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn s` by
    (rpt gen_tac >> strip_tac >>
     `?vars. t = s with vs_vars := vars` by metis_tac[clamp_scalar_state_frame] >>
     `!fuel. ptr_inst_ok D lower fuel ctx' func G tn inst s` by
       (gen_tac >> simp[Abbr `inst`] >>
        irule (cj 1 (SRULE [ptr_safe_step_def] clamp_scalar_step_safe)) >>
        simp[step_inst_non_invoke, mk_inst_def] >>
        reverse conj_tac >- fs[MEM] >>
        qexists_tac `t` >> gvs[step_inst_non_invoke, mk_inst_def]) >>
     irule setup_instruction_continuation >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     simp[Abbr `inst`, mk_inst_def, update_var_def, is_terminator_def] >>
     fs[MEM, is_terminator_def]) >>
  qexistsl_tac [`step_prov PG G inst t`, `step_taint inst s t tn`] >> simp[] >>
  `EVERY (\op. op_taint tn op = {}) ops` by gvs[EVERY_MEM] >>
  conj_tac >- (simp[Abbr `inst`] >> metis_tac[clamp_scalar_output_ghost]) >>
  conj_tac >- (simp[Abbr `inst`] >> metis_tac[clamp_scalar_output_ghost]) >>
  conj_tac >- (simp[Abbr `inst`] >> irule clamp_scalar_frag_ptr >> gvs[]) >>
  `(!x. not_fresh_at sa x ==> x <> "%" ++ toString sa.cs_next_var)` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[Abbr `inst`] >>
  qpat_x_assum `step_inst_base _ _ = _` (assume_tac o SRULE []) >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` (assume_tac o SRULE []) >>
  drule_all clamp_scalar_state_frame >> strip_tac >>
  drule_all clamp_scalar_taint_frame >> strip_tac >> simp[] >>
  conj_tac >- metis_tac[] >> gen_tac >> disch_tac >>
  `x <> "%" ++ toString sa.cs_next_var` by (simp[] >> metis_tac[]) >>
  conj_tac >- (metis_tac[clamp_scalar_lookup_frame, MEM]) >>
  qpat_x_assum `x <> _` (assume_tac o SRULE []) >>
  simp[mk_inst_def] >> simp[step_prov_other_output, step_taint_other_output]
QED

Theorem emit_assert_endpoint_ptr_core:
  emit_void ASSERT [op] sa = ((),sb) /\
  op_taint tn op = {} /\ op_prov G op = NONE /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  frag_exec_ptr cx ctx PG sa sb
    (\g z v. g = G /\ z = tn /\ v = s)
    (\g z v. g = G /\ z = tn /\
      v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\ t = s /\
  (!D lower ctx' func.
    fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx' /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!fuel. ptr_safe_run D lower fuel ctx' func PG G tn
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
    !fuel. ptr_safe_run D lower fuel ctx' func PG G tn s)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_void_same_blocks >> simp[same_blocks_def]) >>
  `step_inst_base (mk_inst sa.cs_next_id ASSERT [op] []) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `t = s` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, AllCaseEqs()] >> metis_tac[]) >>
  `step_prov PG G (mk_inst sa.cs_next_id ASSERT [op] []) t = G /\
   step_taint (mk_inst sa.cs_next_id ASSERT [op] []) s t tn = tn` by
    simp[step_prov_def, set_prov_def, step_taint_def, set_var_taint_def,
      mk_inst_def, adopt_reset_def, store_taint_def, imm_taint_def,
      mem_taint_def, new_site_bytes_def, step_writes_def,
      source_memory_write_ranges_def, range_bytes_def,
      taint_component_equality, pred_setTheory.EXTENSION,
      written_taint_def, FDOM_DRESTRICT, DRESTRICT_UNIV, FLOOKUP_DEF,
      SF CONJ_ss] >>
  conj_tac
  >- (`MEM ASSERT [SIGNEXTEND; SHR; SHL; EQ; ISZERO; ASSERT] /\
       EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) [op]` by simp[] >>
      drule_all clamp_scalar_frag_ptr >>
      disch_then (qspecl_then [`cx`,`ctx`,`R`,`PG`] mp_tac) >> simp[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `!fuel. ptr_inst_ok D lower fuel ctx' func G tn
    (mk_inst sa.cs_next_id ASSERT [op] []) s` by
    (gen_tac >>
     irule (cj 1 (SRULE [ptr_safe_step_def] clamp_scalar_step_safe)) >>
     simp[step_inst_non_invoke, mk_inst_def] >>
     qexists_tac `s` >> gvs[step_inst_non_invoke, mk_inst_def]) >>
  irule setup_instruction_continuation >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  simp[mk_inst_def, is_terminator_def] >>
  qexists_tac `sb` >> gvs[mk_inst_def]
QED
