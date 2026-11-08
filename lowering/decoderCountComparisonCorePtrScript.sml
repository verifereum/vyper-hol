(* The count-bound comparison threads one deterministic ghost. *)
Theory decoderCountComparisonCorePtr
Ancestors wordLoadStorePtr decoderCountLoadCorePtr decoderSetupStepPtr decoderNavigationPtr
  calldataClampPtr typedCopyPtr bodyPtrDefs compileEnv emitHelper venomInst
  venomExecSemantics venomState words list rich_list arithmetic finite_map
  ptrDiscipline ptrSafeRun venomInstProofs codegenRel contextCodegenRel
  emitHelperProps exprLoweringProps fragExec decoderGhostFramePtr
  abiDecoderContract entryDispatchPtr instIdxIndep fragExecPtr

Theorem emit_count_comparison_endpoint_ptr_core:
  !src bound sa out sb s t a G tn cx ctx PG R.
  emit_op GT [src; Lit bound] sa = (out,sb) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u. frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\
        v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\
    op_taint u out = {} /\ op_prov H out = NONE /\
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
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  qabbrev_tac `out = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id GT [src; Lit bound] [out]` >>
  `t = update_var out (bool_to_word (w2n a > w2n bound)) s` by
    (qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
     qpat_x_assum `eval_operand src s = SOME a` mp_tac >>
     simp[Abbr `out`] >> POP_ASSUM_LIST (K all_tac) >>
     strip_tac >>
     simp[run_inst_seq_def] >>
     simp[step_inst_base_def, mk_inst_def, exec_pure2_def,
          eval_operand_def] >> rpt strip_tac >> gvs[]) >>
  `step_inst_base inst s = OK t` by
    (simp[Abbr `inst`, step_inst_base_def, mk_inst_def,
      exec_pure2_def] >> Cases_on `src` >> gvs[eval_operand_def]) >>
  `!D lower fuel ctx' fn. allocas_from lower s /\ ~ctx_has_dalloca ctx' ==>
    ptr_inst_ok D lower fuel ctx' fn G tn inst s` by
    (rpt strip_tac >>
     `op_taint tn (Lit bound) = {}` by simp[op_taint_def] >>
     qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       Abbr `inst`, mk_inst_def, step_inst_non_invoke,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       update_var_def] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> metis_tac[LESS_EQ_REFL]) >>
  qabbrev_tac `H = step_prov PG G inst t` >>
  qabbrev_tac `u = step_taint inst s t tn` >>
  `frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\ v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R` by
    (irule ptr_fragment_step >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
     rpt strip_tac >>
     qexists_tac `update_var out (bool_to_word (w2n a > w2n bound)) s` >>
     simp[Abbr `H`, Abbr `u`] >>
     `allocas_from 0 s` by simp[allocas_from_def] >>
     gvs[update_var_def, mk_inst_def, Abbr `out`] >> metis_tac[]) >>
  `!D lower ctx' func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx' /\
      s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG H u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn s` by
    (rpt gen_tac >> strip_tac >>
     `!fuel. ptr_inst_ok D lower fuel ctx' func G tn inst s` by metis_tac[] >>
     irule setup_instruction_continuation >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     simp[Abbr `H`, Abbr `u`, Abbr `inst`, Abbr `out`, mk_inst_def,
       is_terminator_def, update_var_def]) >>
  qexistsl_tac [`H`,`u`] >> simp[] >>
  simp[Abbr `H`, Abbr `u`, Abbr `inst`, Abbr `out`,
    lookup_var_def,
    op_prov_def, step_prov_def, out_prov_def, set_prov_def,
    op_taint_def, step_taint_def, out_taint_def, set_var_taint_def,
    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, mk_inst_def,
    mem_taint_def, new_site_bytes_def, step_writes_def,
    written_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
    update_var_def, source_memory_write_ranges_def, range_bytes_def,
    pred_setTheory.EXTENSION, FDOM_DRESTRICT, SF CONJ_ss] >>
  simp[FLOOKUP_DEF, SF CONJ_ss] >>
  conj_tac >- (qexists_tac `t.vs_vars` >> simp[update_var_def]) >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` (assume_tac o SRULE []) >>
  gen_tac >> disch_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by metis_tac[] >>
  simp[FLOOKUP_DEF, SF CONJ_ss]
QED
