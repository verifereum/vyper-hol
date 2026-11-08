(* Count loads expose a common fragment/continuation ghost. *)
Theory decoderCountLoadCorePtr
Ancestors wordLoadStorePtr decoderSetupStepPtr decoderNavigationPtr calldataClampPtr typedCopyPtr
  bodyPtrDefs compileEnv emitHelper venomInst venomExecSemantics venomState
  words list rich_list arithmetic finite_map ptrDiscipline ptrSafeRun
  venomInstProofs codegenRel contextCodegenRel emitHelperProps exprLoweringProps
  fragExec decoderGhostFramePtr abiDecoderContract entryDispatchPtr instIdxIndep fragExecPtr

Theorem emit_count_load_endpoint_ptr_core:
  !src sa out sb s t a G tn cx ctx PG R.
  emit_op CALLDATALOAD [src] sa = (out,sb) /\
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
  qabbrev_tac `inst = mk_inst sa.cs_next_id CALLDATALOAD [src] [out]` >>
  `t = update_var out (abi_decode_load CALLDATALOAD a s) s` by
    gvs[run_inst_seq_def, Abbr `out`, step_inst_base_def, mk_inst_def,
      exec_read1_def, abi_decode_load_def, abi_decode_source_def] >>
  qabbrev_tac `H = step_prov PG G inst t` >>
  qabbrev_tac `u = step_taint inst s t tn` >>
  `frag_exec_ptr cx ctx PG sa sb
    (\g z v. g = G /\ z = tn /\ v = s)
    (\g z v. g = H /\ z = u /\ v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R` by
    (irule ptr_fragment_step >> simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
     rpt strip_tac >> qexists_tac `update_var out (abi_decode_load CALLDATALOAD a s) s` >>
     simp[Abbr `H`, Abbr `u`, Abbr `out`, mk_inst_def,
       step_inst_base_def, exec_read1_def, abi_decode_load_def,
       abi_decode_source_def, update_var_def] >>
     rpt strip_tac >>
     irule (cj 1 (SRULE [ptr_safe_step_def, mk_inst_def] ptr_safe_dispatch_scalar_step)) >>
     simp[allocas_from_def] >>
     qexists_tac `update_var (STRING #"%" (toString sa.cs_next_var)) (abi_decode_load CALLDATALOAD a s) s` >>
     simp[mk_inst_def, step_inst_non_invoke,
       step_inst_base_def, exec_read1_def, abi_decode_load_def,
       abi_decode_source_def, update_var_def]) >>
  `!D lower ctx' func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx' /\
      s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG H u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn s` by
    (rpt gen_tac >> strip_tac >>
      `step_inst_base inst s = OK t` by
        (simp[Abbr `inst`, mk_inst_def, step_inst_base_def,
          exec_read1_def, abi_decode_load_def, abi_decode_source_def]) >>
      `!fuel. ptr_inst_ok D lower fuel ctx' func G tn inst s` by
        (gen_tac >> simp[Abbr `inst`] >>
         irule (cj 1 (SRULE [ptr_safe_step_def] ptr_safe_dispatch_scalar_step)) >>
         simp[mk_inst_def, step_inst_non_invoke, update_var_def] >>
         qexists_tac `t` >> simp[mk_inst_def, step_inst_non_invoke, update_var_def]) >>
      irule setup_instruction_continuation >>
      goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >>
      qexists_tac `sa` >>
      simp[Abbr `H`, Abbr `u`, Abbr `inst`, Abbr `out`, mk_inst_def,
        is_terminator_def, update_var_def]) >>
  qexistsl_tac [`H`, `u`] >> simp[] >>
  conj_tac >-
    (simp[Abbr `u`, Abbr `inst`, Abbr `out`] >>
     irule dispatch_scalar_output_clean >> simp[]) >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> metis_tac[LESS_EQ_REFL]) >>
  simp[Abbr `H`, Abbr `u`, Abbr `inst`, Abbr `out`,
    op_prov_def, step_prov_def, out_prov_def, set_prov_def,
    op_taint_def, step_taint_def, out_taint_def, set_var_taint_def,
    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, mk_inst_def,
    mem_taint_def, new_site_bytes_def, step_writes_def,
    written_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
    update_var_def, lookup_var_def, source_memory_write_ranges_def, range_bytes_def,
    pred_setTheory.EXTENSION, FDOM_DRESTRICT, SF CONJ_ss] >>
  simp[FLOOKUP_DEF, SF CONJ_ss] >>
  conj_tac >- (qexists_tac `t.vs_vars` >> simp[update_var_def]) >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` (assume_tac o SRULE []) >>
  gen_tac >> disch_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by metis_tac[] >>
  simp[FLOOKUP_DEF, SF CONJ_ss]
QED
