(* Ghost frame for the payload-copy instruction; independent of the ABI type. *)
Theory calldataBulkPayloadPtr
Ancestors calldataDecodePtr decoderNavigationPtr calldataBulkLive
  bodyPtrDefs ptrDiscipline venomInst venomState finite_map pred_set
  decoderGhostFramePtr emitHelperProps fragExec venomExecSemantics
  codegenRel contextCodegenRel ptrSafeRun compileEnv emitHelper list arithmetic
  exprLoweringProps

Theorem calldatacopy_ghost_frame:
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  eval_operand n s = SOME nw /\
  t = write_memory_with_expansion (w2n dw)
    (TAKE (w2n nw)
      (DROP (w2n sw) s.vs_call_ctx.cc_calldata ++ REPLICATE (w2n nw) 0w)) s ==>
  (!root cap. ptr_covers G tn root s cap ==>
    ptr_covers (step_prov PG G (mk_inst id CALLDATACOPY [dst;src;n] []) t)
      (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s t tn) root t cap) /\
  (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s t tn).t_mem
    SUBSET tn.t_mem /\
  (!i. w2n dw <= i /\ i < w2n dw + w2n nw ==>
    i NOTIN (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s t tn).t_mem) /\
  (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s t tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s t tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s t tn).t_imm = tn.t_imm /\
  (!x. lookup_var x t = lookup_var x s /\
    FLOOKUP (step_prov PG G (mk_inst id CALLDATACOPY [dst;src;n] []) t) x = FLOOKUP G x /\
    op_taint (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s t tn) (Var x) =
      op_taint tn (Var x)) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[ptr_covers_def, step_prov_def, step_taint_def, set_prov_def,
        set_var_taint_def, mk_inst_def, op_taint_def, FLOOKUP_DRESTRICT, lookup_var_def,
        write_memory_with_expansion_def, write_memory_def, expand_memory_def])
  >- (`new_site_bytes s t = {}` by
        (gvs[new_site_bytes_def, write_memory_with_expansion_def,
          write_memory_def, expand_memory_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
      `written_taint tn (mk_inst id CALLDATACOPY [dst;src;n] []) s = {}` by
        simp[written_taint_def, mk_inst_def] >>
      mp_tac (Q.INST [`R` |-> `{}:num set`,
        `inst` |-> `mk_inst id CALLDATACOPY [dst;src;n] []`]
        step_taint_memory_bound) >> simp[])
  >- (metis_tac[calldatacopy_written_range_clean])
  >- simp[calldatacopy_nonmemory_taint]
  >- simp[calldatacopy_nonmemory_taint]
  >- simp[calldatacopy_nonmemory_taint]
  >- (gvs[step_prov_def, step_taint_def, set_prov_def, set_var_taint_def,
        mk_inst_def, op_taint_def, FLOOKUP_DRESTRICT, lookup_var_def,
        write_memory_with_expansion_def, write_memory_def, expand_memory_def])
  >> gvs[write_memory_with_expansion_def, write_memory_def, expand_memory_def]
QED

Theorem emit_calldatacopy_endpoint_ptr:
  emit_void CALLDATACOPY [Var p;src;n] sa = ((),sb) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  eval_operand n s = SOME nw /\ ptr_covers G tn p s (w2n nw) /\
  op_taint tn src = {} /\ op_taint tn n = {} /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u.
    (!root cap. ptr_covers G tn root s cap ==> ptr_covers H u root t cap) /\
    u.t_mem SUBSET tn.t_mem /\
    (!i. w2n dw <= i /\ i < w2n dw + w2n nw ==> i NOTIN u.t_mem) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!D lower ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx func PG H u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn s)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_void_same_blocks >> simp[same_blocks_def]) >>
  `t = write_memory_with_expansion (w2n dw)
    (TAKE (w2n nw)
      (DROP (w2n sw) s.vs_call_ctx.cc_calldata ++ REPLICATE (w2n nw) 0w)) s` by
    gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def] >>
  drule_all calldatacopy_ghost_frame >>
  disch_then (qspecl_then [`tn`,`sa.cs_next_id`,`PG`,`G`] strip_assume_tac) >>
  qexistsl_tac [
    `step_prov PG G (mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []) t`,
    `step_taint (mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []) s t tn`] >>
  simp[] >> rpt strip_tac >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    !k. k < LENGTH [mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []] ==>
      get_instruction bb (LENGTH sa.cs_current_insts + k) =
        SOME (EL k [mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []])` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >> simp[]) >>
  irule calldatacopy_safe_continuation >> simp[] >>
  qexistsl_tac [`dw`,`sa.cs_next_id`,`n`,`nw`,`p`,`src`,`sw`] >>
  simp[ADD1] >> conj_tac
  >- fs[ptr_covers_def] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED
