(* Separation belongs to the actual allocation endpoint, including reused sites. *)
Theory assignBasePtrAllocSeparate
Ancestors assignBasePtrAllocCounted exprSimAlloc exprLoweringProps
  assignBasePtrLiteralGhost assignBasePtrLiteralSource context emitHelper
  emitHelperProps compileEnv venomExecSemantics venomState venomInst
  finite_map words fragExecPtr allocationPtr rich_list fragGasSeqPtr
  assignBasePtrLiteralOutcome ghostPcTransportPtr instIdxIndep fragExec

Theorem assign_base_ptr_alloca_map_frame:
  !s t id n out aid.
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
    aid <> id ==>
    FLOOKUP t.vs_allocas aid = FLOOKUP s.vs_allocas aid
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >> simp[] >> strip_tac >> gvs[] >>
  simp[update_var_def, FLOOKUP_UPDATE] >>
  PairCases_on `x` >> gvs[update_var_def]
QED

Theorem assign_base_ptr_alloc_buffer_endpoint_separation:
  !ctx func cenv cx es sa sm buf sz s t a.
    compile_alloc_buffer sz sa = (buf,sm) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
    run_inst_seq (emitted_insts sa sm) s = OK t /\
    eval_operand buf.buf_operand t = SOME a ==>
    (!name b len. local_region cenv es.scopes t name b len ==>
      regions_disjoint (w2n a) sz b len) /\
    (!aid b len. FLOOKUP t.vs_allocas aid = SOME (b,len) /\
      aid < sa.cs_next_id ==> regions_disjoint (w2n a) sz b len)
Proof
  rpt gen_tac >> strip_tac >> drule_all literal_alloc_buffer_run >> strip_tac >>
  gvs[] >> conj_tac >- metis_tac[] >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()] >> rpt gen_tac >> strip_tac >>
  `FLOOKUP t.vs_allocas aid = FLOOKUP s.vs_allocas aid` by
    (irule assign_base_ptr_alloca_map_frame >>
     goal_assum (drule_at Any) >> decide_tac) >> metis_tac[]
QED

Theorem assign_base_alloca_existing_map_frame:
  !s t id n out aid site.
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
    FLOOKUP s.vs_allocas aid = SOME site ==>
    FLOOKUP t.vs_allocas aid = SOME site
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >> simp[] >> strip_tac >> gvs[]
  >- (simp[update_var_def, FLOOKUP_UPDATE] >>
      Cases_on `aid = id` >> gvs[]) >>
  PairCases_on `x` >> gvs[update_var_def]
QED

Theorem assign_base_alloc_buffer_run_frames:
  !sa sm buf sz s t cenv es ix.
    compile_alloc_buffer sz sa = (buf,sm) /\
    run_inst_seq (emitted_insts sa sm) s = OK t /\
    not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var)) ==>
    (!aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
      FLOOKUP (t with vs_inst_idx := ix).vs_allocas aid = SOME site) /\
    (!name b len. local_region cenv es.scopes s name b len <=>
      local_region cenv es.scopes (t with vs_inst_idx := ix) name b len)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()] >> conj_tac
  >- metis_tac[assign_base_alloca_existing_map_frame] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >> simp[] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  simp[local_region_def, lookup_var_update_var] >>
  fs[not_local_ptr_def] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt gen_tac >> eq_tac >> strip_tac >>
  `STRING #"%" (toString sa.cs_next_var) <> p` by metis_tac[] >>
  qexistsl_tac [`entry`, `p`, `w`] >> gvs[]
QED

Theorem assign_base_ptr_alloc_buffer_counted_separated:
  !ctx func d cenv cx es sa sm buf sz s PG G tn D frame_sa
    ty va vb v op tv w.
    compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ghost_inv d cenv cx es G tn s /\
    not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var)) /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==>
      x <> STRING #"%" (toString sa.cs_next_var)) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==>
      x <> STRING #"%" (toString sa.cs_next_var)) /\
    (!x. not_fresh_at frame_sa x ==>
      x <> STRING #"%" (toString sa.cs_next_var)) /\
    frame_sa.cs_next_id <= sa.cs_next_id /\
    expr_val_at cenv cx ty va vb es v op s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    eval_operand op s = SOME w /\ op <> buf.buf_operand /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n w) m) ==>
    ?u a G' tn'.
      gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK u) /\
      stmt_state_rel ctx func cenv cx es u /\ ~u.vs_halted /\
      eval_operand buf.buf_operand u = SOME a /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n a,sz) /\
      w2n a + sz < dimword (:256) /\
      u.vs_current_bb = sm.cs_current_bb /\
      u.vs_inst_idx = LENGTH sm.cs_current_insts /\
      (?p. buf.buf_operand = Var p /\ ptr_covers G' tn' p u sz) /\
      (!p k. buf.buf_operand <> Var p /\ ptr_covers G tn p s k ==>
        ptr_covers G' tn' p u k) /\
      (!q. q <> buf.buf_operand ==> eval_operand q u = eval_operand q s) /\
      ghost_inv d cenv cx es G' tn' u /\
      ghost_kept cenv es frame_sa G tn s G' tn' /\
      eval_operand op u = SOME w /\
      (!m. mem_agree_outside tn'.t_mem u.vs_memory m ==>
        val_in_memory tv v (w2n w) m) /\
      (!name b len. local_region cenv es.scopes u name b len ==>
        regions_disjoint (w2n a) sz b len) /\
      (!aid b len. FLOOKUP u.vs_allocas aid = SOME (b,len) /\
        aid < frame_sa.cs_next_id ==> regions_disjoint (w2n a) sz b len) /\
      (!aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
        FLOOKUP u.vs_allocas aid = SOME site) /\
      (!name b len. local_region cenv es.scopes s name b len <=>
        local_region cenv es.scopes u name b len)
Proof
  rpt strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all assign_base_ptr_alloc_buffer_sequence_full >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all assign_base_ptr_alloc_buffer_endpoint_separation >> strip_tac >>
  drule_all assign_base_alloc_buffer_run_frames >>
  disch_then (qspec_then `LENGTH sm.cs_current_insts` strip_assume_tac) >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `cs'.cs_current_bb = sa.cs_current_bb` by
    (gvs[emit_op_def, comp_bind_def, comp_return_def, comp_ignore_bind_def,
         fresh_id_def, fresh_var_def, emit_def]) >>
  `~t.vs_halted` by
    (gvs[run_inst_seq_def, AllCaseEqs()] >>
     qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >> simp[] >>
     strip_tac >> gvs[AllCaseEqs(), update_var_def]) >>
  `t.vs_current_bb = s.vs_current_bb` by suspend "control" >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `isPREFIX (emitted_insts sa cs') (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[DROP_APPEND1] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa cs')` by simp[mk_inst_def, is_terminator_def] >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    run_inst_seq_gas_path_ptr >>
  disch_then (qspecl_then [`t`, `bb`] mp_tac) >>
  simp[mk_inst_def, stmt_state_rel_inst_idx, DROP_APPEND1, is_terminator_def] >>
  strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sa.cs_current_insts + 1`,
               `a`, `G'`, `tn'`] >>
  simp[stmt_state_rel_inst_idx, assign_base_ptr_ghost_index] >> conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` irule >>
      fs[local_region_def, lookup_var_def] >> metis_tac[]) >>
  rpt strip_tac >> qpat_x_assum `!aid b len. _` irule >>
  goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

Resume assign_base_ptr_alloc_buffer_counted_separated[control]:
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  `step_inst 0 ctx
     (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  drule venomInstProofsTheory.step_preserves_control_flow >>
  simp[mk_inst_def, is_terminator_def]
QED

Finalise assign_base_ptr_alloc_buffer_counted_separated
