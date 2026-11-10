(* Scratch staging keeps its counted endpoint, representation and ghost together. *)
Theory assignBasePtrStaging
Ancestors assignBasePtrAllocSeparate assignBasePtrCopyFrame
  assignBasePtrMcopyGhost wordArgsPtr typedMemoryCopy bodyPtrDefs
  venomState venomExecSemantics venomInst context compileEnv loweringStateRelDefs
  ghostPcTransportPtr assignBasePtrLiteralOutcome fragGasPathPtr
  exprSimAlloc words finite_map allocationPtr valueEncoding valueEncodingDefs emitHelper emitHelperProps
  exprLoweringProps fragExecPtr fragExec exprSimBufferStore typedCopyPtr ptrDiscipline

Theorem assign_base_scratch_copy_framed_ptr:
  !dst src n sa sb fn s b a G tn D ctx PG tv v kind cenv cx es frame_sa.
    n < dimword (:256) /\
    compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\ ptr_covers G tn dst s n /\
    ptr_covers G tn src s n /\
    lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
    val_wf tv v /\ val_footprint tv v <= n /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n a) m) /\
    local_ptrs_rel fn cenv es.scopes s /\ ghost_inv kind cenv cx es G tn s /\
    (!name base sz. local_region cenv es.scopes s name base sz ==>
      regions_disjoint (w2n b) n base sz) /\
    (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
      aid < frame_sa.cs_next_id ==>
      regions_disjoint (w2n b) n off sz) ==>
    ?Gf tf u. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u = (if n = 0 then s else
        mcopy (w2n b) (w2n a) n s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      typed_copy_state_frame sa (w2n b) n s u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      u.vs_prev_bb = s.vs_prev_bb /\ ptr_covers Gf tf dst u n /\
      (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
        val_in_memory tv v (w2n b) m) /\
      ghost_inv kind cenv cx es Gf tf u /\
      ghost_kept cenv es frame_sa G tn s Gf tf /\
      u.vs_allocas = s.vs_allocas /\
      (!q. eval_operand q u = eval_operand q s) /\
      (!name base sz. local_region cenv es.scopes u name base sz <=>
        local_region cenv es.scopes s name base sz)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `n = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      qexistsl_tac [`G`, `tn`] >>
      simp[cj 1 gas_path_ptr_rules, ghost_kept_refl] >>
      rpt strip_tac >> irule valueCopyTheory.val_in_memory_relocate >> simp[] >>
      qexistsl_tac [`w2n a`, `0`, `m`] >> simp[mem_bytes_at_def]) >>
  `0 < n` by decide_tac >>
  `sa.cs_current_bb = sb.cs_current_bb` by
    (drule buffer_copy_memory_shape >> simp[same_blocks_def]) >>
  `!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
    aid < frame_sa.cs_next_id /\
    (!name base len. local_region cenv es.scopes s name base len ==>
      off + sz <= base \/ base + len <= off) ==>
    regions_disjoint (w2n b) n off sz` by metis_tac[] >>
  drule_all (SRULE [] assign_base_copy_memory_ghost_endpoint_ptr) >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> conj_tac >- simp[typed_copy_mcopy_state_frame] >>
  simp[eval_operand_def, lookup_var_def, local_region_def,
       mcopy_def, write_memory_with_expansion_def] >>
  conj_tac
  >- (fs[ptr_covers_def, step_prov_def, set_prov_def, out_prov_def,
         step_taint_def, set_var_taint_def, mk_inst_def, op_taint_def,
         DRESTRICT_UNIV, mcopy_def, write_memory_with_expansion_def,
         lookup_var_def]) >>
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem assign_base_alloc_scratch_staging_ptr:
  !ctx fn kind cenv cx es sa sm sb buf n s PG G tn D frame_sa
    ty va vb v src dst tv w.
    compile_alloc_buffer n sa = (buf,sm) /\ buf.buf_operand = Var dst /\
    compile_copy_memory (Var dst) (Var src) n sm = ((),sb) /\
    fn_has_code sa sm fn /\ fn_has_code sm sb fn /\
    stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved cenv sa /\ n < dimword (:256) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ghost_inv kind cenv cx es G tn s /\
    not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var)) /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==>
      x <> STRING #"%" (toString sa.cs_next_var)) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==>
      x <> STRING #"%" (toString sa.cs_next_var)) /\
    (!x. not_fresh_at frame_sa x ==>
      x <> STRING #"%" (toString sa.cs_next_var)) /\
    frame_sa.cs_next_id <= sa.cs_next_id /\
    expr_val_at cenv cx ty va vb es v (Var src) s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    eval_operand (Var src) s = SOME w /\ src <> dst /\
    ptr_covers G tn src s n /\ val_wf tv v /\ val_footprint tv v <= n /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n w) m) ==>
    ?u a Gi ti t Gf tf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gi ti (OK u) /\
      stmt_state_rel ctx fn cenv cx es u /\
      stmt_state_rel ctx fn cenv cx es t /\
      gas_path_ptr D 0 ctx fn PG Gi ti u 0 Gf tf (OK t) /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t) /\
      typed_copy_state_frame sm (w2n a) n u t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      t.vs_prev_bb = u.vs_prev_bb /\ ptr_covers Gf tf dst t n /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n a,n) /\
      w2n a + n < dimword (:256) /\
      eval_operand (Var dst) t = SOME a /\ eval_operand (Var src) t = SOME w /\
      (!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
        val_in_memory tv v (w2n a) m) /\
      ghost_inv kind cenv cx es Gf tf t /\
      ghost_kept cenv es frame_sa G tn s Gf tf /\
      t.vs_allocas = u.vs_allocas /\
      (!aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
        FLOOKUP t.vs_allocas aid = SOME site) /\
      (!q. q <> Var dst ==> eval_operand q t = eval_operand q s) /\
      (!name b len. local_region cenv es.scopes t name b len <=>
        local_region cenv es.scopes s name b len)
Proof
  rpt gen_tac >> strip_tac >>
  `Var src <> buf.buf_operand` by simp[] >>
  drule_all assign_base_ptr_alloc_buffer_counted_separated >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `local_ptrs_rel fn cenv es.scopes u` by fs[stmt_state_rel_def, state_rel_def] >>
  `ptr_covers G' tn' src u n` by metis_tac[] >>
  `ptr_covers G' tn' dst u n` by gvs[] >>
  `lookup_var src u = SOME w /\ lookup_var dst u = SOME a` by
    gvs[eval_operand_def] >>
  drule_all assign_base_scratch_copy_framed_ptr >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u')` by
    (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `ghost_kept cenv es frame_sa G tn s Gf tf` by
    (irule ghost_kept_trans >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn)` by
    (drule_all buffer_alloc_code >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx es u'` by
    (Cases_on `n = 0` >> gvs[] >> simp[stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_mcopy_alloca >> simp[] >>
     qexistsl_tac [`n`, `mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString sa.cs_next_var)]`,
       `STRING #"%" (toString sa.cs_next_var)`] >> simp[mk_inst_def]) >>
  qexistsl_tac [`u`, `a`, `G'`, `tn'`, `u'`, `Gf`, `tf`] >>
  simp[] >> gvs[eval_operand_def]
QED
