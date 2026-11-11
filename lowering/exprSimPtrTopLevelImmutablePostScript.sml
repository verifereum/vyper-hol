(* Clean immutable-copy buffers and retained ghost posts. *)
Theory exprSimPtrTopLevelImmutablePost
Ancestors exprSimPtrTopLevelImmutableRun exprSimPtrTopLevelImmutableCopy
  exprSimPtrTopLevelStorageAlloc exprSimStorageCopy ptrDiscipline
  fragGasPathPtr ghostPcTransportPtr fragExec rich_list
  exprSimPtrTopLevelStorageFrame exprSimPtrLiteralBuffer exprSimCopy
  bodyPtrDefs exprSimProps exprLoweringProps valueEncoding valueEncodingProps
  pred_set finite_map venomState words vyperAST vyperState exprLowering compileEnv loweringStateRelDefs

Theorem toplevel_immutable_full_copy_clean:
  immutable_copy_ghost_frame sa s G tn sb t H tm 0 nb w ==>
  (!i. w2n w <= i /\ i < w2n w+nb ==> i NOTIN tm.t_mem)
Proof
  simp[immutable_copy_ghost_frame_def] >> SET_TAC[]
QED

Theorem toplevel_immutable_alloc_copy_taint_subset:
  tn1.t_mem SUBSET tn.t_mem UNION {i | w2n w <= i /\ i < w2n w+nb} /\
  immutable_copy_ghost_frame sa s G1 tn1 sb t H tm 0 nb w ==>
  tm.t_mem SUBSET tn.t_mem
Proof
  simp[immutable_copy_ghost_frame_def] >> SET_TAC[]
QED

Theorem toplevel_immutable_clean_pointer_post:
  ~is_word_type ann /\ evaluate_type (get_tenv cx) ann = SOME tv /\
  lookup_var root t = SOME w /\ ptr_covers G tn root t nb /\
  val_wf tv v /\ val_in_memory tv v (w2n w) t.vs_memory /\
  val_store_size tv v <= nb /\ type_memory_bytes cenv ann <= nb /\
  (!i. w2n w <= i /\ i < w2n w+nb ==> i NOTIN tn.t_mem) ==>
  ptr_val_ok cx ann v (Var root) G tn t /\
  ptr_vv_ok cx ann (Value v) (StackValue ann (Var root)) es G tn t /\
  ptr_buf_ok cenv (TopLevelName ann nsid) (Var root) G t
Proof
  strip_tac >>
  `val_footprint tv v <= nb` by
    metis_tac[val_footprint_le_store_size, arithmeticTheory.LESS_EQ_TRANS] >>
  `!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem` by
    (rpt strip_tac >> irule literal_clean_representation_robust >> simp[] >>
     qexistsl_tac [`tn.t_mem`,`t.vs_memory`] >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  drule_all toplevel_storage_copy_pointer_post >>
  simp[ptr_vv_ok_def, read_result_def, vyperStateTheory.return_def]
QED

Theorem toplevel_immutable_alloc_copy_kept:
  (!x. not_fresh_at st x ==> not_fresh_at sa x /\
     FLOOKUP G1 x = FLOOKUP G x /\
     op_taint tn1 (Var x) = op_taint tn (Var x)) /\
  tn1.t_mem SUBSET tn.t_mem UNION {i | w2n w <= i /\ i < w2n w+nb} /\
  immutable_copy_ghost_frame sa s G1 tn1 sb t H tm 0 nb w ==>
  ghost_kept cenv es st G tn s0 H tm
Proof
  strip_tac >> irule literal_ghost_kept >> conj_tac
  >- (gvs[immutable_copy_ghost_frame_def] >> metis_tac[]) >>
  metis_tac[toplevel_immutable_alloc_copy_taint_subset]
QED

Theorem toplevel_immutable_alloc_copy_run:
  compile_alloc_buffer (32*n) sa = (buf,sm) /\
  compile_imm_copy_to_memory F imm (Lit a) buf.buf_operand n 0 sm = ((),sb) /\
  fn_has_code sa sm fn /\ fn_has_code sm sb fn /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ 32*n < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w Ga ta p t H tm.
    buf.buf_operand = Var p /\
    run_inst_seq (emitted_insts sa sm) s = OK u /\
    stmt_state_rel ctx fn cenv cx es u /\ u.vs_memory = s.vs_memory /\
    lookup_var p u = SOME w /\ lookup_var p t = SOME w /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ptr_covers H tm p t (32*n) /\
    immutable_copy_ghost_frame sm
      (u with vs_inst_idx := LENGTH sm.cs_current_insts) Ga ta sb t H tm 0 (32*n) w /\
    (!i. w2n w <= i /\ i < w2n w+32*n ==> i NOTIN tm.t_mem) /\
    tm.t_mem SUBSET tn.t_mem /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\
    (!name b len. local_region cenv es.scopes u name b len ==>
      regions_disjoint (w2n w) (32*n) b len)
Proof
  strip_tac >> drule_all toplevel_alloc_buffer_ptr_run >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  drule storage_copy_alloc_layout >> strip_tac >>
  `copy_old_operand sm (Lit a) /\
   (!x. not_fresh_at sa x ==> not_fresh_at sm x)` by
    (gvs[copy_old_operand_def, not_fresh_at_def] >> decide_tac) >>
  qabbrev_tac `s1 = u with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  `eval_operand (Lit a) s1 = SOME a /\ op_taint tnf (Lit a) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  `lookup_var p s1 = SOME w /\ ptr_covers Gf tnf p s1 (32*n)` by
    fs[Abbr `s1`, eval_operand_def, lookup_var_def] >>
  `compile_imm_copy_to_memory F imm (Lit a) (Var p) n 0 sm = ((),sb) /\
   0+32*n <= 32*n` by metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.ADD] >>
  drule_all toplevel_immutable_copy_frame >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
   same_blocks sm sb` by
    fs[immutable_copy_ghost_frame_def, copy_runtime_frame_def] >>
  `sb.cs_current_bb = sm.cs_current_bb` by fs[same_blocks_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `~s1.vs_halted /\ s1.vs_current_bb = sm.cs_current_bb /\
   s1.vs_inst_idx = LENGTH sm.cs_current_insts` by simp[Abbr `s1`] >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sm sb) (DROP s1.vs_inst_idx bb.bb_instructions)` by
    (simp[] >>
     qpat_x_assum `fn_has_code sm sb fn` mp_tac >>
     qpat_x_assum `sb.cs_current_insts = _` mp_tac >>
     qpat_x_assum `sb.cs_current_bb = _` mp_tac >>
     qpat_x_assum `lookup_block sm.cs_current_bb _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[fn_has_code_def] >> rpt strip_tac >> gvs[] >>
     qpat_x_assum `isPREFIX _ _` mp_tac >>
     rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >> qexists_tac `l` >>
     asm_rewrite_tac[] >> pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  drule_all toplevel_immutable_copy_counted_frontier >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  `(!i. w2n w <= i /\ i < w2n w+32*n ==> i NOTIN tm'.t_mem) /\
   tm'.t_mem SUBSET tn.t_mem` by
    metis_tac[toplevel_immutable_full_copy_clean,
      toplevel_immutable_alloc_copy_taint_subset] >>
  drule_all toplevel_alloc_buffer_static_effects >> strip_tac >>
  `t'.vs_call_ctx = s.vs_call_ctx /\ t'.vs_accounts = s.vs_accounts /\
   t'.vs_transient = s.vs_transient` by
    (gvs[immutable_copy_ghost_frame_def, copy_runtime_frame_def] >>
     drule copy_static_fields >> simp[Abbr `s1`, copy_static_def]) >>
  qexistsl_tac [`w`,`Gf`,`tnf`,`t'`,`H'`,`tm'`] >>
  fs[Abbr `s1`, eval_operand_def, lookup_var_def] >>
  gvs[immutable_copy_ghost_frame_def, copy_runtime_frame_def, lookup_var_def] >>
  metis_tac[]
QED

Theorem toplevel_immutable_alloc_copy_ghost_inv:
  ghost_inv d cenv cx es G tn s /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
  (!name b len. local_region cenv es.scopes u name b len ==>
    regions_disjoint (w2n w) nb b len) /\
  (!i. i < w2n w \/ w2n w+nb <= i ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  tm.t_mem SUBSET tn.t_mem /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ es'.scopes = es.scopes ==>
  ghost_inv d cenv cx es' H tm t
Proof
  strip_tac >>
  `!name b sz i. local_region cenv es.scopes s name b sz /\
    b <= i /\ i < b+sz ==> i NOTIN {i | w2n w <= i /\ i < w2n w+nb}` by
    (rpt strip_tac >>
     `local_region cenv es.scopes u name b sz` by
       (gvs[local_region_def] >> metis_tac[local_ptrs_reserved_def]) >>
     first_x_assum drule >> gvs[regions_disjoint_def] >> decide_tac) >>
  drule toplevel_local_footprint_disjoint >>
  disch_then (qspec_then `{i | w2n w <= i /\ i < w2n w+nb}` mp_tac) >>
  strip_tac >>
  irule toplevel_ghost_inv_memory_frame >>
  qexistsl_tac [`G`,`es`,`s`,`sa`,`tn`, `{i | w2n w <= i /\ i < w2n w+nb}`] >>
  simp[] >> conj_tac
  >- (gvs[] >> rpt gen_tac >> strip_tac >> first_x_assum irule >>
      simp[] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  gvs[SUBSET_DEF]
QED
