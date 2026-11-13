(* Constructor-compatible frames for local overwrites and buffer allocation. *)
Theory bodyFullMemoryFrames
Ancestors
  assignTuplePtrLocalCopyGhost assignTuplePtrStoreWord assignTuplePtrCopyLen
  bodyPtrDefs robustCopyTransportPtr localPtrsProps compileEnv loweringStateRelDefs
  storageNormalizationOwnershipPtr reasonAllocationFramePtr exprSimAlloc
  assignTuplePtrAlloc exprSimPtrLiteralBuffer
  loweringHalt exprLoweringProps bodyFullUnwrapRun fragExecPtr ptrSafetyTransport
  fragGasOriginPtr fragGasSeqPtr fragExec emitHelper emitHelperProps
  unitTransformDefs memSafeRun contextCodegenRel codegenRel fragExecMem
  context ptrDiscipline ptrSafeRun venomInst venomInstProofs venomExecSemantics
  venomState vyperState vyperLookup finite_map pred_set list rich_list words

Theorem body_full_local_scope_ghost_post:
  ghost_inv_at D lo d cenv cx es G tn s /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME dst /\
  local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
  local_region cenv es.scopes s id (w2n dst) sz /\ n <= sz /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
    val_in_memory entry.type v (w2n dst) mem) /\
  (!i. ~(w2n dst <= i /\ i < w2n dst+n) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  stor_taint_ok_at D tf t /\
  mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  (!i. i < lo /\ i IN tf.t_mem ==> i IN tn.t_mem) /\
  allocas_from lo t /\ lo <= t.vs_alloca_next ==>
  ghost_inv_at D lo d cenv cx
    (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
    Gf tf t
Proof
  strip_tac >>
  `!name x cap. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var x) cap) ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  rewrite_tac[ghost_inv_at_def] >> conj_tac >- suspend "locals" >>
  `return_buf_ptr d cenv Gf tf t` by
    (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
     fs[ghost_inv_at_def,return_buf_ptr_def] >>
     irule ptr_covers_lookup_frame >> goal_assum (drule_at Any) >> simp[]) >>
  simp[] >> fs[ghost_inv_at_def] >> metis_tac[local_ptrs_reserved_def]
QED

Resume body_full_local_scope_ghost_post[locals]:
  rpt gen_tac >> strip_tac >> fs[] >>
  drule_all local_copy_scope_lookup_ptr >> strip_tac >>
  `lookup_var p' t = lookup_var p' s /\ FLOOKUP Gf p' = FLOOKUP G p' /\
   op_taint tf (Var p') = op_taint tn (Var p')` by metis_tac[] >>
  conj_tac
  >- (irule ptr_covers_lookup_frame >> goal_assum (drule_at Any) >>
      fs[ghost_inv_at_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `name = id`
  >- (gvs[] >> metis_tac[]) >>
  `lookup_var p' s = SOME w` by metis_tac[] >> gvs[] >>
  drule_all local_region_other_footprint_ptr >> strip_tac >>
  irule robust_val_in_memory_exterior_frame >> simp[] >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`s.vs_memory`,`t.vs_memory`,`tn.t_mem`,`tf.t_mem`] >>
  simp[] >> fs[ghost_inv_at_def] >> metis_tac[]
QED

Finalise body_full_local_scope_ghost_post

Theorem body_full_memory_ghost_frame:
  ghost_inv_at D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
      i NOTIN writes)) /\
  (!i. i NOTIN writes ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  (!i. i < lo /\ i IN tf.t_mem ==> i IN tn.t_mem) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
  allocas_from lo t /\ lo <= t.vs_alloca_next ==>
  ghost_inv_at D lo d cenv cx es Gf tf t
Proof
  strip_tac >>
  `!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
    ptr_covers Gf tf p t sz` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_at_def,stor_taint_ok_at_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      conj_tac >- metis_tac[] >>
      rpt gen_tac >> strip_tac >>
      irule robust_val_in_memory_exterior_frame >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`s.vs_memory`,`t.vs_memory`,`tn.t_mem`,`tf.t_mem`,`writes`] >>
      metis_tac[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[])
  >- (rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[])
QED

Theorem body_full_alloc_buffer_path:
  stmt_state_rel H ctx func cenv cx es s /\
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func /\
  n < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u root b G1 tn1.
    buf.buf_operand = Var root /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,G1,tn1)) /\
    (!H'. stmt_state_rel H' ctx func cenv cx es s ==>
      stmt_state_rel H' ctx func cenv cx es u) /\
    (!D d. ghost_inv_at D lo d cenv cx es G tn s ==>
      ghost_inv_at D lo d cenv cx es G1 tn1 u) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,n) /\
    lo <= b /\ b+n < dimword (:256) /\ lookup_var root u = SOME (n2w b) /\
    ptr_covers G1 tn1 root u n /\
    (!name a len. local_region cenv es.scopes u name a len ==>
      regions_disjoint b n a len) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
      regions_disjoint b n a len) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x)) /\
    (!x cap. not_fresh_at sa x /\ ptr_covers G tn x s cap ==>
      ptr_covers G1 tn1 x u cap) /\
    not_fresh_at sb root /\
    (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\
    u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels /\
    u.vs_accounts = s.vs_accounts /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables /\
    (!i. ~(b <= i /\ i < b+n) ==> (i IN tn1.t_mem <=> i IN tn.t_mem)) /\
    tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all normalization_alloc_buffer_ownership >>
  disch_then (qspecl_then [`PG`,`G`,`tn`] strip_assume_tac) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `p = STRING #"%" (toString sa.cs_next_var)` by
    (qpat_x_assum `buf.buf_operand = Var p` mp_tac >> simp[]) >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [p]` >>
  qabbrev_tac `G1 = step_prov PG G inst t` >>
  qabbrev_tac `tn1 = step_taint inst s t tn` >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ [inst] /\
   sb.cs_blocks = sa.cs_blocks` by suspend "code" >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (irule step_inst_allocas_from >>
     qexistsl_tac [`ctx`,`0`,`inst`,`s`] >>
     simp[Abbr `inst`,step_inst_non_invoke,mk_inst_def]) >>
  `lo <= w2n w` by (fs[allocas_from_def] >> metis_tac[]) >>
  `~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
   t.vs_labels = s.vs_labels /\ t.vs_accounts = s.vs_accounts /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_transient = s.vs_transient /\
   t.vs_immutables = s.vs_immutables` by suspend "fields" >>
  `(!i. ~(w2n w <= i /\ i < w2n w+n) ==> (i IN tn1.t_mem <=> i IN tn.t_mem)) /\
   tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by suspend "taints" >>
  `!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
    op_taint tn1 (Var x) = op_taint tn (Var x)` by suspend "old" >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`,
    `p`,`w2n w`,`G1`,`tn1`] >>
  simp[lookup_var_def] >>
  conj_tac >- suspend "path" >>
  conj_tac >- suspend "state" >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- gvs[eval_operand_def,lookup_var_def] >>
  conj_tac >- (qpat_x_assum `!name a len. local_region _ _ t _ _ _ ==> _` mp_tac >>
    simp[local_region_def,lookup_var_def]) >>
  suspend "post"
QED

Resume body_full_alloc_buffer_path[post]:
  rpt conj_tac
  >- (rpt strip_tac >> metis_tac[])
  >- (rpt strip_tac >> fs[lookup_var_def] >> metis_tac[])
  >- (rpt strip_tac >> irule ptr_covers_lookup_frame >>
      goal_assum (drule_at Any) >> fs[lookup_var_def]) >>
  fs[allocas_from_def] >> rpt strip_tac >> metis_tac[]
QED

Resume body_full_alloc_buffer_path[code]:
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def,emit_op_def,comp_bind_def,comp_ignore_bind_def,
    comp_return_def,fresh_var_def,fresh_id_def,emit_def,Abbr `inst`] >>
  strip_tac >> gvs[]
QED

Resume body_full_alloc_buffer_path[fields]:
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Abbr `inst`,step_inst_base_opcode_eqs,mk_inst_def,exec_alloca_def,
    AllCaseEqs(),update_var_def] >>
  rpt strip_tac >> gvs[]
QED

Resume body_full_alloc_buffer_path[taints]:
  conj_tac
  >- (qunabbrev_tac `inst` >> qpat_x_assum `p = _` SUBST_ALL_TAC >>
      drule_all alloca_step_exterior_ghost_ptr >>
      disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
      fs[Abbr `tn1`] >> first_assum ACCEPT_TAC) >>
  simp[Abbr `tn1`,Abbr `inst`,normalization_alloca_key_taints]
QED

Resume body_full_alloc_buffer_path[ghost]:
  rpt strip_tac >> irule body_full_memory_ghost_frame >>
  fs[allocas_from_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G`,`s`,`sa`,`tn`,`{i | w2n w <= i /\ i < w2n w+n}`] >>
  simp[] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p'` by metis_tac[local_ptrs_reserved_def] >>
      `lookup_var p' t = SOME w'` by metis_tac[] >>
      drule_all literal_ptr_local_footprint_exterior >> simp[])
  >- (rpt strip_tac >> fs[lookup_var_def] >> metis_tac[])
  >- (rpt strip_tac >>
      `~(w2n w <= i /\ i < w2n w+n)` by decide_tac >> metis_tac[]) >>
  fs[lookup_var_def] >> rpt strip_tac >>
  qpat_x_assum `!j. _ ==> (j IN tn1.t_mem <=> j IN tn.t_mem)`
    (qspec_then `i` mp_tac) >>
  `~(w2n w <= i)` by decide_tac >> simp[]
QED

Resume body_full_alloc_buffer_path[old]:
  rpt strip_tac >>
  `x <> p` by metis_tac[] >>
  simp[] >> qunabbrev_tac `inst` >>
  qpat_x_assum `p = _` SUBST_ALL_TAC >>
  drule_all reason_alloca_old_metadata >>
  disch_then (qspecl_then [`PG`,`G`,`tn`] mp_tac) >>
  simp[Abbr `G1`,Abbr `tn1`] >> metis_tac[]
QED

Resume body_full_alloc_buffer_path[path]:
  gen_tac >>
  `inst_seq_ptr D lo ctx func PG G tn [inst] s G1 tn1` by
    (simp[inst_seq_ptr_def,Abbr `G1`,Abbr `tn1`,Abbr `inst`] >>
     irule ptr_inst_ok_lower_bound_transport >> simp[] >> qexists_tac `0` >>
     simp[ptr_inst_ok_alloca]) >>
  qspecl_then [`[inst]`,`sa`,`sb`,`s`,`t`,`G`,`tn`,`G1`,`tn1`]
    mp_tac emitted_origin_ptr_path >>
  simp[Abbr `inst`,mk_inst_def,is_terminator_def,run_inst_seq_def,
    run_inst_seq_mem_ok_def,inst_mem_below_frontier_def,inst_dload_in_section_def,
    source_memory_write_ranges_def,source_memory_read_ranges_def]
QED

Resume body_full_alloc_buffer_path[state]:
  rpt strip_tac >>
  qpat_x_assum `stmt_state_rel H ctx func cenv cx es s` kall_tac >>
  qpat_x_assum `stmt_state_rel H ctx func cenv cx es t` kall_tac >>
  drule_all normalization_alloc_buffer_ownership >>
  disch_then (qspecl_then [`PG`,`G`,`tn`] strip_assume_tac) >>
  gvs[Abbr `inst`,stmt_state_rel_inst_idx]
QED

Finalise body_full_alloc_buffer_path
