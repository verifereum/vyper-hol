(* The constructor-code field is unwrapped at the cursor after ADD, not at
   the end of the child's compilation. The result allocation is already old
   at that cursor, even when the new scratch allocation has size zero. *)
Theory bodyStructFieldCtorReadMods
Ancestors
  bodyIfExpArmUnwrapMods bodyPtrMakeArrayMemoryFrame abiDecodeStaticProps
  representationCleanPtr exprSimUnwrap exprLowering compileEnv exprLoweringProps[qualified]
  freshWrites loweringShapeDefs vyperStorageFootprint exprPtrUnwrapStorageShape
  bodyFullPostsMods loweringPosts bodyPtrDefs exprSimProps context
  loweringStateRelDefs[qualified] words list pair finite_map arithmetic

Theorem ctor_unwrap_keeps_struct_cells[local]:
  literal_prefix_ok cells tn s /\
  EVERY (\(tv,v,p,k). addr <= p /\ p+k <= addr+capacity) cells /\
  mem_bytes_at addr capacity z.vs_memory = mem_bytes_at addr capacity s.vs_memory /\
  (!i. addr <= i /\ i < addr+capacity /\ i IN tf.t_mem ==> i IN tn.t_mem) ==>
  literal_prefix_ok cells tf z
Proof
  strip_tac >> irule literal_prefix_transport >>
  qexistsl_tac [`s`,`tn`] >> simp[] >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac literal_prefix_lookup >>
  `addr <= p /\ p+k <= addr+capacity` by
    (qpat_x_assum `EVERY _ cells` mp_tac >> simp[EVERY_MEM] >>
     disch_then (qspec_then `(tv,v,p,k)` mp_tac) >> simp[]) >>
  `mem_bytes_at p k z.vs_memory = mem_bytes_at p k s.vs_memory` by
    (irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >> rpt strip_tac >>
     irule representationCleanPtrTheory.mem_bytes_at_eq_byte >>
     qexistsl_tac [`addr`,`capacity`] >> simp[] >> decide_tac) >>
  gen_tac >> disch_tac >> irule robust_val_in_memory_shrinking_frame >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`tn.t_mem`,`tf.t_mem`,`s.vs_memory`,`z.vs_memory`,`k`] >>
  simp[] >> rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac
QED

Theorem ctor_old_result_frame[local]:
  wb_frame ce ee ee sn s z /\ ghost_kept_at lo ce ee sn G tn s Gf tf /\
  aid < sn.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (addr,capacity) /\
  (!name b n. loweringStateRelDefs$local_region ce ee.scopes s name b n ==>
      addr+capacity <= b \/ b+n <= addr) ==>
  mem_bytes_at addr capacity z.vs_memory = mem_bytes_at addr capacity s.vs_memory /\
  (!i. addr <= i /\ i < addr+capacity /\ i IN tf.t_mem ==> i IN tn.t_mem)
Proof
  simp[wb_frame_def,ghost_kept_at_def] >> strip_tac >> conj_tac
  >- (qpat_assum `!a off sz. _ ==> mem_bytes_at off sz _ = _`
        (qspecl_then [`aid`,`addr`,`capacity`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  gen_tac >> strip_tac >>
  qpat_assum `!a off sz i. _ ==> i IN tn.t_mem`
    (qspecl_then [`aid`,`addr`,`capacity`,`i`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

(* Even when the copy loop emits no code, the constructor route allocates. *)
Theorem ctor_unwrap_advances[local]:
  unwrap_value ce (LocatedValue tag p) sn = (op,su) /\
  ce.ce_is_ctor /\ p.ptr_location = LocCode /\ ~is_word_type tag ==>
  sn.cs_next_id < su.cs_next_id
Proof
  strip_tac >> qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, compile_ensure_in_memory_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_then strip_assume_tac loweringHaltTheory.compile_alloc_buffer_parts >>
  `ci_mono cs' cs''` by
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_imm_copy_to_memory,SND] >>
  fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac
QED

Theorem struct_field_ctor_read_mods:
  compile_expr ce ty e si = (LocatedValue tag p,sm) /\
  unwrap_value ce (LocatedValue tag p) sn = (op,su) /\
  ce.ce_is_ctor /\ p.ptr_location = LocCode /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  fn_has_code sn su func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce si /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at si x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at si x) /\
  expr_body_pre_mods mods ce cx env e es /\ ~is_word_type (expr_type e) /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es si sn s0 ee tv (LocatedValue tag p) s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e)
    ee tv (LocatedValue tag p) s /\
  ptr_vv_ok cx (post_value_type ce e) tv (LocatedValue tag p) ee G tn s /\
  (?v. read_result cx tv ee = (INL v,ee) /\
    !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
           eval_operand p.ptr_operand s = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory rt v (w2n w) mem)) /\
  ghost_kept_at lo ce es si Gi ti s0 G tn /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\ alloca_history func s /\
  aid < sn.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (addr,capacity) /\
  (!name b n. loweringStateRelDefs$local_region ce ee.scopes s name b n ==>
      addr+capacity <= b \/ b+n <= addr) /\
  EVERY (\(tv,v,b,n). addr <= b /\ b+n <= addr+capacity) cells /\
  literal_prefix_ok cells tn s /\
  not_fresh_at sn root /\ ptr_covers G tn root s capacity /\
  not_fresh_at sn dst /\ ptr_covers G tn dst s field_size ==>
  ?v z Gf tf rt w.
    read_result cx tv ee = (INL v,ee) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post_mods H ctx func ce cx e es si su s0 ee v op z /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z) /\
    ghost_kept_at lo ce es si Gi ti s0 Gf tf /\
    ptr_val_ok cx (post_value_type ce e) v op Gf tf z /\
    ptr_buf_ok ce e op Gf z /\ expr_store_bound cx (post_value_type ce e) v op z /\
    ~z.vs_halted /\ z.vs_current_bb = su.cs_current_bb /\
    z.vs_inst_idx = LENGTH su.cs_current_insts /\ alloca_history func z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ s.vs_alloca_next <= z.vs_alloca_next /\
    ~is_word_type (post_value_type ce e) /\ post_value_type ce e = lowered_value_type ce e /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
    value_has_type rt v /\ val_wf rt v /\ eval_operand op z = SOME w /\ op_taint tf op = {} /\
    (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==>
      val_in_memory rt v (w2n w) mem) /\
    (type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    w2n w + type_memory_size rt < dimword (:256) /\
    (0 < type_memory_size rt ==>
      ?r. op = Var r /\ not_fresh_at su r /\ ptr_covers Gf tf r z (type_memory_size rt)) /\
    cs_extends sn su /\ sn.cs_next_id < su.cs_next_id /\
    FLOOKUP z.vs_allocas sn.cs_next_id = SOME (w2n w,type_memory_size rt) /\ lo <= w2n w /\
    (w2n w + val_footprint rt v <= addr \/ addr+capacity <= w2n w) /\
    wb_frame ce ee ee sn s z /\ ghost_kept_at lo ce ee sn G tn s Gf tf /\
    (!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!old b. FLOOKUP s.vs_allocas old = SOME b ==> FLOOKUP z.vs_allocas old = SOME b) /\
    literal_prefix_ok cells tf z /\ ptr_covers Gf tf root z capacity /\
    ptr_covers Gf tf dst z field_size
Proof
  strip_tac >>
  drule ifexp_arm_nonword_unwrap_mods >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_body_pre_mods _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `vv_store_bound _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`st0`,`explicit`,`d`,`ctx`,`PG`,`DF`] mp_tac) >>
  impl_tac
  >- (asm_simp_tac (srw_ss()) [vv_location_def,vv_operand_def] >>
      qexists_tac `v` >> simp[]) >>
  `~is_word_type tag` by
    (`valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
       fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
       (drule_then strip_assume_tac) >>
     `tag = post_value_type ce e` by
       (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
          (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
        qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
        simp[vv_holds_mods_def]) >>
     `lowered_value_type ce e = expr_type e` by
       (drule compile_nonmemory_lowered_value_type >> simp[]) >>
     simp[post_value_type_lowered]) >>
  drule_all_then assume_tac ctor_unwrap_advances >>
  `su <> sn` by (strip_tac >> fs[]) >>
  disch_then (qx_choosel_then [`v'`,`z`,`Gf`,`tf`,`pt`,`rt`,`w`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `(su = sn /\ _) \/ _` mp_tac >> asm_rewrite_tac[] >> strip_tac >>
  drule_all_then strip_assume_tac ctor_old_result_frame >>
  drule_all_then assume_tac ctor_unwrap_keeps_struct_cells >>
  `w2n w + val_footprint rt v' <= addr \/ addr+capacity <= w2n w` by
    (qpat_assum `!a b len. _ ==> loweringStateRelDefs$regions_disjoint _ _ b len`
       (qspecl_then [`aid`,`addr`,`capacity`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
     `val_footprint rt v' <= type_memory_size rt` by simp[val_footprint_le] >>
     decide_tac) >>
  `ptr_covers Gf tf root z capacity /\ ptr_covers Gf tf dst z field_size` by
    (conj_tac >> first_x_assum irule >> simp[]) >>
  drule_then assume_tac unwrap_value_extends >>
  qexistsl_tac [`v'`,`z`,`Gf`,`tf`,`rt`,`w`] >>
  asm_rewrite_tac[]
QED
