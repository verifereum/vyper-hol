(* The tuple allocation frames native, zero-safe argument resources. *)
Theory bodyFullAbiEncodeTupleAlloc
Ancestors
  bodyFullAbiEncodeAllocOrigin bodyFullAllocaFresh
  abiTupleProps abiArgsLabelBoundary logValueFramePtr assignTuplePtrCopyLen
  robustCopyTransportPtr ptrDiscipline abiBuiltinAllocation emitHelperProps
  loweringShapeDefs
  abiEncodeArgsSim exprSimProps bodyPtrDefs loweringPosts
  exprLoweringProps loweringHalt compileEnv loweringStateRelDefs
  valueEncodingProps abiDecodeStaticProps venomState venomMemDefs
  arithmetic list words finite_map pred_set

Theorem allocation_footprint_separation[local]:
  expr_val_at ce cx ty origin a es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w /\
  (!aid z k. aid < a.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (z,k) ==>
    loweringStateRelDefs$regions_disjoint dst sz z k) /\
  (!name z k. local_region ce es.scopes s name z k ==>
    loweringStateRelDefs$regions_disjoint dst sz z k) ==>
  val_footprint tv v = 0 \/
  loweringStateRelDefs$regions_disjoint dst sz (w2n w) (val_footprint tv v)
Proof
  strip_tac >> Cases_on `val_footprint tv v = 0` >> simp[] >>
  fs[expr_val_at_def] >> gvs[] >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def]
  >- (qpat_x_assum `!aid z k. _` (qspecl_then [`aid`, `b`, `sz'`] mp_tac) >> simp[] >> decide_tac) >>
  qpat_x_assum `!name z k. _` (drule_then mp_tac) >> decide_tac
QED

Theorem allocation_positive_resource_frame[local]:
  abi_tuple_input ce ty tv v op s /\ ~is_word_type ty /\
  val_wf tv v /\ type_memory_size tv = type_memory_bytes ce ty /\
  op = Var x /\ lookup_var x s = SOME w /\
  ptr_covers G tn x s (type_memory_bytes ce ty) /\
  w2n w + type_memory_bytes ce ty < dimword(:256) /\
  w2n w + type_memory_bytes ce ty <= s.vs_alloca_next /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem) /\
  lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
  op_taint tn' (Var x) = op_taint tn (Var x) /\
  t.vs_memory = s.vs_memory /\ s.vs_alloca_next <= t.vs_alloca_next /\
  (!i. i IN tn'.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < endpos)) ==>
  abi_tuple_input ce ty tv v op t /\
  lookup_var x t = SOME w /\ ptr_covers G' tn' x t (type_memory_bytes ce ty) /\
  w2n w + type_memory_bytes ce ty < dimword(:256) /\
  w2n w + type_memory_bytes ce ty <= t.vs_alloca_next /\
  (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem)
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem` by
    (rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
     conj_tac >- simp[] >>
     qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tn'.t_mem`,
       `{i | s.vs_alloca_next <= i}`] >> simp[] >>
     `val_footprint tv v <= type_memory_bytes ce ty` by metis_tac[val_footprint_le] >>
     rpt strip_tac >> gvs[] >> decide_tac) >>
  conj_tac >- (gvs[abi_tuple_input_def, eval_operand_def] >> metis_tac[mem_agree_outside_def]) >>
  simp[] >> irule ptr_covers_lookup_frame >>
  qexistsl_tac [`G`, `s`, `tn`] >> simp[]
QED

Theorem abi_encode_tuple_allocate_origin:
  compile_alloc_buffer sz a = (buf,b) /\ fn_has_code a b func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce a /\
  sz < dimword(:256) /\
  stmt_state_rel H ctx func ce cx es s /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  LENGTH ops = LENGTH tys /\ LENGTH tvs = LENGTH tys /\ LENGTH vs = LENGTH tys /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!i. i < LENGTH tys ==>
    val_wf (EL i tvs) (EL i vs) /\
    type_memory_size (EL i tvs) = type_memory_bytes ce (EL i tys) /\
    type_memory_bytes ce (EL i tys) < dimword(:256) /\
    (if ~is_word_type (EL i tys) /\ type_memory_bytes ce (EL i tys) = 0 then T else
      abi_tuple_input ce (EL i tys) (EL i tvs) (EL i vs) (EL i ops) s /\
      (!x. EL i ops = Var x ==> not_fresh_at a x) /\
      (if is_word_type (EL i tys) then op_taint tn (EL i ops) = {} else
        evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
        expr_val_at ce cx (EL i tys) origin a es (EL i vs) (EL i ops) s /\
        ?x w. EL i ops = Var x /\ lookup_var x s = SOME w /\
          ptr_covers G tn x s (type_memory_bytes ce (EL i tys)) /\
          w2n w + type_memory_bytes ce (EL i tys) < dimword(:256) /\
          w2n w + type_memory_bytes ce (EL i tys) <= s.vs_alloca_next /\
          (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
            val_in_memory (EL i tvs) (EL i vs) (w2n w) mem)))) ==>
  ?root bw t Gf tnf.
    buf.buf_operand = Var root /\ not_fresh_at b root /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    stmt_state_rel H ctx func ce cx es t /\ alloca_history func t /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    lookup_var root t = SOME bw /\ ptr_covers Gf tnf root t sz /\
    FLOOKUP Gf root = SOME (w2n bw,sz) /\
    w2n bw + sz < dimword(:256) /\ lo <= w2n bw /\
    w2n bw + sz <= t.vs_alloca_next /\
    (!name z k. local_region ce es.scopes s name z k ==>
      loweringStateRelDefs$regions_disjoint (w2n bw) sz z k) /\
    (!name z k. local_region ce es.scopes t name z k ==>
      loweringStateRelDefs$regions_disjoint (w2n bw) sz z k) /\
    (!aid z k. aid < a.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (z,k) ==>
      loweringStateRelDefs$regions_disjoint (w2n bw) sz z k) /\
    (!D. ghost_inv_at D lo d ce cx es G tn s ==>
      ghost_inv_at D lo d ce cx es Gf tnf t) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    t.vs_memory = s.vs_memory /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!i. i IN tnf.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < w2n bw + sz)) /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!i. i < LENGTH tys ==>
      val_wf (EL i tvs) (EL i vs) /\
      type_memory_size (EL i tvs) = type_memory_bytes ce (EL i tys) /\
      type_memory_bytes ce (EL i tys) < dimword(:256) /\
      (if ~is_word_type (EL i tys) /\ type_memory_bytes ce (EL i tys) = 0 then T else
        abi_tuple_input ce (EL i tys) (EL i tvs) (EL i vs) (EL i ops) t /\
        (!x. EL i ops = Var x ==> not_fresh_at b x) /\
        (if is_word_type (EL i tys) then op_taint tnf (EL i ops) = {} else
          ?x w. EL i ops = Var x /\ lookup_var x t = SOME w /\
            ptr_covers Gf tnf x t (type_memory_bytes ce (EL i tys)) /\
            w2n w + type_memory_bytes ce (EL i tys) < dimword(:256) /\
            w2n w + type_memory_bytes ce (EL i tys) <= t.vs_alloca_next /\
            (val_footprint (EL i tvs) (EL i vs) = 0 \/
             loweringStateRelDefs$regions_disjoint (w2n bw) sz (w2n w) (val_footprint (EL i tvs) (EL i vs))) /\
            (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
              val_in_memory (EL i tvs) (EL i vs) (w2n w) mem))))
Proof
  strip_tac >> drule_all (INST_TYPE [``:'b`` |-> ``:'a``] abi_encode_alloc_origin_exact) >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`] strip_assume_tac) >>
  `t.vs_memory = s.vs_memory /\ ~t.vs_halted` by
    (qpat_assum `t with <| vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _ |> = s`
       mp_tac >> simp[venom_state_component_equality]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_assum `t with <| vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _ |> = s`
       mp_tac >> simp[venom_state_component_equality]) >>
  `lo <= w2n w` by (fs[allocas_from_def] >> metis_tac[]) >>
  `!name z k. local_region ce es.scopes s name z k ==>
     loweringStateRelDefs$regions_disjoint (w2n w) sz z k` by
    (rpt strip_tac >> qpat_x_assum `!name z k. local_region ce es.scopes t name z k ==> _` irule >>
     qexists_tac `name` >> fs[local_region_def] >>
     metis_tac[local_ptrs_reserved_def]) >>
  `!D. ghost_inv_at D lo d ce cx es G tn s ==> ghost_inv_at D lo d ce cx es G' tn' t` by
    (rpt strip_tac >> irule alloc_buffer_ghost_inv_at >>
     simp[] >> rpt (first_assum (irule_at Any)) >>
     qexists_tac `w2n w + sz` >> simp[] >>
     qpat_x_assum `t with <| vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _ |> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexistsl_tac [`q`, `w`, `t`, `G'`, `tn'`] >> simp[ADD_COMM] >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[ADD_COMM]) >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[ADD_COMM]) >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule_all >> simp[ADD_COMM]) >>
  `a.cs_next_var <= b.cs_next_var` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     qspecl_then [`ALLOCA`, `[Lit (n2w sz)]`, `a`] mp_tac ci_mono_emit_op >>
     simp[ci_mono_def]) >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH tys ==> _` drule >> strip_tac >>
  Cases_on `is_word_type (EL i tys)` >> gvs[]
  >- (conj_tac
      >- (gvs[abi_tuple_input_def] >> Cases_on `EL i ops` >>
          gvs[eval_operand_def] >> metis_tac[]) >>
      conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
      Cases_on `EL i ops` >> gvs[op_taint_def] >> metis_tac[]) >>
  Cases_on `type_memory_bytes ce (EL i tys) = 0` >> gvs[] >>
  qpat_assum `!x. not_fresh_at a x ==> _` (drule_then strip_assume_tac) >>
  drule allocation_positive_resource_frame >>
  rpt (disch_then (drule_at_then Any mp_tac)) >>
  simp[ADD_COMM] >> strip_tac >>
  simp[] >> conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  irule allocation_footprint_separation >>
  simp[eval_operand_def] >> rpt (first_assum (irule_at Any)) >>
  simp[eval_operand_def] >> metis_tac[]
QED
