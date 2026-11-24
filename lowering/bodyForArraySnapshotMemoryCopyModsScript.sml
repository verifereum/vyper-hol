Theory bodyForArraySnapshotMemoryCopyMods
Ancestors
  bodyForArraySnapshotChildMods bodyForArraySnapshotOwnedDomainMods
  bodyFullForMemoryElementDispatch bodyForArrayHeaderMods bodyMemoryDefs
  bodyPtrDefs ptrDiscipline loweringPosts abiDecodeStaticProps whitelistForIterImmCopy
  vyperTypeValues vyperTypeArgFits valueEncoding finite_map arithmetic words

(* The local region bounds the actual read. Provenance for the computed
   address is inherited separately and need not refer to this region. *)
Theorem snapshot_local_copy_domain[local]:
  ptr_mem_ok cx (ArrayT ty bd) (ArrayV av) base_op Gc tc capture /\
  evaluate_type (get_tenv cx) (ArrayT ty bd) = SOME (ArrayTV tv bd) /\
  eval_operand base_op capture = SOME bw /\
  op_prov G (Var xs) = op_prov Gc base_op /\
  lookup_var xs u = SOME (bw + n2w delta) /\
  op_taint tn (Var xs) = {} /\
  delta + type_memory_size tv <= type_memory_size (ArrayTV tv bd) /\
  stmt_state_rel H ctx func c cx ee u /\
  local_region c ee.scopes u name b sz /\
  b <= w2n bw /\ w2n bw + type_memory_size (ArrayTV tv bd) <= b + sz /\
  for_array_item_mods c sa saExpr (xd,dw,cap,aidItem) ee G tn u /\
  type_memory_size tv <= cap /\ u.vs_alloca_next < dimword (:256) ==>
  w2n (bw + n2w delta) = w2n bw + delta /\
  ptr_covers G tn xs u (type_memory_size tv) /\
  w2n (bw + n2w delta) + type_memory_size tv <= u.vs_alloca_next /\
  (w2n (bw + n2w delta) + type_memory_size tv <= w2n dw \/
   w2n dw + type_memory_size tv <= w2n (bw + n2w delta))
Proof
  strip_tac >>
  drule_all_then assume_tac body_local_region_frontier >>
  qhdtm_x_assum `for_array_item_mods`
    (strip_assume_tac o REWRITE_RULE [for_array_item_mods_def]) >>
  qpat_assum `!nm b sz. local_region _ _ _ nm b sz ==> _`
    (drule_then assume_tac) >>
  qabbrev_tac `extent = type_memory_size (ArrayTV tv bd)` >>
  `w2n (bw + n2w delta) = w2n bw + delta` by
    (irule w2n_add_n2w_lt >> decide_tac) >>
  `0 < type_memory_size tv` by
    (drule immutable_array_element_size_positive >> simp[]) >>
  `extent <> 0` by decide_tac >>
  `?p b0 sz0. base_op = Var p /\ FLOOKUP Gc p = SOME (b0,sz0) /\
      b0 <= w2n bw /\ w2n bw + extent <= b0 + sz0` by
    (qhdtm_x_assum `ptr_mem_ok` (mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >>
     disch_then (qspecl_then [`ArrayTV tv bd`,`bw`] mp_tac) >>
     simp[Abbr `extent`, val_footprint_def, exprSimPropsTheory.val_store_size_def]) >>
  `FLOOKUP G xs = SOME (b0,sz0)` by fs[op_prov_def] >>
  `ptr_covers G tn xs u (type_memory_size tv)` by
    (simp[ptr_covers_def] >> qexistsl_tac [`b0`,`sz0`] >> simp[] >> decide_tac) >>
  simp[] >> decide_tac
QED

Theorem for_array_snapshot_memory_copy_mods:
  evaluate_type (get_tenv cx) (ArrayT ty bd) = SOME (ArrayTV tv bd) /\
  vs = MAP Value (array_elements (ArrayTV tv bd) av) /\
  k < LENGTH vs /\ value_has_type (ArrayTV tv bd) (ArrayV av) /\
  compile_iter_elem_copy c (Var xs) (Var xd) (type_memory_size tv)
    LocMemory F ty ty saCopy = ((),sbCopy) /\
  acyclic_struct_metadata c.ce_struct_fields /\
  sfields_tenv_consistent c.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP c.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_memory_bytes c ty = type_memory_size tv /\
  delta = (case bd of Fixed _ => 0 | Dynamic _ => 32) + k * type_memory_size tv /\
  (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
    val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) mem) /\
  ptr_mem_ok cx (ArrayT ty bd) (ArrayV av) base_op Gc tc capture /\
  eval_operand base_op capture = SOME bw /\
  op_prov G (Var xs) = op_prov Gc base_op /\
  lookup_var xs u = SOME (bw + n2w delta) /\
  op_taint tn (Var xs) = {} /\ not_fresh_at saCopy xs /\
  (0 < type_memory_size (ArrayTV tv bd) ==>
    (?aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) /\
       aid < saExpr.cs_next_id /\ b <= w2n bw /\
       w2n bw + type_memory_size (ArrayTV tv bd) <= b + sz) \/
    (?name b sz. local_region c ee.scopes u name b sz /\ b <= w2n bw /\
       w2n bw + type_memory_size (ArrayTV tv bd) <= b + sz)) /\
  stmt_state_rel H ctx func c cx ee u /\
  for_array_item_mods c sa saExpr (xd,dw,cap,aidItem) ee G tn u /\
  alloca_inv u /\ u.vs_alloca_next < dimword (:256) /\
  not_fresh_at saCopy xd /\ type_memory_size tv <= cap /\
  allocas_from lo u /\ lo <= u.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  fn_has_code saCopy sbCopy func /\ fn_inst_ids_distinct func /\
  ~u.vs_halted /\ u.vs_current_bb = saCopy.cs_current_bb /\
  u.vs_inst_idx = LENGTH saCopy.cs_current_insts ==>
  ?v n z Gf tf.
    EL k vs = Value v /\ value_has_type tv v /\ val_wf tv v /\
    n <= cap /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G,tn) [] (OK z,Gf,tf)) /\
    ~z.vs_halted /\ z.vs_current_bb = sbCopy.cs_current_bb /\
    z.vs_inst_idx = LENGTH sbCopy.cs_current_insts /\
    val_in_memory tv v (w2n dw) z.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==>
      val_in_memory tv v (w2n dw) mem) /\
    typed_copy_state_frame saCopy (w2n dw) n u z /\
    tf.t_imm = tn.t_imm /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+n) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!p. not_fresh_at saCopy p ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    FLOOKUP z.vs_allocas aidItem = SOME (w2n dw,cap) /\
    lookup_var xd z = SOME dw /\ ptr_covers Gf tf xd z cap
Proof
  strip_tac >>
  drule_then assume_tac evaluate_type_well_formed_type_value >>
  drule_all_then (strip_assume_tac o SIMP_RULE std_ss [LET_THM])
    for_array_snapshot_child_mods >>
  `0 < type_memory_size tv` by
    (drule immutable_array_element_size_positive >> simp[]) >>
  `delta + type_memory_size tv <= type_memory_size (ArrayTV tv bd)` by fs[] >>
  `0 < type_memory_size (ArrayTV tv bd)` by decide_tac >>
  Q.SUBGOAL_THEN
    `w2n (bw + n2w delta) = w2n bw + delta /\
     ptr_covers G tn xs u (type_memory_size tv) /\
     w2n (bw + n2w delta) + type_memory_size tv <= u.vs_alloca_next /\
     (w2n (bw + n2w delta) + type_memory_size tv <= w2n dw \/
      w2n dw + type_memory_size tv <= w2n (bw + n2w delta))`
    (map_every assume_tac o CONJUNCTS)
  >-
    (qpat_x_assum `0 < type_memory_size (ArrayTV _ _) ==> _`
       (drule_then DISJ_CASES_TAC) >-
       (`0 < type_memory_size (ArrayTV tv bd) ==>
          ?aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) /\
            aid < saExpr.cs_next_id /\ b <= w2n bw /\
            w2n bw + type_memory_size (ArrayTV tv bd) <= b + sz` by simp[] >>
        drule_all_then mp_tac (SIMP_RULE bool_ss []
          (Q.INST [`dtv` |-> `stv`] for_array_snapshot_owned_domain_mods)) >> simp[]) >>
     qpat_x_assum `?name b sz. local_region _ _ _ name b sz /\ _` strip_assume_tac >>
     drule_all_then ACCEPT_TAC snapshot_local_copy_domain) >>
  qhdtm_x_assum `for_array_item_mods`
    (strip_assume_tac o REWRITE_RULE [for_array_item_mods_def]) >>
  `evaluate_type (get_tenv cx) ty = SOME tv` by
    (drule_then strip_assume_tac evaluate_type_ArrayT_cases >> gvs[]) >>
  qabbrev_tac `v = EL k (array_elements (ArrayTV tv bd) av)` >>
  `!m. mem_agree_outside tn.t_mem u.vs_memory m ==>
       val_in_memory tv v (w2n (bw + n2w delta)) m` by
    (gen_tac >> strip_tac >>
     qpat_assum `!mem. mem_agree_outside _ _ mem ==> _`
       (drule_then assume_tac) >>
     asm_rewrite_tac[] >>
     qpat_assum `!base m. val_in_memory (ArrayTV _ _) _ base m ==>
                          val_in_memory _ _ (base + _) m`
       (qspecl_then [`w2n (bw:bytes32)`,`m`] (drule_then ACCEPT_TAC))) >>
  `w2n (bw + n2w delta) + type_memory_size tv < dimword (:256) /\
   w2n dw + type_memory_size tv < dimword (:256) /\
   w2n dw + type_memory_size tv <= u.vs_alloca_next` by decide_tac >>
  qexists_tac `v` >> asm_rewrite_tac[] >>
  irule for_memory_element_dispatch_joint_frame >> asm_rewrite_tac[] >>
  conj_tac >- (qexistsl_tac [`k`,`vs`] >> asm_rewrite_tac[]) >>
  qexistsl_tac [`type_memory_size tv`,`c`,`ty`,`tv`,`ty`,
                `bw + n2w delta`,`get_tenv cx`,`xs`] >>
  asm_rewrite_tac[type_widens_to_refl]
QED
