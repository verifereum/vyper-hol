(* The destination is already allocated. A stack or memory source needs
   no further instructions and keeps its original ownership witness. *)
Theory bodyExtDefaultUnwrapIdentityMods
Ancestors
  bodyLocalCopyPhysicalRhsMods bodyFullPostsMods bodyPtrDefs
  exprSimIfExpWidenedAdapter reasonEndpointResourcesPtr bodyPtrAttributeSource
  exprSimWordArgs wordArgsPtr fragGasOriginPtr vyperStorageFootprint
  loweringPosts exprLowering compileEnv valueCopyBytes context words

Theorem identity_vv_post_cursor[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv u /\
  sm.cs_next_id <= sn.cs_next_id ==>
  vv_post_mods H ctx func ce cx e es sa sn s0 ee tv vv u
Proof
  disch_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  asm_rewrite_tac[vv_post_mods_def] >> conj_tac
  >- (irule vv_at_alloc_mono_frame >> qexistsl [`u`,`sm`] >> simp[]) >>
  strip_tac >> irule vv_own_alloc_mono_frame >> qexistsl [`u`,`sm`] >> simp[]
QED

Theorem identity_source_shape[local]:
  ((?tag x. vv = StackValue tag x) \/
   (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory)) /\
  vv_holds_mods ce cx ty tv vv ee u /\ ~is_word_type ty ==>
  ((?tag. vv = StackValue tag (vv_operand vv)) \/
   (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory /\
            ~is_word_type tag /\ p.ptr_operand = vv_operand vv)) /\
  (?v w. read_result cx tv ee = (INL v,ee) /\
         eval_operand (vv_operand vv) u = SOME w)
Proof
  strip_tac >> gvs[vv_holds_mods_def,vv_operand_def]
  >- (drule attribute_vv_holds_read_operand >> simp[vv_operand_def]) >>
  qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
  simp[vv_holds_def] >> metis_tac[is_bytestring_word_type]
QED

Theorem default_unwrap_identity_prefix_mods:
  ((?tag x. vv = StackValue tag x) \/
   (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory)) /\
  unwrap_value ce vv sn = (op,sc) /\
  sm.cs_next_id <= sn.cs_next_id /\
  ~is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv u /\
     ghost_inv_at_mods (DF H) lo d ce cx ee Ga ta u) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv u /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee Ga ta u /\
  ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
  u.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  sc = sn /\ op = vv_operand vv /\
  ?v sw. read_result cx tv ee = (INL v,ee) /\
    eval_operand op u = SOME sw /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Ga,ta) [] (OK u,Ga,ta) /\
       expr_post_mods H ctx func ce cx e es sa sc s0 ee v op u /\
       ghost_inv_at_mods (DF H) lo d ce cx ee Ga ta u) /\
    ptr_val_ok cx (post_value_type ce e) v op Ga ta u /\
    expr_store_bound cx (post_value_type ce e) v op u /\
    (val_footprint ptv v = 0 \/
     (?aid b len. FLOOKUP u.vs_allocas aid = SOME (b,len) /\ aid < sm.cs_next_id /\
        b <= w2n sw /\ w2n sw + val_footprint ptv v <= b + len) \/
     (?name b len. local_region ce ee.scopes u name b len /\
        b <= w2n sw /\ w2n sw + val_footprint ptv v <= b + len)) /\
    wb_frame ce ee ee sn u u /\ ghost_kept_at lo ce ee sn Ga ta u Ga ta /\
    u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  drule_all_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) identity_source_shape >>
  `sc = sn /\ op = vv_operand vv` by
    (Cases_on `vv` >> gvs[unwrap_value_def,comp_return_def,vv_operand_def]) >>
  Q.SUBGOAL_THEN
    `(?tag. vv = StackValue tag op) \/
      (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory /\
               ~is_word_type tag /\ p.ptr_operand = op)` assume_tac
  >- metis_tac[] >>
  `unwrap_value ce vv sm = (op,sm)` by
    (Cases_on `vv` >> gvs[unwrap_value_def,comp_return_def,vv_operand_def]) >>
  `ptr_val_ok cx (post_value_type ce e) v op Ga ta u /\
   expr_store_bound cx (post_value_type ce e) v op u` by
    (drule_all local_copy_rhs_identity_unwrap_mods >> simp[]) >>
  qpat_x_assum `unwrap_value ce vv sm = (op,sm)` kall_tac >>
  simp[wb_frame_refl,ghost_kept_at_refl] >>
  `ptr_val_ok cx (post_value_type ce e) v (vv_operand vv) Ga ta u /\
   expr_store_bound cx (post_value_type ce e) v (vv_operand vv) u` by metis_tac[] >>
  asm_rewrite_tac[] >> conj_tac
  >- (qx_gen_tac `H` >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
      simp[cj 1 gas_origin_ptr_path_rules] >>
      `vv_post_mods H ctx func ce cx e es sa sn s0 ee tv vv u` by
        (irule identity_vv_post_cursor >> qexists `sm` >> asm_rewrite_tac[]) >>
      drule_all local_copy_rhs_identity_unwrap_mods >> simp[]) >>
  Cases_on `val_footprint ptv v = 0` >- simp[] >>
  simp[] >> irule vv_at_memory_region_prefix >>
  qpat_assum `vv_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `read_result _ _ _ = _` (irule_at Any) >>
  qpat_assum `evaluate_type _ _ = _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED
