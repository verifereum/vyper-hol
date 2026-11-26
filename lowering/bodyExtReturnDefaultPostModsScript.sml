(* Linked postcondition at the actual endpoint of the default-value copy. *)
Theory bodyExtReturnDefaultPostMods
Ancestors
  bodyIfExpTypedGhostMods bodyIfExpTypedImmFrameMods
  exprSimIfExpWidenedCounted exprSimIfExpWidenedProvenance
  bodyFullUnwrapSlotPost exprSimHash bodyFullPostsMods stateRelProj
  freshWrites assignTuplePtrCopyLen exprSimProps loweringPosts
  typedMemoryCopy loweringStateRelDefs exprSimMemDefs bodyPtrDefs
  exprLowering compileEnv vyperState vyperAST venomState words finite_map context

Triviality default_copy_caller_frame:
  typed_copy_frame off n a.vs_memory z.vs_memory /\
  wb_frame ce es ee sa s0 a /\ local_ptrs_reserved ce sa /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x a /\
     FLOOKUP Gz x = FLOOKUP Ga x /\ op_taint tz (Var x) = op_taint ta (Var x)) /\
  a.vs_allocas = z.vs_allocas /\
  (!aid b len. FLOOKUP s0.vs_allocas aid = SOME (b,len) /\ aid < sa.cs_next_id ==>
     regions_disjoint off n b len) /\
  (!name b len. local_region ce ee.scopes a name b len ==>
     regions_disjoint off n b len) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 Ga ta /\ lo <= off /\
  (!i. ~(off <= i /\ i < off + n) ==> (i IN tz.t_mem <=> i IN ta.t_mem)) ==>
  wb_frame ce es ee sa s0 z /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gz tz
Proof
  strip_tac >>
  `!i len. regions_disjoint off n i len ==>
      mem_bytes_at i len z.vs_memory = mem_bytes_at i len a.vs_memory` by
    (fs[typed_copy_frame_def, loweringStateRelDefsTheory.regions_disjoint_def] >>
     rpt gen_tac >> disch_tac >> first_x_assum irule >> decide_tac) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by fs[wb_frame_def, locals_kept_def] >>
  `!name b len. local_region ce es.scopes s0 name b len ==>
     regions_disjoint off n b len` by
    (rpt strip_tac >> first_assum irule >> qexists_tac `name` >> irule local_region_frame_fwd >>
     qexistsl_tac [`s0`,`sa`,`es.scopes`] >> fs[wb_frame_def]) >>
  conj_tac
  >- (qpat_x_assum `wb_frame _ _ _ _ _ _`
        (strip_assume_tac o PURE_REWRITE_RULE[wb_frame_def]) >>
      pure_rewrite_tac[wb_frame_def] >> conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then strip_assume_tac) >>
          simp[] >> first_assum irule >> simp[]) >>
      conj_tac >- (rpt strip_tac >> gvs[] >> first_assum irule >> simp[]) >>
      conj_tac
      >- (rpt strip_tac >> suspend "old_bytes") >>
      irule locals_kept_regions_tail >> qexists_tac `a` >> simp[] >>
      rpt strip_tac >> first_assum irule >> first_assum irule >> simp[] >>
      qexists_tac `n'` >> simp[]) >>
  `!b len i. regions_disjoint off n b len /\ b <= i /\ i < b + len /\
      i IN tz.t_mem ==> i IN ta.t_mem` by
    (rpt strip_tac >> fs[loweringStateRelDefsTheory.regions_disjoint_def] >>
     qpat_assum `!i. _ ==> (i IN tz.t_mem <=> _)` (qspec_then `i` mp_tac) >>
     impl_tac >- decide_tac >> simp[]) >>
  irule unwrap_slot_copy_ghost_kept_at >> qexistsl_tac [`Ga`,`ta`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> rename1 `local_region ce es.scopes s0 name b len` >>
      qpat_assum `!name b len. local_region ce es.scopes s0 name b len ==> _`
        (drule_then assume_tac) >>
      qpat_assum `!b len i. regions_disjoint _ _ b len /\ _ ==> _`
        (qspecl_then [`b`,`len`,`i`] mp_tac) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> rename1 `FLOOKUP s0.vs_allocas aid = SOME (b,len)` >>
      qpat_assum `!aid b len. FLOOKUP s0.vs_allocas aid = SOME (b,len) /\ _ ==> _`
        (drule_all_then assume_tac) >>
      qpat_assum `!b len i. regions_disjoint _ _ b len /\ _ ==> _`
        (qspecl_then [`b`,`len`,`i`] mp_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!i. _ ==> (i IN tz.t_mem <=> _)` (qspec_then `i` mp_tac) >>
  impl_tac >- decide_tac >> simp[]
QED

Resume default_copy_caller_frame[old_bytes]:
  rename1 `FLOOKUP s0.vs_allocas aid = SOME (b,len)` >>
  qpat_assum `!aid b len. FLOOKUP s0.vs_allocas aid = SOME (b,len) /\ _ ==> regions_disjoint _ _ _ _`
    (drule_all_then assume_tac) >>
  `mem_bytes_at b len z.vs_memory = mem_bytes_at b len a.vs_memory` by simp[] >>
  pop_assum SUBST1_TAC >>
  first_assum irule >> conj_tac >- (first_assum ACCEPT_TAC) >> qexists_tac `aid` >> simp[]
QED

Finalise default_copy_caller_frame

Triviality default_copy_owned_value:
  evaluate_type (get_tenv cx) ty = SOME rt /\ val_wf rt v /\
  value_has_type rt v /\ lookup_var q z = SOME w /\
  FLOOKUP z.vs_allocas aid = SOME (w2n w,type_memory_size rt) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!name b len. local_region ce ee.scopes z name b len ==>
     w2n w + type_memory_size rt <= b \/ b + len <= w2n w) /\
  (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
     val_in_memory rt v (w2n w) mem) ==>
  vv_holds_mods ce cx ty (Value v) (LocatedValue ty (mk_ptr (Var q) LocMemory)) ee z /\
  vv_at ce cx ty sa sb ee (Value v) (LocatedValue ty (mk_ptr (Var q) LocMemory)) z /\
  vv_own ce cx ty sa sb ee (Value v) (LocatedValue ty (mk_ptr (Var q) LocMemory)) z
Proof
  strip_tac >>
  `val_in_memory rt v (w2n w) z.vs_memory` by
    (first_assum irule >> simp[mem_agree_outside_def]) >>
  conj_tac
  >- (simp[vv_holds_mods_def,vv_holds_def,mk_ptr_def,eval_operand_def,
           read_result_def,return_def] >>
      strip_tac >> irule val_in_memory_word_type >> simp[] >>
      qexistsl_tac [`ty`,`get_tenv cx`] >> simp[]) >>
  `val_footprint rt v <= type_memory_size rt` by simp[val_footprint_le] >>
  conj_tac
  >- (irule allocated_vv_at >> simp[eval_operand_def,read_result_def,return_def] >>
      qexistsl_tac [`type_memory_size rt`,`aid`,`w2n w`] >>
      simp[] >> rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >>
      decide_tac) >>
  simp[vv_own_def,mk_ptr_def,eval_operand_def,read_result_def,return_def] >>
  disj1_tac >> qexistsl_tac [`aid`,`w2n w`,`type_memory_size rt`] >>
  simp[] >> rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> decide_tac
QED

(* The final cursor and history come from the executed control suffix.  The
   typed frame below compares the allocation cut with that same endpoint. *)
Theorem extcall_default_copy_post_mods:
  expr_type e = ty /\ lowered_value_type ce e = ty /\ post_value_type ce e = ty /\
  expr_has_effect e /\
  evaluate_type (get_tenv cx) ty = SOME rt /\ val_wf rt v /\ value_has_type rt v /\
  type_memory_bytes ce ty = type_memory_size rt /\
  stmt_state_rel H ctx func ce cx ee a /\ storage_well_formed_on cx ee (FST H) /\
  immutable_frame_mods func ce cx ee a /\ ghost_inv_at_mods (DF H) lo d ce cx ee Ga ta a /\
  wb_frame ce es ee sa s0 a /\ ghost_kept_at lo ce es sa G0 tn0 s0 Ga ta /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce k /\
  (!x. not_fresh_at sa x ==> not_fresh_at k x) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  sa.cs_next_id <= inst.inst_id /\ inst.inst_id < sb.cs_next_id /\
  FLOOKUP a.vs_allocas inst.inst_id = SOME (w2n w,type_memory_size rt) /\
  lo <= w2n w /\ w2n w + type_memory_size rt <= a.vs_alloca_next /\
  s0.vs_alloca_next <= a.vs_alloca_next /\
  (!aid b len. FLOOKUP s0.vs_allocas aid = SOME (b,len) /\ aid < sa.cs_next_id ==>
    regions_disjoint (w2n w) (type_memory_size rt) b len) /\
  (!name b len. local_region ce ee.scopes a name b len ==>
    regions_disjoint (w2n w) (type_memory_size rt) b len) /\
  typed_copy_state_frame k (w2n w) (type_memory_size rt) a z /\
  lookup_var q a = SOME w /\ not_fresh_at k q /\
  ptr_covers Ga ta q a (type_memory_size rt) /\
  tz.t_imm = ta.t_imm /\ tz.t_stor = ta.t_stor /\ tz.t_trans = ta.t_trans /\
  (!i. ~(w2n w <= i /\ i < w2n w + type_memory_size rt) ==>
    (i IN tz.t_mem <=> i IN ta.t_mem)) /\
  (!x. not_fresh_at k x ==> FLOOKUP Gz x = FLOOKUP Ga x /\
    op_taint tz (Var x) = op_taint ta (Var x)) /\
  (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
    val_in_memory rt v (w2n w) mem) /\
  z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func z ==>
  let vv = LocatedValue ty (mk_ptr (Var q) LocMemory) in
    vv_post_mods H ctx func ce cx e es sa sb s0 ee (Value v) vv z /\
    vv_store_bound cx ty ty ee (Value v) vv z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z /\
    ptr_vv_ok cx ty (Value v) vv ee Gz tz z /\
    ptr_buf_ok ce e (Var q) Gz z /\
    vv_own ce cx ty sa sb ee (Value v) vv z /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gz tz
Proof
  simp[] >> strip_tac >>
  `a.vs_allocas = z.vs_allocas /\ a.vs_alloca_next = z.vs_alloca_next /\
   typed_copy_frame (w2n w) (type_memory_size rt) a.vs_memory z.vs_memory /\
   (!x. not_fresh_at k x ==> lookup_var x z = lookup_var x a)` by
    fs[typed_copy_state_frame_def,venom_state_component_equality] >>
  `stmt_state_rel H ctx func ce cx ee z` by
    (irule typed_copy_semantic_frame >>
     goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ a z`)) >>
     goal_assum (drule_at (Pat `MEM inst (fn_insts func)`)) >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!name b len. local_region ce ee.scopes a name b len ==> regions_disjoint _ _ _ _`
       (drule_then mp_tac) >> simp[regions_disjoint_def] >> decide_tac) >>
  `immutable_frame_mods func ce cx ee z` by
    (irule ifexp_typed_immutable_frame_mods >>
     goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ a z`)) >>
     goal_assum (drule_at (Pat `MEM inst (fn_insts func)`)) >> simp[]) >>
  `ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z` by suspend "ghost" >>
  `wb_frame ce es ee sa s0 z /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gz tz` by
    suspend "writeback" >>
  `ptr_covers Gz tz q z (type_memory_size rt)` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`Ga`,`a`,`ta`] >> simp[]) >>
  `lookup_var q z = SOME w` by
    (qpat_assum `!x. not_fresh_at k x ==> lookup_var x z = _` (drule_then SUBST1_TAC) >> simp[]) >>
  `!name b len. local_region ce ee.scopes z name b len ==>
      w2n w + type_memory_size rt <= b \/ b + len <= w2n w` by suspend "regions" >>
  `FLOOKUP z.vs_allocas inst.inst_id = SOME (w2n w,type_memory_size rt)` by fs[] >>
  drule_all default_copy_owned_value >> strip_tac >>
  conj_tac >- suspend "value_post" >>
  suspend "pointer_post"
QED

Resume extcall_default_copy_post_mods[ghost]:
  qpat_assum `stmt_state_rel H ctx func ce cx ee a`
    (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
  irule ifexp_typed_copy_ghost_mods >>
  goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ a z`)) >>
  goal_assum (drule_at (Pat `local_ptrs_rel func ce ee.scopes a`)) >>
  goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ Ga ta a`)) >> simp[] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume extcall_default_copy_post_mods[writeback]:
  irule default_copy_caller_frame >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `typed_copy_frame _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ghost_kept_at lo ce es sa G0 tn0 s0 Ga ta`)) >>
  simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  `not_fresh_at k x` by (first_assum irule >> simp[]) >> simp[]
QED

Resume extcall_default_copy_post_mods[regions]:
  rpt strip_tac >>
  `local_region ce ee.scopes a name b len` by
    (irule (iffLR local_region_lookup_cong) >>
     goal_assum (drule_at (Pat `local_region _ _ z _ _ _`)) >> rpt strip_tac >>
     rename1 `FLOOKUP ce.ce_vars nm = SOME (PtrVar (Var p) sz)` >>
     `not_fresh_at k p` by
       (qpat_assum `local_ptrs_reserved ce k`
          (strip_assume_tac o PURE_REWRITE_RULE [local_ptrs_reserved_def]) >>
        first_x_assum (drule_then strip_assume_tac) >> simp[]) >> simp[]) >>
  qpat_assum `!name b len. local_region ce ee.scopes a name b len ==> regions_disjoint _ _ _ _`
    (drule_then mp_tac) >> simp[regions_disjoint_def] >> decide_tac
QED

Resume extcall_default_copy_post_mods[value_post]:
  qpat_assum `wb_frame ce es ee sa s0 z`
    (strip_assume_tac o PURE_REWRITE_RULE [wb_frame_def]) >>
  simp[vv_post_mods_def,vv_place_ptr_mods_def,vv_place_ptr_def] >>
  first_assum ACCEPT_TAC
QED

Resume extcall_default_copy_post_mods[pointer_post]:
  `val_store_size rt v <= type_memory_size rt` by simp[val_store_size_le] >>
  qpat_assum `ptr_covers Gz tz q z _`
    (strip_assume_tac o PURE_REWRITE_RULE [ptr_covers_def]) >>
  simp[vv_store_bound_def,ptr_vv_ok_def,ptr_mem_ok_def,ptr_buf_ok_def,
       mk_ptr_def,eval_operand_def,read_result_def,return_def] >>
  gvs[] >> decide_tac
QED

Finalise extcall_default_copy_post_mods
