(* Recover the private RHS allocation at the linked storage-target landing.
   The same snapshot can feed either a direct slot copy or typed normalization. *)
Theory bodySlotCopySnapshotMods
Ancestors
  bodyAssignLocalSnapshotMods bodyWriteTargetStageMods bodyFullTargetDefs
  loweringPosts loweringStateRelDefs bodyPtrDefs exprSimProps venomState arithmetic words

(* Only the common, non-immutable part of the linked post is needed
   for the snapshot frame theorem. *)
Theorem storage_snapshot_target_post[local]:
  write_target_post_mods H D lo d ctx func ce cx bt mid ss st u ee
    (PlaceR (StoragePlace tr k dtv)) (Type ty) r G tn Gz tnz z ==>
  assign_target_post F H ctx func ce cx mid ss st u ee (StoragePlace tr k dtv) ty r Gz z
Proof
  simp[assign_target_post_def,target_post_def,write_target_post_mods_def,
       write_target_location_mods_def,wb_frame_def,SF CONJ_ss] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> first_assum ACCEPT_TAC
QED

Theorem slot_copy_snapshot_input_mods:
  ~is_word_type (vv_type vv) /\
  compile_snapshot_vv ce T vv sm = (snap,ss) /\ vv_operand snap = Var x /\
  compile_get_target_ptr compile_expr ce bt ss = (r,st) /\
  unwrap_value ce snap st = (op,su) /\
  write_target_post_mods H D lo d ctx func ce cx bt mid ss st u ee
    (PlaceR (StoragePlace tr k dtv)) (Type ty) r G tn Gz tnz z /\
  stmt_state_rel H ctx func ce cx mid u /\ local_ptrs_reserved ce ss /\
  evaluate_type (get_tenv cx) (vv_type vv) = SOME tv /\ val_wf tv v /\
  FLOOKUP u.vs_allocas aid = SOME (b,type_memory_size tv) /\ aid < ss.cs_next_id /\
  lo <= b /\ b + type_memory_size tv < dimword (:256) /\
  b + type_memory_size tv <= u.vs_alloca_next /\
  (!n off len. local_region ce mid.scopes u n off len ==>
     loweringStateRelDefs$regions_disjoint b (type_memory_size tv) off len) /\
  not_fresh_at ss x /\ lookup_var x u = SOME (n2w b) /\
  ptr_covers G tn x u (type_memory_size tv) /\
  (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==> val_in_memory tv v b mem) ==>
  vv_location snap = SOME LocMemory /\ op = Var x /\ su = st /\
  ~z.vs_halted /\ z.vs_current_bb = su.cs_current_bb /\
  z.vs_inst_idx = LENGTH su.cs_current_insts /\
  not_fresh_at su x /\ (!y. FST r = Var y ==> not_fresh_at su y) /\
  FST (SND r) = SOME (slot_loc tr) /\ SND (SND r) = SOME (ValPT ty) /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\
  eval_operand (FST r) z = SOME k /\ op_prov Gz (FST r) = NONE /\
  op_taint tnz (FST r) = {} /\
  eval_operand op z = SOME (n2w b) /\ lookup_var x z = SOME (n2w b) /\
  op_taint tnz op = {} /\ ptr_covers Gz tnz x z (type_memory_size tv) /\
  lo <= b /\ b + type_memory_size tv < dimword (:256) /\
  w2n (n2w b : 256 word) = b /\ b + type_memory_size tv <= z.vs_alloca_next /\
  (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==> val_in_memory tv v b mem) /\
  FLOOKUP z.vs_allocas aid = SOME (b,type_memory_size tv) /\ aid < su.cs_next_id /\
  (!n off len. local_region ce ee.scopes z n off len ==>
     loweringStateRelDefs$regions_disjoint b (type_memory_size tv) off len) /\
  expr_val_at ce cx (vv_type vv) (ss with cs_next_id := aid) su ee v op z
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_then strip_assume_tac write_target_storage_view_mods >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  drule_then assume_tac storage_snapshot_target_post >>
  `MAP FDOM ee.scopes = MAP FDOM mid.scopes` by fs[wb_frame_def,locals_kept_def] >>
  drule_all_then strip_assume_tac assign_local_snapshot_ready_mods >>
  `op_taint tnz (Var x) = {}` by fs[ptr_covers_def] >>
  `b < dimword (:256)` by decide_tac >>
  `w2n (n2w b : 256 word) = b` by simp[w2n_n2w,LESS_MOD] >>
  simp[eval_operand_def,exprLoweringTheory.value_type_place_def,SF CONJ_ss] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[expr_val_at_def,eval_operand_def] >>
  disj1_tac >> qexistsl_tac [`aid`,`b`,`type_memory_size tv`] >>
  gvs[val_footprint_le] >>
  pure_rewrite_tac[GSYM loweringStateRelDefsTheory.regions_disjoint_def] >>
  first_assum ACCEPT_TAC
QED
