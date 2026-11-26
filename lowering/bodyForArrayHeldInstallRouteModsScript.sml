(* Keep the selected local, rather than an arbitrary covering region, when
   installing the condition header for a memory-place iterator. *)
Theory bodyForArrayHeldInstallRouteMods
Ancestors
  bodyForArrayEntryMods bodyForArrayHeaderInstallMods bodyFullTargetArrayLoad
  exprBodyPreProps nameLoweringProps vyperPlaceTyping stateRelProj
  bodyFullPostsMods loweringPosts loweringStateRelDefs exprSimProps
  exprSimHypsDefs vyperTypeInvariants exprSimCopy ptrDiscipline venomState words
  option finite_map arithmetic

Theorem held_local_type[local]:
  expr_sim_inv_mods mods c cx env em /\ lookup_scopes name em.scopes = SOME ent ==>
  ?ty. c.ce_var_type name = SOME ty /\
       evaluate_type (get_tenv cx) ty = SOME ent.type
Proof
  simp[expr_sim_inv_mods_def,env_consistent_def,env_scopes_consistent_def] >>
  strip_tac >>
  `IS_SOME (FLOOKUP env.var_types name)` by
    (qpat_assum `!id entry. _` (drule_then ACCEPT_TAC)) >>
  Cases_on `FLOOKUP env.var_types name` >> gvs[] >> metis_tac[]
QED

Theorem held_named_root[local]:
  expr_sim_inv_mods mods c cx env em /\
  runtime_place_typed cx em (MemoryPlace name path) tv /\
  stmt_state_rel H ctx func c cx em r /\
  vv_place_ptr c cx em r (PlaceR (MemoryPlace name path)) (LocatedValue ann p) /\
  eval_operand p.ptr_operand r = SOME bw ==>
  ?q b sz ent k. lookup_scopes name em.scopes = SOME ent /\
    FLOOKUP c.ce_vars name = SOME (PtrVar (Var q) sz) /\
    lookup_var q r = SOME b /\ mem_path_offset ent.type path = SOME (k,tv) /\
    bw = b + n2w k /\ w2n b + k < dimword (:256) /\
    w2n b <= w2n bw /\ w2n bw + type_memory_size tv <= w2n b + sz
Proof
  simp[runtime_place_typed_memory,vv_place_ptr_def] >> strip_tac >>
  drule_all_then strip_assume_tac held_local_type >> gvs[] >>
  drule mem_path_offset_sound >> strip_tac >> gvs[] >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_all_then strip_assume_tac local_ptrs_rel_value >>
  gvs[eval_operand_def] >>
  rename1 `lookup_var q r = SOME b` >>
  `local_region c em.scopes r name (w2n b) sz` by
    (simp[local_region_def] >> goal_assum (drule_at Any) >> simp[]) >>
  `w2n b + sz < dimword (:256)` by
    (drule_then strip_assume_tac stmt_state_rel_region_lt >> first_assum drule >> simp[]) >>
  `w2n (b + n2w k) = w2n b + k` by
    (irule buffer_offset_no_wrap >> qexists_tac `sz` >> simp[] >> decide_tac) >>
  simp[] >> goal_assum (drule_at Any) >> qexistsl_tac [`q`,`k`] >> simp[] >> decide_tac
QED

Theorem held_named_extent[local]:
  expr_sim_inv_mods mods c cx env em /\
  runtime_place_typed cx em (MemoryPlace name path) tv /\
  stmt_state_rel H ctx func c cx em r /\
  vv_place_ptr c cx em r (PlaceR (MemoryPlace name path)) (LocatedValue ann p) /\
  eval_operand p.ptr_operand r = SOME bw ==>
  ?q b sz ent. lookup_scopes name em.scopes = SOME ent /\
    FLOOKUP c.ce_vars name = SOME (PtrVar (Var q) sz) /\
    lookup_var q r = SOME b /\ w2n b <= w2n bw /\
    w2n bw + type_memory_size tv <= w2n b + sz
Proof
  strip_tac >>
  drule_all_then strip_assume_tac held_named_root >>
  qexistsl_tac [`q`,`b`,`sz`,`ent`] >> gvs[]
QED

Theorem held_length_operand[local]:
  array_length_frame sbExpr r Gr traw u Gu tu /\ copy_old_operand sbExpr op ==>
  eval_operand op u = eval_operand op r
Proof
  simp[array_length_frame_def,copy_old_operand_def] >> strip_tac >>
  `u.vs_labels = r.vs_labels` by
    (qpat_assum `_ with vs_vars := _ = r` (once_rewrite_tac o single o SYM) >> simp[]) >>
  Cases_on `op` >> gvs[eval_operand_def]
QED

Theorem held_install_provenance[local]:
  for_array_install_frame_mods saL u Gu tu G tn t /\ copy_old_operand saL op ==>
  op_prov G op = op_prov Gu op
Proof
  Cases_on `op` >> simp[for_array_install_frame_mods_def,copy_old_operand_def,op_prov_def]
QED

Theorem for_array_held_install_route_mods:
  vv_post_mods H ctx func c cx e es sa0 sbExpr s0 em
    (PlaceR (MemoryPlace name path)) (LocatedValue ann p) r /\
  expr_sim_inv_mods mods c cx env em /\
  runtime_place_typed cx em (MemoryPlace name path) (ArrayTV tv bd) /\
  evaluate_type (get_tenv cx) sty = SOME tv /\
  value_has_type (ArrayTV tv bd) (ArrayV av) /\
  vs = MAP Value (array_elements (ArrayTV tv bd) av) /\
  read_result cx (PlaceR (MemoryPlace name path)) em = (INL (ArrayV av),em) /\
  eval_operand p.ptr_operand u = SOME bw /\
  copy_old_operand sbExpr p.ptr_operand /\ copy_old_operand saL p.ptr_operand /\
  local_ptrs_reserved c sbExpr /\ local_ptrs_reserved c saL /\
  array_length_frame sbExpr r Gr traw u Gu tu /\
  for_array_install_frame_mods saL u Gu tu G tn t /\
  for_array_memory_backing_mods cx sty bd tv av p.ptr_operand bw (u,Gu,tu) (t,tn) ==>
  for_array_entry_route_mods c cx lo (sty,bd,LocMemory) (em,sbExpr,u,Gu,tu)
    (p.ptr_operand,bw) vs (ForArrayHeld name path av) hor vs em G tn t
Proof
  strip_tac >>
  drule_all_then assume_tac held_install_provenance >>
  simp[for_array_entry_route_mods_def] >> strip_tac >>
  qhdtm_x_assum `vv_post_mods`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  qhdtm_x_assum `vv_place_ptr_mods`
    (assume_tac o SIMP_RULE (srw_ss()) [vv_place_ptr_mods_def]) >>
  `eval_operand p.ptr_operand r = SOME bw` by
    (drule_all held_length_operand >> simp[]) >>
  drule_all_then strip_assume_tac held_named_extent >>
  `not_fresh_at sbExpr q /\ not_fresh_at saL q` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `lookup_var q u = SOME b` by fs[array_length_frame_def] >>
  `lookup_var q t = SOME b` by fs[for_array_install_frame_mods_def] >>
  qexistsl_tac [`w2n b`,`sz`] >> simp[local_region_def] >>
  qexistsl_tac [`ent`,`q`,`b`] >> simp[]
QED

Theorem for_array_held_length_root_mods:
  vv_post_mods H ctx func c cx e es sa0 sbExpr s0 em
    (PlaceR (MemoryPlace name path)) (LocatedValue ann p) r /\
  expr_sim_inv_mods mods c cx env em /\
  runtime_place_typed cx em (MemoryPlace name path) (ArrayTV tv bd) /\
  eval_operand p.ptr_operand u = SOME bw /\
  copy_old_operand sbExpr p.ptr_operand /\
  local_ptrs_reserved c sbExpr /\ local_ptrs_reserved c saL /\
  array_length_frame sbExpr r Gr traw u Gu tu ==>
  ?ent q sz rw delta. lookup_scopes name em.scopes = SOME ent /\
    FLOOKUP c.ce_vars name = SOME (PtrVar (Var q) sz) /\
    lookup_var q u = SOME rw /\ not_fresh_at saL q /\
    mem_path_offset ent.type path = SOME (delta,ArrayTV tv bd) /\
    bw = rw + n2w delta /\ w2n rw + delta < dimword (:256) /\
    w2n rw <= w2n bw /\ w2n bw + type_memory_size (ArrayTV tv bd) <= w2n rw + sz
Proof
  strip_tac >>
  qhdtm_x_assum `vv_post_mods`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  qhdtm_x_assum `vv_place_ptr_mods`
    (assume_tac o SIMP_RULE (srw_ss()) [vv_place_ptr_mods_def]) >>
  `eval_operand p.ptr_operand r = SOME bw` by
    (drule_all held_length_operand >> simp[]) >>
  drule_all_then strip_assume_tac held_named_root >>
  `not_fresh_at sbExpr q /\ not_fresh_at saL q` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `lookup_var q u = SOME b` by fs[array_length_frame_def] >>
  qexistsl_tac [`ent`,`q`,`sz`,`b`,`k`] >> gvs[]
QED
