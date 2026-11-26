(* Positive memory Pop: the post at the endpoint of the supplied run. *)
Theory bodyPopMemoryPostMods
Ancestors
  bodyPopLocalRepresentationMods bodyPopLocalFrameMods
  exprSimPopNestedLocalPost exprSimPopNestedLocalPtrs
  bodyFullPostsMods exprSimMemDefs mstoreRestorePtr
  vyperLookup exprSimSource bodyPtrDefs loweringPosts loweringStateRelDefs
  valueEncodingProps valueEncodingDefs compileEnv exprLowering typedMemoryCopy
  exprSimProps exprSimPopNestedLocalMemory context venomState vyperAST
  bodyWriteTargetStageMods exprLoweringProps vyperState exprSimHypsDefs
  arithmetic words pred_set finite_map

Theorem pop_memory_scope_update[local]:
  find_containing_scope id mid.scopes = SOME (pre,sc,entry,rest) /\
  ef = mid with scopes := pre ++ sc |+ (id,entry') :: rest ==>
  ef = mid with scopes := ef.scopes /\ MAP FDOM ef.scopes = MAP FDOM mid.scopes /\
  lookup_scopes id ef.scopes = SOME entry' /\
  (!j. j <> id ==> lookup_scopes j ef.scopes = lookup_scopes j mid.scopes)
Proof
  strip_tac >> drule_then strip_assume_tac find_containing_scope_structure >>
  drule_then assume_tac find_containing_scope_pre_none >>
  `id IN FDOM sc` by fs[FLOOKUP_DEF] >>
  simp[FDOM_FUPDATE, ABSORPTION_RWT, lookup_scopes_update, lookup_scopes_update_other]
QED

Theorem pop_memory_robust_encoding[local]:
  mutable_place_path tv path /\ value_has_type tv a /\ well_formed_type_value tv /\
  val_wf tv a /\ mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic cap)) /\
  evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  assign_subscripts tv a path (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated /\
  val_wf tv updated /\ val_wf etv (LAST vs) /\
  (!m. mem_agree_outside old s.vs_memory m ==> val_in_memory tv a b m) /\
  new = old DIFF {i | b+k <= i /\ i < b+k+32} /\
  u.vs_memory = (mstore (b+k) (n2w (LENGTH vs-1)) s).vs_memory ==>
  !m. mem_agree_outside new u.vs_memory m ==>
    val_in_memory tv updated b m /\
    val_in_memory etv (LAST vs) (b+k+32+(LENGTH vs-1)*type_memory_size etv) m
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `?orig. mem_agree_outside old s.vs_memory orig /\
    !i. mem_bytes_at i 1 (mstore (b+k) (n2w (LENGTH vs-1))
      (s with vs_memory := orig)).vs_memory = mem_bytes_at i 1 m` by
    (irule clean_mstore_restore_witness >>
     qpat_x_assum `new = _` SUBST_ALL_TAC >>
     qpat_x_assum `u.vs_memory = _` SUBST_ALL_TAC >> first_assum ACCEPT_TAC) >>
  qpat_assum `!m. mem_agree_outside old _ _ ==> _` (drule_then assume_tac) >>
  `val_in_memory tv a b (s with vs_memory := orig).vs_memory` by simp[] >>
  `!off n. mem_bytes_at off n (mstore (b+k) (n2w (LENGTH vs-1))
       (s with vs_memory := orig)).vs_memory = mem_bytes_at off n m` by
    (irule memory_byte_agree_window >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `sr = s with vs_memory := orig` >>
  qabbrev_tac `stored = (mstore (b+k) (n2w (LENGTH vs-1)) sr).vs_memory` >>
  conj_tac
  >- (irule val_in_memory_footprint_agree >> simp[] >>
      qexists `stored` >> simp[Abbr `stored`] >>
      irule val_in_memory_pop_path >> simp[] >>
      qexistsl_tac [`a`,`etv`,`cap`,`path`] >> simp[]) >>
  irule val_in_memory_footprint_agree >> simp[] >>
  qexists `stored` >> simp_tac bool_ss [Abbr `stored`] >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  `b + (k + (type_memory_size etv * (LENGTH vs-1) + 32)) =
    b+k+32+(LENGTH vs-1)*type_memory_size etv` by simp[] >>
  pop_assum (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
  irule pop_path_elem_in_memory >> simp[] >> qexistsl_tac [`a`,`cap`,`path`,`tv`] >> simp[]
QED

Theorem pop_memory_located_bounds[local]:
  evaluate_type (get_tenv cx) ann = SOME etv /\
  type_memory_bytes cenv ann = type_memory_size etv /\
  read_result cx tv ef = (INL v,ef) /\ val_wf etv v /\
  lookup_var x u = SOME w /\ ptr_covers G tn x u (type_memory_size etv) /\
  w2n w + type_memory_size etv <= u.vs_alloca_next /\
  (!m. mem_agree_outside tn.t_mem u.vs_memory m ==> val_in_memory etv v (w2n w) m) ==>
  vv_store_bound cx ann ann ef tv (LocatedValue ann (mk_ptr (Var x) LocMemory)) u /\
  ptr_vv_ok cx ann tv (LocatedValue ann (mk_ptr (Var x) LocMemory)) ef G tn u /\
  ptr_buf_ok cenv (Pop ann bt) (Var x) G u
Proof
  strip_tac >>
  `val_store_size etv v <= type_memory_size etv` by (irule val_store_size_le >> simp[]) >>
  gvs[ptr_covers_def] >>
  conj_tac
  >- (simp[vv_store_bound_def, mk_ptr_def, eval_operand_def] >> decide_tac) >>
  conj_tac
  >- (simp[ptr_vv_ok_def, mk_ptr_def] >>
      simp[ptr_mem_ok_def, eval_operand_def] >> decide_tac) >>
  simp[ptr_buf_ok_def, lowered_value_type_def, expr_type_def, eval_operand_def]
QED

Theorem pop_memory_linked_vv[local]:
  immutable_frame_mods func cenv cx ef u /\
  vv_post H ctx func cenv cx e es sa sb s0 ef (PlaceR (MemoryPlace id path))
    (LocatedValue ann (mk_ptr op LocMemory)) u ==>
  vv_post_mods H ctx func cenv cx e es sa sb s0 ef (PlaceR (MemoryPlace id path))
    (LocatedValue ann (mk_ptr op LocMemory)) u
Proof
  simp[vv_post_def, vv_post_mods_def, vv_holds_mods_def,
       vv_place_ptr_mods_def, mk_ptr_def] >> metis_tac[]
QED

Theorem pop_memory_positive_post_mods:
  let e = Pop ann bt;
      off = k+32+(LENGTH vs-1)*type_memory_size etv;
      qpath = path ++ [ValueSubscript (IntV &(LENGTH vs-1))];
      tv = PlaceR (MemoryPlace id qpath);
      vv = LocatedValue ann (mk_ptr (Var x) LocMemory)
  in
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  dead_lo_ok_mods H (DF H) lo cenv cx /\ stmt_state_rel H ctx func cenv cx es s0 /\
  write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sm s0 mid
    (PlaceR (MemoryPlace id path)) (Type (ArrayT ann (Dynamic cap))) dst G0 tn0 G tn s /\
  immutable_decl_sep_mods cenv cx mid.scopes s.vs_vars s.vs_allocas s.vs_alloca_next /\
  local_ptrs_reserved cenv sa /\ ci_mono sa sm /\
  (!z cap. cenv.ce_return_buf = SOME (PtrVar (Var z) cap) ==> not_fresh_at sm z) /\
  (!z cap. cenv.ce_return_pc = SOME (PtrVar (Var z) cap) ==> not_fresh_at sm z) /\
  lookup_scopes id mid.scopes = SOME entry /\ popped_keys_indexed mid.scopes /\
  entry.assignable /\ mutable_place_path entry.type path /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  val_wf entry.type entry.value /\
  cenv.ce_var_type id = SOME root_ty /\ evaluate_type (get_tenv cx) root_ty = SOME entry.type /\
  evaluate_type (get_tenv cx) ann = SOME etv /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root) sz) /\ lookup_var root s = SOME b /\
  local_region cenv mid.scopes s id (w2n b) sz /\ type_memory_size entry.type <= sz /\
  k+32 <= sz /\ off + type_memory_size etv <= sz /\
  w2n b + sz <= s.vs_alloca_next /\
  mem_path_offset entry.type path = SOME (k,ArrayTV etv (Dynamic cap)) /\
  subscripts_type entry.type path = SOME (ArrayTV etv (Dynamic cap)) /\
  dynarray_len_untupled cenv id k /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  vs <> [] /\ LENGTH vs <= cap /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory entry.type entry.value (w2n b) m) /\
  u = s with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory; vs_inst_idx := u.vs_inst_idx|> /\
  u.vs_memory = (mstore (w2n b+k) (n2w (LENGTH vs-1)) s).vs_memory /\
  tn'.t_mem = tn.t_mem DIFF {i | w2n b+k <= i /\ i < w2n b+k+32} /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!z. not_fresh_at sm z ==> lookup_var z u = lookup_var z s /\
       FLOOKUP G' z = FLOOKUP G z /\ op_taint tn' (Var z) = op_taint tn (Var z)) /\
  lookup_var x u = SOME w /\ w2n w = w2n b + off /\
  ptr_covers G' tn' x u (type_memory_size etv) /\
  u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) ==>
  ?ef. pop_place cx (MemoryPlace id path) mid = (INL tv,ef) /\
    ef = mid with scopes := ef.scopes /\
    vv_post_mods H ctx func cenv cx e es sa sb s0 ef tv vv u /\
    vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ef tv vv u /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx ef G' tn' u /\
    ptr_vv_ok cx (post_value_type cenv e) tv vv ef G' tn' u /\
    ptr_buf_ok cenv e (Var x) G' u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  drule_then strip_assume_tac lookup_scopes_find_containing_scope >>
  `val_in_memory entry.type entry.value (w2n b) s.vs_memory` by
    simp[mem_agree_outside_def] >>
  drule_all pop_local_representation_mods >>
  disch_then (qspec_then `cx` (qx_choose_then `updated` strip_assume_tac)) >>
  qpat_x_assum `let t = _ in _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM, record_pop_def]) >>
  rename1 `find_containing_scope id mid.scopes = SOME (pre,sc,entry,rest)` >>
  qabbrev_tac `ef = mid with scopes := pre ++ sc |+ (id,entry with <|value := updated;
    popped := (path ++ [ValueSubscript (IntV &(LENGTH vs-1))], LAST vs)::entry.popped|>) :: rest` >>
  `ef = mid with scopes := ef.scopes /\ MAP FDOM ef.scopes = MAP FDOM mid.scopes /\
   lookup_scopes id ef.scopes = SOME (entry with <|value := updated;
     popped := (path ++ [ValueSubscript (IntV &(LENGTH vs-1))], LAST vs)::entry.popped|>) /\
   (!j. j <> id ==> lookup_scopes j ef.scopes = lookup_scopes j mid.scopes)` by
    (irule pop_memory_scope_update >> simp[Abbr `ef`] >>
     goal_assum (drule_at (Pat `find_containing_scope _ _ = _`))) >>
  `value_has_type entry.type updated` by
    (drule_all pop_path_updated_typed >> simp[]) >>
  `val_wf entry.type updated` by simp[valueEncodingTypingTheory.value_has_type_val_wf] >>
  drule_all_then strip_assume_tac pop_path_result_bounds >>
  `!m. mem_agree_outside tn'.t_mem u.vs_memory m ==>
    val_in_memory entry.type updated (w2n b) m /\
    val_in_memory etv (LAST vs) (w2n w) m` by
    (`w2n w = w2n b+k+32+(LENGTH vs-1)*type_memory_size etv` by
       (qpat_assum `w2n w = _` mp_tac >> pure_rewrite_tac [ADD_ASSOC] >> simp[]) >>
     pop_assum (once_rewrite_tac o single) >>
     gen_tac >> disch_tac >> irule pop_memory_robust_encoding >>
     simp[] >> qexistsl_tac [`entry.value`,`cap`,`tn.t_mem`,`path`,`s`,`u`] >>
     qpat_x_assum `mem_agree_outside tn'.t_mem _ _` mp_tac >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx ef u /\ immutable_frame_mods func cenv cx ef u /\
   storage_well_formed_on cx ef (FST H) /\ wb_frame cenv es ef sa s0 u /\
   ghost_inv_at_mods (DF H) lo d cenv cx ef G' tn' u /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'` by suspend "frame" >>
  qexists_tac `ef` >>
  simp_tac bool_ss [lowered_value_type_def, post_value_type_def, expr_type_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "vv" >>
  suspend "bounds"
QED

Resume pop_memory_positive_post_mods[frame]:
  `snapshot_in entry.type (w2n b) sz
     (path ++ [ValueSubscript (IntV &(LENGTH vs-1))], LAST vs) u.vs_memory` by
    (qpat_assum `u.vs_memory = _` (once_rewrite_tac o single) >>
     drule_all_then MATCH_ACCEPT_TAC pop_path_snapshot_in) >>
  drule_all_then assume_tac popped_keys_indexed_lookup_dead >>
  qpat_x_assum `ci_mono sa sm` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  `!m. mem_agree_outside tn'.t_mem u.vs_memory m ==>
       val_in_memory entry.type updated (w2n b) m` by
    (gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >>
  drule_all_then ACCEPT_TAC pop_local_write_frame_mods
QED

Resume pop_memory_positive_post_mods[vv]:
  irule pop_memory_linked_vv >> simp[] >>
  `not_fresh_at sm root` by
    (`local_ptrs_reserved cenv sm` by
       (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
     qpat_x_assum `local_ptrs_reserved cenv sm` mp_tac >>
     simp[local_ptrs_reserved_def] >> metis_tac[]) >>
  `local_region cenv ef.scopes u id (w2n b) sz` by
    (qpat_assum `!z. not_fresh_at sm z ==> _` (drule_then strip_assume_tac) >>
     simp[local_region_def] >> goal_assum (drule_at (Pat `lookup_scopes id ef.scopes = _`)) >>
     qexistsl_tac [`root`,`b`] >> simp[]) >>
  `local_path_at cenv cx id k (ArrayTV etv (Dynamic cap))` by
    (simp[local_path_at_def] >> qexists_tac `path` >> simp[]) >>
  `LENGTH vs - 1 < cap` by (`0 < LENGTH vs` by (Cases_on `vs` >> gvs[]) >> decide_tac) >>
  `mem_path_offset entry.type (path ++ [ValueSubscript (IntV &(LENGTH vs-1))]) =
     SOME (k+32+(LENGTH vs-1)*type_memory_size etv,etv)` by
    (drule mem_path_offset_snoc >>
     disch_then (qspec_then `ValueSubscript (IntV &(LENGTH vs-1))` mp_tac) >>
     simp[mem_step_offset_def]) >>
  `eval_operand (Var x) u = SOME w` by simp[eval_operand_def] >>
  irule (SIMP_RULE (srw_ss()) [expr_type_def]
    (Q.INST [`e` |-> `Pop ann bt`] pop_path_vv_post)) >> simp[local_place_at_def] >>
  qexistsl_tac [`entry.value`,`cap`,`s`,`sz`,`entry.type`] >> simp[]
QED

Resume pop_memory_positive_post_mods[bounds]:
  `u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `u = s with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>` (once_rewrite_tac o single) >> simp[]) >>
  `w2n w + type_memory_size etv <= u.vs_alloca_next` by decide_tac >>
  `type_memory_bytes cenv ann = type_memory_size etv` by
    (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
     qpat_assum `expr_sim_inv_mods _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >> simp[] >> metis_tac[]) >>
  `!m. mem_agree_outside tn'.t_mem u.vs_memory m ==>
       val_in_memory etv (LAST vs) (w2n w) m` by
    (gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >>
  drule_all_then strip_assume_tac pop_memory_located_bounds >> simp[]
QED

Finalise pop_memory_positive_post_mods
