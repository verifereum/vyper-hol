(* The memory header of the actual place reached by a linked Pop. *)
Theory bodyPopReachedMemoryMods
Ancestors
  bodyWriteTargetStageMods exprSimPopNestedLocalHandoff bodyFullShadowBodyInv
  bodyPtrBopInMemoryContents targetSubscriptMemory abiEncodeOwnership
  typedCopyLayoutPtr valueEncoding valueEncodingProps vyperPlaceStatePreservation
  exprSimHypsDefs vyperTypeInvariants vyperTyping
  loweringPosts bodyFullTargetDefs exprSimProps venomState
  ptrDiscipline bodyPtrDefs words arithmetic

Theorem reached_root_type[local]:
  expr_sim_inv_mods mods cenv cx env es /\ env_consistent env cx ee /\
  lookup_scopes id ee.scopes = SOME entry ==>
  ?ty. cenv.ce_var_type id = SOME ty /\
       evaluate_type (get_tenv cx) ty = SOME entry.type
Proof
  strip_tac >>
  fs[env_consistent_def, env_scopes_consistent_def] >>
  `IS_SOME (FLOOKUP env.var_types id)` by
    (qpat_assum `!name v. lookup_scopes _ _ = _ ==> _` (drule_then ACCEPT_TAC)) >>
  Cases_on `FLOOKUP env.var_types id` >> gvs[] >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
  qpat_assum `!name ty. FLOOKUP env.var_types name = _ ==> cenv.ce_var_type name = _`
    (drule_then assume_tac) >>
  qpat_assum `!name ty ent. _ /\ _ ==> evaluate_type _ _ = SOME ent.type`
    (drule_all_then assume_tac) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem reached_memory_target_post[local]:
  write_target_post_mods H D lo d ctx func cenv cx bt es sa sm s0 ee
    (PlaceR (MemoryPlace id path)) (Type aty) dst G0 tn0 G tn s ==>
  target_post H ctx func cenv cx es sa sm s0 ee
    (PlaceR (MemoryPlace id path)) (Type aty) dst s /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) dst G tn s /\
  ghost_inv_at_mods D lo d cenv cx ee G tn s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s)
Proof
  strip_tac >> drule_then strip_assume_tac write_target_post_view_mods >>
  fs[write_target_location_mods_def, target_post_def, wb_frame_def] >>
  first_assum ACCEPT_TAC
QED

Theorem reached_memory_robust_layout[local]:
  ghost_inv_at_mods D lo d cenv cx ee G tn s /\
  lookup_scopes id ee.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root) sz) /\
  lookup_var root s = SOME b /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  mem_path_offset entry.type path = SOME (k,ArrayTV etv (Dynamic cap)) ==>
  ptr_covers G tn root s sz /\ allocas_from lo s /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory entry.type entry.value (w2n b) m) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs))
         (w2n b + k) m)
Proof
  strip_tac >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  qpat_x_assum `!name v p sz. lookup_scopes _ _ = _ /\ _ ==> _`
    (drule_all_then strip_assume_tac) >> simp[] >>
  rpt strip_tac >>
  drule_at (Pat `mem_path_offset _ _ = _`) mem_path_offset_current_value >>
  disch_then (drule_at (Pat `evaluate_subscripts _ _ _ = _`)) >> simp[]
QED

Theorem reached_header_covers[local]:
  ptr_covers G tn root s sz /\ lookup_var root s = SOME b /\
  eval_operand hdr s = SOME w /\ w2n w = w2n b + k /\
  k + len <= sz /\ op_taint tn hdr = {} /\
  op_prov G hdr = FLOOKUP G root ==>
  ?p. hdr = Var p /\ lookup_var p s = SOME w /\ ptr_covers G tn p s len
Proof
  Cases_on `hdr` >>
  gvs[ptr_covers_def, op_prov_def, eval_operand_def] >>
  strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> decide_tac
QED

Theorem reached_array_bounds[local]:
  value_has_type tv a /\ well_formed_type_value tv /\
  subscripts_type tv path = SOME (ArrayTV etv (Dynamic cap)) /\
  evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\
  k + type_memory_size (ArrayTV etv (Dynamic cap)) <= sz ==>
  LENGTH vs <= cap /\ cap < dimword (:256) /\ LENGTH vs < dimword (:256) /\
  (vs <> [] ==>
   k + 32 + (LENGTH vs - 1) * type_memory_size etv + type_memory_size etv <= sz)
Proof
  strip_tac >>
  drule_all_then assume_tac evaluate_subscripts_type >>
  drule_all_then assume_tac subscripts_type_well_formed >>
  `LENGTH vs <= cap` by fs[value_has_type_def] >>
  `cap < dimword (:256)` by fs[well_formed_type_value_def] >>
  `LENGTH vs < dimword (:256)` by decide_tac >> simp[] >>
  strip_tac >>
  `LENGTH vs * type_memory_size etv <= cap * type_memory_size etv` by simp[] >>
  `(LENGTH vs - 1) * type_memory_size etv + type_memory_size etv =
   LENGTH vs * type_memory_size etv` by
    (Cases_on `vs` >> gvs[MULT_CLAUSES]) >>
  qpat_x_assum `k + type_memory_size _ <= sz` mp_tac >>
  pure_rewrite_tac[type_memory_size_def] >> decide_tac
QED

(* The post can be used at any supplied H, in particular at the reached
   trace's own valid horizon. The extracted address and layout have no H. *)
Theorem pop_reached_memory_header_mods:
  write_target_post_mods (H : (bool # bytes32 # type_value) list # num list) D lo d ctx func cenv cx bt es sa sm s0 ee
    (PlaceR (MemoryPlace id path)) (Type aty) (hdr,loc,pt) G0 tn0 G tn s /\
  expr_sim_inv_mods mods cenv cx env es /\ env_consistent env cx ee /\
  lookup_scopes id ee.scopes = SOME entry /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  subscripts_type entry.type path = SOME (ArrayTV etv (Dynamic cap)) /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) ==>
  loc = SOME LocMemory /\ pt = SOME (value_type_place (Type aty)) /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV etv (Dynamic cap)) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ?root_ty root b sz k p w.
    cenv.ce_var_type id = SOME root_ty /\
    evaluate_type (get_tenv cx) root_ty = SOME entry.type /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root) sz) /\
    lookup_var root s = SOME b /\ ptr_covers G tn root s sz /\
    local_region cenv ee.scopes s id (w2n b) sz /\
    w2n b + sz < dimword (:256) /\ w2n b + sz <= s.vs_alloca_next /\
    type_memory_size entry.type <= sz /\ val_wf entry.type entry.value /\
    mem_path_offset entry.type path = SOME (k,ArrayTV etv (Dynamic cap)) /\
    local_path_at cenv cx id k (ArrayTV etv (Dynamic cap)) /\
    k + type_memory_size (ArrayTV etv (Dynamic cap)) <= sz /\ k + 32 <= sz /\
    w = b + n2w k /\ w2n w = w2n b + k /\
    hdr = Var p /\ eval_operand hdr s = SOME w /\
    lookup_var p s = SOME w /\ not_fresh_at sm p /\
    op_taint tn (Var p) = {} /\ FLOOKUP G p = FLOOKUP G root /\
    ptr_covers G tn p s 32 /\ w2n w + 32 <= s.vs_alloca_next /\
    w2n w + 32 < dimword (:256) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
         val_in_memory entry.type entry.value (w2n b) m) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
         val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs))
           (w2n w) m) /\
    mem_word_taint tn.t_mem (w2n w) = {} /\
    mload (w2n w) s = n2w (LENGTH vs) /\
    LENGTH vs <= cap /\ cap < dimword (:256) /\ LENGTH vs < dimword (:256) /\
    (vs <> [] ==>
     k + 32 + (LENGTH vs - 1) * type_memory_size etv + type_memory_size etv <= sz)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac reached_root_type >>
  drule_then strip_assume_tac reached_memory_target_post >>
  drule_all_then strip_assume_tac memory_target_encoding_handoff >>
  `tv = ArrayTV etv (Dynamic cap)` by
    (drule_then strip_assume_tac mem_path_offset_sound >> fs[]) >>
  qpat_x_assum `tv = _` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac reached_memory_robust_layout >>
  drule_all_then strip_assume_tac reached_array_bounds >>
  drule_all_then assume_tac abi_encode_local_region_frontier >>
  `k + 32 <= sz` by fs[type_memory_size_def] >>
  `op_taint tn hdr = {} /\ op_prov G hdr = FLOOKUP G p` by
    (qpat_assum `target_ptr_ok _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [target_ptr_ok_def]) >> fs[] >>
     qpat_assum `!p sz. FLOOKUP _ _ = _ ==> _` (drule_then ACCEPT_TAC)) >>
  `?hp. hdr = Var hp /\ lookup_var hp s = SOME w /\ ptr_covers G tn hp s 32` by
    (drule_all_then ACCEPT_TAC reached_header_covers) >>
  `mem_word_taint tn.t_mem (w2n b + k) = {}` by
    (irule dynarray_memory_header_clean >> goal_assum (drule_at Any)) >>
  `mload (w2n b + k) s = n2w (LENGTH vs)` by
    (drule dynarray_in_memory_robust_length >>
     disch_then (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, mem_word_at_eq_mload]) >>
  gvs[op_prov_def]
QED
