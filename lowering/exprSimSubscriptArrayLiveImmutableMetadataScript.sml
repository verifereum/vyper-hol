(* Transport captured immutable root metadata without preserving its value. *)
Theory exprSimSubscriptArrayLiveImmutableMetadata
Ancestors
  exprSimSubscriptArrayLiveImmutableView exprSimHypsDefs vyperTypeInvariants
  exprSimProps targetSubscriptMemory vyperPlaceTyping loweringPosts
  vyperEvalPreservesScopes vyperTypeEnvPreservation vyperState finite_map words

Theorem live_immutable_captured_root:
  expr_sim_inv cenv cx env t /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP t.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables src imms) id = SOME (itv,iv) ==>
  off + type_memory_size itv < dimword (:256) /\
  ?root_ty. FLOOKUP env.bare_globals (src,id) = SOME root_ty /\
    evaluate_type (get_tenv cx) root_ty = SOME itv
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?root_ty. FLOOKUP env.bare_globals (src,id) = SOME root_ty` by
    (fs[expr_sim_inv_def, bare_globals_layout_def] >> metis_tac[]) >>
  `evaluate_type (get_tenv cx) root_ty = SOME itv` by
    (fs[expr_sim_inv_def, env_consistent_def, env_immutables_consistent_def] >>
     Cases_on `ALOOKUP t.immutables cx.txn.target` >>
     gvs[get_source_immutables_def] >> metis_tac[]) >>
  conj_tac
  >- (fs[expr_sim_inv_def] >>
      qpat_x_assum `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==> _`
        drule >> simp[] >> strip_tac >> gvs[]) >>
  metis_tac[]
QED

Theorem live_immutable_captured_array_view:
  expr_sim_inv cenv cx env t /\ expr_sim_inv cenv cx env ee /\
  stmt_state_rel ctx func cenv cx ee s /\
  vv_place_ptr cenv cx t u (PlaceR (ImmutablePlace src id path))
    (LocatedValue (ArrayT et bd) p) /\
  runtime_place_typed cx t (ImmutablePlace src id path) (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  (!w. eval_operand p.ptr_operand u = SOME w ==>
       eval_operand p.ptr_operand s = SOME w) /\
  (!itv iv. FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables src imms) id = SOME (itv,iv) ==>
    ?v. evaluate_subscripts itv iv path = INL v) ==>
  ?off itv k iv v.
    src = cenv.ce_module /\ p.ptr_location = LocCode /\
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables src imms) id = SOME (itv,iv) /\
    mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
    off + type_memory_size itv < dimword (:256) /\
    eval_operand p.ptr_operand s = SOME (n2w (off+k)) /\
    evaluate_subscripts itv iv path = INL v /\
    value_has_type (ArrayTV etv bd) v /\ well_formed_type_value (ArrayTV etv bd) /\
    read_result cx (PlaceR (ImmutablePlace src id path)) ee = (INL v,ee) /\
    vv_place_ptr cenv cx ee s (PlaceR (ImmutablePlace src id path))
      (LocatedValue (ArrayT et bd) p) /\
    immutable_holds cenv cx (ArrayT et bd)
      (PlaceR (ImmutablePlace src id path)) (n2w (off+k)) ee s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `vv_place_ptr _ _ _ _ _ _`
    (strip_assume_tac o SRULE [loweringPostsTheory.vv_place_ptr_def]) >>
  `mem_path_offset itv path = SOME (k,ArrayTV etv bd)` by
    (drule mem_path_offset_sound >> strip_tac >>
     qpat_x_assum `runtime_place_typed _ _ _ _` mp_tac >>
     simp[vyperPlaceTypingTheory.runtime_place_typed_immutable,
          get_immutables_def, get_address_immutables_def, bind_def,
          lift_option_type_def, return_def, AllCaseEqs()] >>
     rpt strip_tac >>
     Cases_on `ALOOKUP t.immutables cx.txn.target` >>
     gvs[raise_def, return_def]) >>
  `FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off)` by gvs[] >>
  drule_all live_immutable_captured_root >> strip_tac >>
  `eval_operand p.ptr_operand s = SOME (n2w (off+k))` by metis_tac[] >>
  `FLOOKUP env.bare_globals (src,id) = SOME root_ty` by gvs[] >>
  drule_all live_immutable_array_current_view >> strip_tac >>
  qexistsl_tac [`off`,`itv`,`k`,`iv'`,`v`] >> simp[]
QED
