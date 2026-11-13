(* Current immutable contents at a captured typed path. *)
Theory exprSimSubscriptArrayLiveImmutableView
Ancestors
  exprSimPopImmutableTarget targetSubscriptMemory exprSimSubscriptArraySource
  exprSimProps loweringPosts loweringStateRelDefs exprSimHypsDefs
  vyperTypeEnv vyperTypeInvariants vyperTypeSystem vyperState finite_map words

Theorem live_immutable_root_current:
  expr_sim_inv cenv cx env ee /\
  FLOOKUP env.bare_globals (src,id) = SOME root_ty /\
  evaluate_type (get_tenv cx) root_ty = SOME itv ==>
  ?iv. FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
            NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
         SOME (itv,iv)
Proof
  rpt strip_tac >>
  `env_immutables_consistent env cx ee` by
    fs[expr_sim_inv_def, env_consistent_def] >>
  Cases_on `ALOOKUP ee.immutables cx.txn.target` >>
  gvs[env_immutables_consistent_def, get_source_immutables_def] >>
  `IS_SOME (FLOOKUP (case ALOOKUP x src of
                      NONE => FEMPTY | SOME imm => imm) id)` by metis_tac[] >>
  Cases_on `FLOOKUP (case ALOOKUP x src of
                     NONE => FEMPTY | SOME imm => imm) id` >> gvs[] >>
  PairCases_on `x'` >>
  `evaluate_type (get_tenv cx) root_ty = SOME x'0` by metis_tac[] >>
  gvs[]
QED

Theorem live_immutable_path_holds:
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
       NONE => FEMPTY | SOME imms => get_source_immutables cenv.ce_module imms) id =
    SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,tvt) /\
  evaluate_subscripts itv iv path = INL v /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  off + type_memory_size itv < dimword (:256) ==>
  immutable_holds cenv cx ty
    (PlaceR (ImmutablePlace cenv.ce_module id path)) (n2w (off+k)) ee s
Proof
  rpt strip_tac >>
  `value_has_type tvt v /\ well_formed_type_value tvt` by
    (drule_all imm_place_at_value_type >> simp[]) >>
  `value_has_type itv iv /\ well_formed_type_value itv` by
    (irule imm_place_at_value_type >> goal_assum (drule_at Any) >>
     qexistsl_tac [`cenv`, `env`, `0`, `[]`] >>
     simp[mem_path_offset_def, evaluate_subscripts_def]) >>
  `sub_layout itv iv k tvt v` by
    (simp[sub_layout_def] >> conj_tac
     >- metis_tac[mem_path_offset_sound] >> rpt strip_tac >>
     irule mem_path_offset_current_value >> goal_assum (drule_at Any) >>
     qexists_tac `path` >> simp[]) >>
  simp[immutable_holds_def] >>
  qexistsl_tac [`id`, `off`, `itv`, `iv`, `k`, `v`] >> simp[] >>
  Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[] >>
  simp[read_result_def, read_place_def, get_immutables_def,
       get_address_immutables_def, bind_def, lift_option_type_def,
       lift_sum_def, return_def]
QED

Theorem live_immutable_array_current_view:
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  src = cenv.ce_module /\
  FLOOKUP env.bare_globals (src,id) = SOME root_ty /\
  evaluate_type (get_tenv cx) root_ty = SOME itv /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  off + type_memory_size itv < dimword (:256) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  eval_operand p.ptr_operand s = SOME (n2w (off+k)) /\
  p.ptr_location = LocCode /\
  (!itv iv. FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
       NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
    SOME (itv,iv) ==> ?v. evaluate_subscripts itv iv path = INL v) ==>
  ?iv v.
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
       NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
      SOME (itv,iv) /\
    evaluate_subscripts itv iv path = INL v /\
    value_has_type (ArrayTV etv bd) v /\
    well_formed_type_value (ArrayTV etv bd) /\
    k + type_memory_size (ArrayTV etv bd) <= type_memory_size itv /\
    read_result cx (PlaceR (ImmutablePlace src id path)) ee = (INL v,ee) /\
    vv_place_ptr cenv cx ee s (PlaceR (ImmutablePlace src id path))
      (LocatedValue (ArrayT et bd) p) /\
    immutable_holds cenv cx (ArrayT et bd)
      (PlaceR (ImmutablePlace src id path)) (n2w (off+k)) ee s
Proof
  rpt strip_tac >>
  drule_all live_immutable_root_current >> strip_tac >>
  `?v. evaluate_subscripts itv iv path = INL v` by metis_tac[] >>
  `value_has_type (ArrayTV etv bd) v /\
   well_formed_type_value (ArrayTV etv bd)` by
    (drule_all imm_place_at_value_type >> simp[]) >>
  `k + type_memory_size (ArrayTV etv bd) <= type_memory_size itv` by
    metis_tac[mem_path_offset_sound] >>
  `immutable_holds cenv cx (ArrayT et bd)
      (PlaceR (ImmutablePlace src id path)) (n2w (off+k)) ee s` by
    (qpat_assum `src = cenv.ce_module` SUBST_ALL_TAC >>
     drule_all live_immutable_path_holds >> simp[]) >>
  qexistsl_tac [`iv`, `v`] >> simp[vv_place_ptr_def] >>
  conj_tac
  >- (Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[] >>
      simp[read_result_def, read_place_def, get_immutables_def,
           get_address_immutables_def, bind_def, lift_option_type_def,
           lift_sum_def, return_def]) >>
  qexistsl_tac [`off`, `itv`, `iv`, `k`, `ArrayTV etv bd`] >> gvs[]
QED
