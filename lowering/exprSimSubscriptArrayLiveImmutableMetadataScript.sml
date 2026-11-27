(* Transport captured immutable root metadata without preserving its value. *)
Theory exprSimSubscriptArrayLiveImmutableMetadata
Ancestors
  exprSimSubscriptArrayLiveImmutableView exprSimHypsDefs vyperTypeInvariants
  exprSimProps targetSubscriptMemory vyperPlaceTyping loweringPosts
  vyperEvalPreservesScopes vyperTypeEnvPreservation vyperState finite_map words option[qualified,ignore_grammar]

Theorem live_immutable_captured_root:
  expr_sim_inv cenv cx env t /\
  (~cx_const_name cx (src,id) \/
   IS_SOME (FLOOKUP env.bare_global_assignable (src,id))) /\
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
      qpat_x_assum `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty /\ _ ==> _`
        (qspecl_then [`src`,`id`,`root_ty`] mp_tac) >>
      simp[] >> strip_tac >> gvs[]) >>
  metis_tac[]
QED


Theorem live_immutable_captured_array_view:
  expr_sim_inv cenv cx env t /\ expr_sim_inv cenv cx env ee /\
  (~cx_const_name cx (src,id) /\
   IS_SOME (FLOOKUP env.bare_global_assignable (src,id))) /\
  stmt_state_rel H ctx func cenv cx ee s /\
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
    value_has_type (ArrayTV etv bd) v /\
    well_formed_type_value (ArrayTV etv bd) /\
    read_result cx (PlaceR (ImmutablePlace src id path)) ee = (INL v,ee) /\
    vv_place_ptr cenv cx ee s (PlaceR (ImmutablePlace src id path))
      (LocatedValue (ArrayT et bd) p) /\
    immutable_holds cenv cx (ArrayT et bd)
      (PlaceR (ImmutablePlace src id path)) (n2w (off+k)) ee s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `vv_place_ptr _ _ _ _ _ _`
    (strip_assume_tac o SRULE [loweringPostsTheory.vv_place_ptr_def]) >>
  `off + type_memory_size itv < dimword (:256) /\
     ?root_ty. FLOOKUP env.bare_globals (src,id) = SOME root_ty /\
       evaluate_type (get_tenv cx) root_ty = SOME itv` by
    (mp_tac (live_immutable_captured_root |> Q.INST
      [`cenv` |-> `cenv`, `cx` |-> `cx`, `env` |-> `env`, `t` |-> `t`,
       `src` |-> `src`, `id` |-> `id`, `off` |-> `off`, `itv` |-> `itv`,
       `iv` |-> `iv`]) >> simp[]) >>
  qpat_x_assum `expr_sim_inv _ _ _ t`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
  `src = cenv.ce_module` by
    (qpat_assum `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty /\
          (~cx_const_name cx (src,id) \/ IS_SOME (FLOOKUP env.bare_global_assignable (src,id))) ==> _`
       (qspecl_then [`src`,`id`,`root_ty`] mp_tac) >>
     simp[] >> disch_tac >> (metis_tac [optionTheory.IS_SOME_EXISTS, env_consistent_def, env_context_consistent_def])) >>
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
  qpat_assum `src = cenv.ce_module` SUBST_ALL_TAC >>
  `eval_operand p.ptr_operand s = SOME (n2w (off+k))` by metis_tac[] >>
  qexistsl_tac [`off`,`itv`,`k`] >> simp[] >>
  mp_tac (live_immutable_array_current_view |> Q.INST
    [`src` |-> `cenv.ce_module`, `s` |-> `s`, `root_ty` |-> `root_ty`,
     `path` |-> `path`, `p` |-> `p`, `off` |-> `off`, `k` |-> `k`,
     `itv` |-> `itv`, `id` |-> `id`, `func` |-> `func`, `etv` |-> `etv`,
     `et` |-> `et`, `ctx` |-> `ctx`, `bd` |-> `bd`, `H` |-> `H`]) >>
  `?iv' v.
      FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) id = SOME (itv,iv') /\
      evaluate_subscripts itv iv' path = INL v /\
      value_has_type (ArrayTV etv bd) v /\
      well_formed_type_value (ArrayTV etv bd) /\
      k + type_memory_size (ArrayTV etv bd) <= type_memory_size itv /\
      read_result cx (PlaceR (ImmutablePlace cenv.ce_module id path)) ee = (INL v,ee) /\
      vv_place_ptr cenv cx ee s (PlaceR (ImmutablePlace cenv.ce_module id path))
        (LocatedValue (ArrayT et bd) p) /\
      immutable_holds cenv cx (ArrayT et bd)
        (PlaceR (ImmutablePlace cenv.ce_module id path)) (n2w (off+k)) ee s` by
    (irule live_immutable_array_current_view >> simp[] >>
     conj_tac
     >- (qexistsl_tac [`env`,`root_ty`] >> simp[])
     >- (qexistsl_tac [`H`,`ctx`,`func`] >> simp[])) >>
  disch_tac >> qexistsl_tac [`iv'`,`v`] >> simp[] >> metis_tac [arithmeticTheory.ADD_COMM]
QED
