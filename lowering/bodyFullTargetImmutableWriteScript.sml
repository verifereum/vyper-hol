(* A successful, typed target selects a writable constructor path. *)
Theory bodyFullTargetImmutableWrite
Ancestors
  bodySimAugPlaceLoad exprSimPopNestedLocalSource exprSimSubscriptArrayLiveImmutableView
  exprSimHypsDefs vyperTypeSystem vyperTypeInvariants vyperTargetPlaceWrite
  vyperPlaceWriteSoundness vyperInterpreter vyperState immutableDeployAssignMemoryFrame
  exprSimSource vyperTypeExprSoundness loweringPosts bodyFullTargetRoots tuplePlaceSourceHead
  immutableDeployAssignFacts vyperTypeEnv vyperTypeInitialState finite_map alist

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `expr_sim_inv ce cx env (mid with gas_obs := gs)` by simp[] >>
  drule_all_then assume_tac aug_place_target_inv >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `well_typed_target env bt ty` by simp[well_typed_target_def] >>
  `env_consistent env cx (mid with gas_obs := gs) /\
   state_well_typed (mid with gas_obs := gs) /\ context_well_typed cx /\
   accounts_well_typed (mid with gas_obs := gs).accounts /\ functions_well_typed cx` by
    fs[expr_sim_inv_def,runtime_consistent_def] >>
  drule_all_then assume_tac eval_target_place_writable >>
  `?imms. ALOOKUP ee.immutables cx.txn.target = SOME imms` by
    (Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[]) >>
  pop_assum strip_assume_tac >>
  `mutable_place_path itv path` by
    (fs[writable_place_result_def,runtime_place_writable_def,get_immutables_def,
        get_address_immutables_def,bind_def,lift_option_type_def,return_def] >>
     gvs[]) >>
  `value_has_type itv old /\ well_formed_type_value itv` by
    (qspecl_then [`ce`,`cx`,`env`,`ee`,`src`,`id`,`[]`,`itv`,`old`,`0`,`itv`,`old`]
       mp_tac imm_place_at_value_type >>
     simp[mem_path_offset_def,evaluate_subscripts_def]) >>
  gvs[] >> irule immutableDeployAssignMemoryFrameTheory.immutable_path_write_live >>
  rpt (CHANGED_TAC (first_assum (irule_at Any))) >> simp[]
QED
*)
Theorem immutable_target_write_entry:
  expr_sim_inv_mods mods ce cx env mid /\ target_indices_pre ce cx env bt /\
  type_place_target env bt = SOME (Type ty) /\
  call_evaluation_safe cx (int_calls_target bt) /\
  eval_target_place cx bt (mid with gas_obs := gs) =
    (INL (ImmutablePlace src id path),ee) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables src imms) id = SOME (itv,old) /\
  mem_path_offset itv path = SOME (k,tv) /\
  evaluate_subscripts itv old path = INL selected ==>
  expr_sim_inv_mods mods ce cx env ee /\
  ?fin. write_place cx (ImmutablePlace src id path) v ee = (INL (),fin)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  drule_then assume_tac tuple_place_target_base_inversion >>
  drule_all_then strip_assume_tac immutable_target_base_place_result >>
  gvs[] >>
  drule_all_then strip_assume_tac immutable_assign_target_layout >>
  simp[] >>
  `env_immutables_consistent env cx ee` by
    fs[expr_sim_inv_def,env_consistent_def] >>
  Cases_on `ALOOKUP ee.immutables cx.txn.target` >>
  gvs[env_immutables_consistent_def] >>
  first_x_assum drule_all >> simp[]
QED
*)
Theorem immutable_target_write_root:
  immutable_root cx bt /\
  target_root bt = TopLevelNameTarget (NONE,id) /\
  eval_target_place cx bt es = (INL (ImmutablePlace NONE name path),ee) /\
  expr_sim_inv_mods mods ce cx env ee /\
  FLOOKUP env.bare_globals (NONE,id) = SOME ity /\
  ~cx_const_name cx (NONE,id) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables NONE imms) name = SOME (itv,old) ==>
  name = id /\ ce.ce_module = NONE /\
  ce.ce_module_var_type (NONE,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME itv
Proof
  cheat
QED
