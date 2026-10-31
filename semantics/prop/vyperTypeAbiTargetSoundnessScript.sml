(* TOP-LEVEL: target_place_pop_sound, abi_target_operand_pop_sound.
   Source typing supplies both a live, writable place and a valid ABI capture.
   Projected immutable targets retain genuine immutable-arena operands; no
   future-read readiness premise is imposed on callers. *)
Theory vyperTypeAbiTargetSoundness
Ancestors
  vyperAST vyperState vyperTypeSystem vyperTypeExprSoundness
  vyperTypeEvalSoundness vyperTargetPlaceWrite vyperTypeAbiPlaceSoundness
  vyperAbiExprTyping vyperAbiReadTyping vyperTypeEnv vyperTypeInvariants vyperValue

Theorem target_place_pop_sound:
  runtime_consistent env cx st /\ well_typed_expr env (Pop elem_ty bt) /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
  eval_target_place cx bt st = (res,rt) ==>
  runtime_consistent env cx rt /\ no_type_error_result res /\
  case res of
  | INL p => ?n.
      eval_result_typed (env,cx,rt) (PlaceR p)
        (Type (ArrayT elem_ty (Dynamic n))) /\
      runtime_place_writable cx rt p /\ live_memory_result rt (PlaceR p)
  | INR _ => T
Proof
  strip_tac >> fs[Once well_typed_expr_def] >>
  `well_typed_target env bt (ArrayT elem_ty (Dynamic n))` by
    simp[well_typed_target_def] >>
  fs[runtime_consistent_def] >>
  drule_all (cj 1 (SPEC_ALL (cj 8 eval_scc_type_sound_mutual))) >> strip_tac >>
  drule_all (cj 3 (SPEC_ALL (cj 8 eval_scc_type_sound_mutual))) >> strip_tac >>
  drule_all (cj 4 (SPEC_ALL (cj 8 eval_scc_type_sound_mutual))) >> strip_tac >>
  Cases_on `res` >> gvs[runtime_consistent_def, writable_place_result_def] >>
  goal_assum drule >> simp[]
QED

Theorem abi_target_operand_pop_sound:
  runtime_consistent env cx st /\ well_typed_expr env (Pop elem_ty bt) /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
  eval_target_place cx bt st = (INL p,target_st) /\
  abi_place_operand cx p target_st = (res,rt) ==>
  runtime_consistent env cx rt /\ no_type_error_result res /\
  case res of
  | INL arg => ?n tv.
      evaluate_type env.type_defs elem_ty = SOME tv /\
      abi_operand_valid rt (ArrayTV tv (Dynamic n)) arg /\
      (~?v. arg = AbiSnapshot v)
  | INR _ => T
Proof
  strip_tac >> drule_all target_place_pop_sound >> strip_tac >>
  gvs[eval_result_typed_def, evaluate_type_def, AllCaseEqs()] >>
  `!src id. p <> ImmutablePlace src id []` by
    (fs[Once well_typed_expr_def] >>
     irule mutable_target_not_direct_immutable >> goal_assum drule >>
     qexists_tac `env` >> fs[well_typed_target_def, runtime_consistent_def]) >>
  fs[runtime_consistent_def] >> drule_all abi_place_operand_valid >> strip_tac >>
  Cases_on `res` >> gvs[runtime_consistent_def] >> goal_assum drule >> simp[]
QED
