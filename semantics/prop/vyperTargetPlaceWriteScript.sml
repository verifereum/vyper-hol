(* TOP-LEVEL: writable target places and their extension boundary.
   Helpers keep declared mutable paths separate from dynamic bounds. *)
Theory vyperTargetPlaceWrite
Ancestors
  list option pair finite_map alist vyperState vyperMisc vyperTyping
  vyperTypeSystem vyperTypeInvariants vyperTypeExprSoundness
  vyperPlaceTyping vyperPlaceResultTyping vyperPlaceWriteSoundness
  vyperPlaceFrames vyperStatePreservation vyperImmutableMetadataFrame[ignore_grammar]

Definition writable_place_result_def:
  writable_place_result cx st (PlaceR p) = runtime_place_writable cx st p /\
  writable_place_result cx st (ValueR v) = T
End

Theorem writable_place_result_frame:
  scope_pop_trace st.scopes events st'.scopes /\
  vyperImmutableMetadataFrame$immutable_metadata_frame st st' /\
  writable_place_result cx st pv ==> writable_place_result cx st' pv
Proof
  Cases_on `pv` >> simp[writable_place_result_def] >> Cases_on `p`
  >- simp[runtime_place_writable_def]
  >- (simp[runtime_place_writable_def] >> rpt strip_tac >>
      drule_all scope_pop_trace_lookup >> strip_tac >>
      drule entry_pop_trace_metadata >> metis_tac[]) >>
  simp[runtime_place_writable_def] >> rpt strip_tac >>
  drule_all immutable_metadata_frame_lookup >> strip_tac >> metis_tac[]
QED

Theorem lookup_global_place_writable:
  lookup_global_place cx src id st = (res,st') ==>
  (case res of INL pv => writable_place_result cx st' pv | INR _ => T)
Proof
  simp[lookup_global_place_def, bind_def, lift_option_type_def,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
      var_decl_info_CASE_rator, bind_def, lift_option_type_def, return_def,
      raise_def, AllCaseEqs(), writable_place_result_def,
      runtime_place_writable_def, mutable_place_path_def] >>
  imp_res_tac get_immutables_state >> gvs[] >> PairCases_on `tvv` >> metis_tac[]
QED

Theorem mutable_place_path_append:
  !path tv etv sb.
    mutable_place_path tv path /\ subscripts_type tv path = SOME etv /\
    mutable_place_path etv [sb] ==>
    mutable_place_path tv (path ++ [sb])
Proof
  Induct >> simp[subscripts_type_def] >> rpt gen_tac >>
  Cases_on `h` >> TRY (rename1 `ValueSubscript key` >> Cases_on `key`) >>
  Cases_on `tv` >>
  simp[mutable_place_path_def, subscript_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> first_x_assum irule >> simp[]
QED

Theorem extend_memory_place_writable:
  runtime_place_writable cx st p /\ runtime_place_typed cx st p tv /\
  mutable_place_path tv [sb] ==>
  runtime_place_writable cx st (extend_memory_place p sb)
Proof
  Cases_on `p` >>
  simp[extend_memory_place_def, runtime_place_writable_def,
       runtime_place_typed_memory, runtime_place_typed_immutable] >>
  rpt strip_tac >> gvs[] >>
  drule_all mutable_place_path_append >> metis_tac[]
QED

Theorem target_path_step_mutable:
  evaluate_type env.type_defs ty = SOME tv /\
  target_path_step_type env (Type ty) sb out ==>
  mutable_place_path tv [sb]
Proof
  Cases_on `ty` >> simp[target_path_step_type_def] >>
  rpt strip_tac
  >- (Cases_on `sb` >> gvs[] >> Cases_on `v` >>
      gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), mutable_place_path_def]) >>
  Cases_on `sb` >> gvs[] >>
  drule_all attribute_type_runtime_step >> strip_tac >>
  Cases_on `tv` >> gvs[subscript_type_def, mutable_place_path_def]
QED

Theorem extend_storage_place_writable:
  extend_storage_place cx tr slot tv sb st = (INL p,st') ==>
  runtime_place_writable cx st' p
Proof
  Cases_on `tv` >> Cases_on `sb` >>
  simp[extend_storage_place_def, raise_def] >>
  TRY (Cases_on `v` >> simp[extend_storage_place_def, raise_def]) >>
  simp[bind_def, ignore_bind_def, return_def, AllCaseEqs(),
       lift_option_type_def, check_def, assert_def, raise_def] >>
  rpt strip_tac >> gvs[runtime_place_writable_def] >>
  pairarg_tac >> gvs[return_def, runtime_place_writable_def]
QED

Theorem extend_mapping_place_writable:
  extend_target_place cx (ValueR (HashMapRef tr slot kt vt)) sb st = (INL pv,st') ==>
  writable_place_result cx st' pv
Proof
  Cases_on `sb` >>
  simp[extend_target_place_def, extend_place_def, get_Value_def,
       bind_def, lift_sum_def, return_def, raise_def,
       evaluate_subscript_def, AllCaseEqs(), subscript_result_place_def] >>
  rpt strip_tac >>
  gvs[vyperMiscTheory.sum_CASE_rator, return_def, raise_def, AllCaseEqs(),
      subscript_result_place_def, writable_place_result_def, runtime_place_writable_def]
QED

Theorem extend_target_place_writable:
  writable_place_result cx st pv /\ place_result_typed env cx st pv vt /\
  target_path_step_type env vt sb out /\
  extend_target_place cx pv sb st = (INL next,st') ==>
  writable_place_result cx st' next
Proof
  Cases_on `pv`
  >- (Cases_on `vt` >> simp[place_result_typed_def] >> rpt strip_tac >>
      `mutable_place_path tv [sb]` by
        (drule_all target_path_step_mutable >> simp[]) >>
      Cases_on `p`
      >- (gvs[extend_target_place_def, extend_place_def, bind_def,
              return_def, AllCaseEqs()] >>
          drule extend_storage_place_writable >>
          simp[writable_place_result_def]) >>
      imp_res_tac vyperPlaceFramesTheory.extend_target_place_state >>
      gvs[extend_target_place_def, extend_place_def, bind_def,
          ignore_bind_def, return_def, AllCaseEqs(), writable_place_result_def] >>
      drule_all extend_memory_place_writable >> simp[]) >>
  Cases_on `t` >> simp[extend_target_place_def, raise_def] >>
  metis_tac[SRULE[extend_target_place_def] extend_mapping_place_writable]
QED
