Theory vyperImmutableMetadataFrame
Ancestors
  list option pair finite_map alist vyperAST vyperState vyperInterpreter
  vyperCallOutcomeFrame vyperPlaceFrames vyperStatePreservation
  vyperImmutablesPreservation vyperCreate vyperCreateFrame vyperCallFrame
  vyperMachineFrame vyperEvalFrame

(* Resolved immutable paths retain their declared type across expression effects.
   Values may change; presence and declared type metadata may not. *)
Definition immutable_metadata_frame_def:
  immutable_metadata_frame (st:evaluation_state) (st':evaluation_state) <=>
    (!addr. IS_SOME (ALOOKUP st.immutables addr) <=>
            IS_SOME (ALOOKUP st'.immutables addr)) /\
    (!addr imms imms' src id.
       ALOOKUP st.immutables addr = SOME imms /\
       ALOOKUP st'.immutables addr = SOME imms' ==>
       OPTION_MAP FST (FLOOKUP (get_source_immutables src imms) id) =
       OPTION_MAP FST (FLOOKUP (get_source_immutables src imms') id))
End

Theorem immutable_metadata_frame_refl[simp]:
  immutable_metadata_frame st st
Proof
  rw[immutable_metadata_frame_def] >> gvs[]
QED

Theorem immutable_metadata_frame_eq:
  st'.immutables = st.immutables ==> immutable_metadata_frame st st'
Proof
  rw[immutable_metadata_frame_def] >> gvs[]
QED

Theorem immutable_metadata_frame_trans:
  immutable_metadata_frame s t /\ immutable_metadata_frame t u ==>
  immutable_metadata_frame s u
Proof
  rw[immutable_metadata_frame_def] >>
  `?middle. ALOOKUP t.immutables addr = SOME middle` by
    (Cases_on `ALOOKUP t.immutables addr` >> gvs[] >>
     qpat_x_assum `!addr. IS_SOME (ALOOKUP t.immutables _) <=> _`
       (qspec_then `addr` mp_tac) >> simp[]) >>
  metis_tac[]
QED

Theorem set_immutable_existing_metadata_frame:
  get_immutables cx src st = (INL imms,st) /\
  FLOOKUP imms id = SOME (tv,old) /\
  set_immutable cx src id tv v st = (res,st') ==>
  immutable_metadata_frame st st'
Proof
  rw[get_immutables_def, get_address_immutables_def, set_immutable_def,
     set_address_immutables_def, bind_def, lift_option_type_def,
     return_def, raise_def, vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  gvs[immutable_metadata_frame_def, get_source_immutables_def,
      set_source_immutables_def, FLOOKUP_UPDATE, AllCaseEqs()] >>
  rw[ALOOKUP_ADELKEY] >> gvs[ALOOKUP_ADELKEY, FLOOKUP_UPDATE] >>
  Cases_on `src = src'` >> gvs[ALOOKUP_ADELKEY, FLOOKUP_UPDATE] >>
  Cases_on `id = id'` >> gvs[FLOOKUP_UPDATE]
QED

Theorem write_place_immutable_metadata_frame:
  write_place cx (ImmutablePlace src id path) v st = (res,st') ==>
  immutable_metadata_frame st st'
Proof
  simp[write_place_def, bind_def, ignore_bind_def, lift_option_type_def,
       lift_sum_def, vyperMiscTheory.option_CASE_rator,
       vyperMiscTheory.sum_CASE_rator, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  `s'' = st` by metis_tac[vyperStatePreservationTheory.get_immutables_state, SND] >>
  gvs[] >>
  PairCases_on `tva` >> gvs[] >>
  drule_all set_immutable_existing_metadata_frame >> simp[]
QED

Theorem write_place_metadata_frame:
  write_place cx p v st = (res,st') ==> immutable_metadata_frame st st'
Proof
  Cases_on `p`
  >- metis_tac[write_storage_place_immutables, immutable_metadata_frame_eq]
  >- metis_tac[write_memory_place_immutables, immutable_metadata_frame_eq] >>
  metis_tac[write_place_immutable_metadata_frame]
QED

Theorem append_place_metadata_frame:
  !cx p v st res st'.
    append_place cx p v st = (res,st') ==> immutable_metadata_frame st st'
Proof
  rpt gen_tac >> Cases_on `p`
  >- (strip_tac >> irule immutable_metadata_frame_eq >>
      metis_tac[vyperScopePreservationTheory.append_storage_place_scopes_immutables]) >>
  pure_rewrite_tac [append_place_def, bind_def] >>
  qmatch_goalsub_abbrev_tac `place_type_value cx pl st` >>
  Cases_on `place_type_value cx pl st` >>
  drule place_type_value_state >> strip_tac >> gvs[] >>
  rename1 `place_type_value cx pl s0 = (tvres,s0)` >>
  Cases_on `tvres` >> simp[bind_def, raise_def] >>
  Cases_on `read_place cx pl s0` >>
  drule read_place_state >> strip_tac >> gvs[] >>
  rename1 `read_place cx pl s1 = (oldres,s1)` >>
  Cases_on `oldres` >> simp[bind_def, raise_def] >>
  qmatch_goalsub_abbrev_tac `append_element tv old v` >>
  Cases_on `append_element tv old v` >>
  simp[lift_sum_def, return_def, raise_def] >>
  metis_tac[write_place_metadata_frame]
QED

Theorem pop_place_metadata_frame:
  !cx p st res st'. pop_place cx p st = (res,st') ==>
    immutable_metadata_frame st st'
Proof
  rpt gen_tac >> Cases_on `p`
  >- (strip_tac >> irule immutable_metadata_frame_eq >>
      metis_tac[vyperScopePreservationTheory.pop_storage_place_scopes_immutables])
  >- (rename1 `MemoryPlace id path` >> strip_tac >>
      Cases_on `find_containing_scope id st.scopes` >>
      gvs[pop_place_def, bind_def, get_scopes_def, lift_option_type_def,
          return_def, raise_def, immutable_metadata_frame_refl] >> PairCases_on `x` >>
      gvs[bind_def, ignore_bind_def, lift_sum_def, type_check_def, assert_def,
          check_def, set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
      fs[GSYM lift_sum_def, GSYM lift_option_type_def] >>
      imp_res_tac lift_sum_state >> imp_res_tac lift_option_type_state >>
      gvs[immutable_metadata_frame_refl] >>
      pairarg_tac >> gvs[bind_def, ignore_bind_def, set_scopes_def, return_def] >>
      irule immutable_metadata_frame_eq >> simp[]) >>
  simp[pop_place_def, bind_def, ignore_bind_def, lift_option_type_def,
       lift_sum_def, vyperMiscTheory.option_CASE_rator,
       vyperMiscTheory.sum_CASE_rator, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac get_immutables_state >> gvs[] >>
  PairCases_on `tva` >> gvs[] >>
  drule_all set_immutable_existing_metadata_frame >> simp[]
QED

Theorem metadata_eval_frame[local]:
  (!s t u. immutable_metadata_frame s t /\ immutable_metadata_frame t u ==>
           immutable_metadata_frame s u) /\
  (!s t. machine_frame s t ==> immutable_metadata_frame s t) /\
  (!cx p v. state_rel_frame immutable_metadata_frame (write_place cx p v)) /\
  (!cx p v. state_rel_frame immutable_metadata_frame (append_place cx p v)) /\
  (!cx p. state_rel_frame immutable_metadata_frame (pop_place cx p)) /\
  (!ev. state_rel_frame immutable_metadata_frame (push_log ev)) /\
  (!a b n. state_rel_frame immutable_metadata_frame (transfer_value a b n)) /\
  (!cx g vs. state_rel_frame immutable_metadata_frame (eval_send cx g vs)) /\
  (!cx st sk sig opts vs.
     state_rel_frame immutable_metadata_frame (eval_ext_call cx st sk sig opts vs)) /\
  (!cx fl a d m g.
     state_rel_frame immutable_metadata_frame (eval_raw_call cx fl a d m g)) /\
  (!cx k h r ts vs cs.
     state_rel_frame immutable_metadata_frame (eval_create cx k h r ts vs cs)) /\
  (!a n v. state_rel_frame immutable_metadata_frame
             (acquire_nonreentrant_lock a n v)) /\
  (!a n. state_rel_frame immutable_metadata_frame (release_nonreentrant_lock a n))
Proof
  rewrite_tac[state_rel_frame_result] >> rpt conj_tac >> rpt gen_tac
  >- metis_tac[immutable_metadata_frame_trans]
  >- simp[machine_frame_def, immutable_metadata_frame_eq]
  >- metis_tac[write_place_metadata_frame]
  >- metis_tac[append_place_metadata_frame]
  >- metis_tac[pop_place_metadata_frame]
  >- (strip_tac >> irule immutable_metadata_frame_eq >>
      gvs[push_log_def, return_def])
  >- metis_tac[concrete_send_step_locals, immutable_metadata_frame_eq]
  >- metis_tac[eval_send_preserves_non_accounts, immutable_metadata_frame_eq]
  >- metis_tac[eval_ext_call_preserves_non_accounts, immutable_metadata_frame_eq]
  >- metis_tac[eval_raw_call_preserves_non_accounts, immutable_metadata_frame_eq]
  >- metis_tac[eval_create_preserves_scopes_immutables, immutable_metadata_frame_eq]
  >- metis_tac[acquire_nonreentrant_lock_immutables, immutable_metadata_frame_eq] >>
  metis_tac[release_nonreentrant_lock_immutables, immutable_metadata_frame_eq]
QED

Theorem eval_metadata_frame_with_results =
  REWRITE_RULE [state_rel_frame_result]
    (MATCH_MP eval_state_rel_frame metadata_eval_frame);


Theorem eval_metadata_frame_mutual:
  (!cx s st res st'. eval_stmt cx s st = (res,st') ==> immutable_metadata_frame st st') /\
  (!cx ss st res st'. eval_stmts cx ss st = (res,st') ==> immutable_metadata_frame st st') /\
  (!cx it st res st'. eval_iterator cx it st = (res,st') ==> immutable_metadata_frame st st') /\
  (!cx tyv nm body vs st res st'. eval_for cx tyv nm body vs st = (res,st') ==> immutable_metadata_frame st st') /\
  (!cx e st res st'. eval_expr cx e st = (res,st') ==> immutable_metadata_frame st st') /\
  (!cx es st res st'. eval_exprs cx es st = (res,st') ==> immutable_metadata_frame st st') /\
  (!cx t st res st'. eval_base_place cx t st = (res,st') ==> immutable_metadata_frame st st') /\
  (!cx t st res st'. eval_target_place cx t st = (res,st') ==> immutable_metadata_frame st st') /\
  (!cx g v st res st'. assign_tuple_targets cx g v st = (res,st') ==> immutable_metadata_frame st st') /\
  (!cx gs vs st res st'. assign_tuple_target_list cx gs vs st = (res,st') ==> immutable_metadata_frame st st')
Proof
  metis_tac[eval_metadata_frame_with_results]
QED

Theorem eval_expr_results_immutable_metadata_frame:
  eval_expr_results cx es st = (res,st') ==> immutable_metadata_frame st st'
Proof
  metis_tac[eval_metadata_frame_with_results]
QED

Theorem eval_expr_immutable_metadata_frame:
  eval_expr cx e st = (res,st') ==> immutable_metadata_frame st st'
Proof
  metis_tac[eval_metadata_frame_mutual]
QED

Theorem immutable_metadata_frame_lookup:
  immutable_metadata_frame st st' /\
  get_immutables cx src st = (INL imms,st) /\
  FLOOKUP imms id = SOME (tv,v) ==>
  ?imms' v'. get_immutables cx src st' = (INL imms',st') /\
    FLOOKUP imms' id = SOME (tv,v')
Proof
  rpt strip_tac >>
  qpat_x_assum `get_immutables _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [get_immutables_def, get_address_immutables_def, bind_def,
       lift_option_type_def, return_def, raise_def,
       vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  strip_tac >> fs[] >>
  `?imms'. ALOOKUP st'.immutables cx.txn.target = SOME imms'` by
    (fs[immutable_metadata_frame_def] >>
     qpat_x_assum `!addr. IS_SOME _ <=> _`
       (qspec_then `cx.txn.target` mp_tac) >>
     Cases_on `ALOOKUP st'.immutables cx.txn.target` >> simp[]) >>
  gvs[] >>
  fs[immutable_metadata_frame_def] >>
  first_x_assum (drule_all_then (qspecl_then [`src`,`id`] mp_tac)) >>
  simp[] >> strip_tac >> PairCases_on `z` >> gvs[] >> metis_tac[]
QED
