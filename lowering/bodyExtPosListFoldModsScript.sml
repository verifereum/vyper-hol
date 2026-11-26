(* Fold a reached head and tail at their actual linked run endpoints. *)
Theory bodyExtPosListFoldMods
Ancestors
  bodyECRecoverOperandReturnConsMods bodyForcedStorageFrameMods
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  exprSimWordArgs vyperStorageFootprint vyperStorageTrace vyperInterpreter vyperState
Libs monadsyntax

val head = ``bind (eval_expr cx e) (read_result cx)``;

Theorem ext_pos_list_fold_mods:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    ^head (es,s,G,tn)
    (\H res mid G1 tn1 t. ?v. res = INL v /\ HeadQ H v mid G1 tn1 t) HeadR /\
  (!obs v mid G1 tn1 t.
     ^head (es with gas_obs := obs) = (INL v,mid) /\
     mid.gas_obs = [] /\ storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==> HeadQ H v mid G1 tn1 t) ==>
     gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
       (eval_exprs cx xs) (mid,t,G1,tn1)
       (\H res ee G2 tn2 u. ?vs. res = INL vs /\ TailQ mid t G1 tn1 H vs ee G2 tn2 u)
       TailR) /\
  (!H obs0 obs v mid G1 tn1 t vs ee G2 tn2 u.
     ^head (es with gas_obs := obs0) = (INL v,mid) /\
     eval_exprs cx xs (mid with gas_obs := obs) = (INL vs,ee) /\
     mid.gas_obs = [] /\ ee.gas_obs = [] /\
     valid_horizon cx st0 H ee.storage_trace /\
     HeadQ H v mid G1 tn1 t /\ TailQ mid t G1 tn1 H vs ee G2 tn2 u ==>
     Q H (INL (v::vs)) ee G2 tn2 u) /\
  (!H res mid gt r. HeadR H res mid gt r ==> ?ex. res = INR ex /\ R H (INR ex) mid gt r) /\
  (!H v res ee gt r. TailR H res ee gt r ==>
     R H (case res of INL vs => INL (v::vs) | INR ex => INR ex) ee gt r) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_exprs cx (e::xs)) (es,s,G,tn) Q R
Proof
  strip_tac >> rewrite_tac[eval_exprs_cons_action] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- irule bodyForcedStorageFrameModsTheory.bop_forced_storage_frame
  >~ [`storage_trace_frame (bind (eval_exprs _ _) _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_return] >>
  qexists_tac `\H res mid G1 tn1 t.
    mid.gas_obs = [] /\ ?v. res = INL v /\ HeadQ H v mid G1 tn1 t` >>
  BETA_TAC >> reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ ^head _ _ _` (irule_at Any) >> simp[]) >>
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _` (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> HeadQ H v mid G1 tn1 t` by
    (qx_gen_tac `hh` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
       (qspec_then `hh` (drule_then strip_assume_tac)) >> gvs[]) >>
  `^head (es with gas_obs := gas_explicit marks s.vs_gas_readings) = (INL v,mid)` by
    (`mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     qpat_assum `mid with gas_obs := [] = mid` (fn frame =>
       qpat_assum `!tail. ^head _ = _` (qspec_then `[]`
          (ACCEPT_TAC o PURE_REWRITE_RULE [listTheory.APPEND_NIL,frame])))) >>
  qpat_assum `!obs v mid G1 tn1 t. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (drule_all_then assume_tac) >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  suspend "tail"
QED

Resume ext_pos_list_fold_mods[tail]:
  `gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_exprs cx xs) (mid,t,G1,tn1)
    (\H res ee G2 tn2 u. ?vs obs. res = INL vs /\
      eval_exprs cx xs (mid with gas_obs := obs) = (INL vs,ee) /\
      TailQ mid t G1 tn1 H vs ee G2 tn2 u) TailR` by
    (irule gas_outcome_full_mods_post_source >>
     qpat_assum `gas_outcome_full_mods _ _ _ _ (eval_exprs _ _) _ _ _` (irule_at Any) >>
     BETA_TAC >> simp[] >> rpt gen_tac >> strip_tac >>
     qexistsl_tac [`vs`,`xs'`] >> simp[] >>
     `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
     qpat_assum `ee with gas_obs := [] = ee` (fn frame =>
       qpat_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `[]`
         (mp_tac o PURE_REWRITE_RULE [listTheory.APPEND_NIL,frame]))) >>
     simp[]) >>
  irule gas_outcome_full_mods_post_source >>
  irule_at Any ecrecover_operand_return_cons_mods >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (eval_exprs _ _) _ (\H res ee G2 tn2 u. ?vs obs. _) TailR`
    (irule_at Any) >>
  BETA_TAC >> reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >> first_x_assum drule >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `eval_exprs cx xs (mid with gas_obs := obs) = _`
       (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame) >>
     simp[evaluate_storage_trace_frame]) >>
  `HeadQ H v mid G1 tn1 t` by simp[] >>
  qpat_assum `!H obs0 obs v mid G1 tn1 t vs ee G2 tn2 u. _ ==> Q _ _ _ _ _ _`
    (drule_all_then ACCEPT_TAC)
QED

Finalise ext_pos_list_fold_mods
