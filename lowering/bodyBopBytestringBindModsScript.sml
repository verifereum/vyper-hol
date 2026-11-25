(* The two forced operands feed the comparison at their actual endpoints. *)
Theory bodyBopBytestringBindMods
Ancestors
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods gasExplicitSites
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState compileEnv
  bodyWriteSubscriptSourceMods bodyBranchCellFrameMods exprBodyPreProps
Libs monadsyntax

(* Value prefixes can continue only from a clean, non-halted landing;
   a prefix exception uses the final exit post without running the suffix. *)
Theorem reached_value_bind[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (source : evaluation_state -> value evaluation_result) (es,s,G,tn)
    (\H res ee G' tn' t. ?v. res = INL v /\ P H v ee G' tn' t) (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
  (!marks v ee G' tn' t.
     (!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
              (INL v,ee with gas_obs := tail)) /\
     storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\ ~t.vs_halted /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> P H v ee G' tn' t) ==>
     gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
       (next v) (ee,t,G',tn') Q R) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind source next) (es,s,G,tn) Q R
Proof
  strip_tac >> irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame source`] >- first_assum ACCEPT_TAC
  >~ [`!v. storage_trace_frame (next v)`] >- first_assum ACCEPT_TAC >>
  qexists_tac `\H res ee G' tn' t.
     (?v. res = INL v /\ P H v ee G' tn' t) /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ source _ _ _` (irule_at Any) >> simp[]) >>
  qx_genl_tac [`marks`,`res`,`ee`,`G'`,`tn'`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >> gvs[] >>
  first_x_assum irule >> simp[] >> qexists_tac `marks` >> simp[]
QED

val operand1 = ``bind (eval_expr cx e1) (read_result cx)``;
val operand2 = ``bind (eval_expr cx e2) (read_result cx)``;

Theorem bop_bytestring_bind_mods:
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 ^operand1 (es,s,G,tn)
    (\H res mid G1 tn1 t. ?v1. res = INL v1 /\ P1 H v1 mid G1 tn1 t)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!v1 v2. storage_trace_frame (suffix v1 v2)) /\
  (!m1 v1 mid G1 tn1 t.
     (!tail. ^operand1 (es with gas_obs := gas_explicit m1 s.vs_gas_readings ++ tail) =
              (INL v1,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\ ~t.vs_halted /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==> P1 H v1 mid G1 tn1 t) ==>
     gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cenv.ce_modules cx st0 ^operand2 (mid,t,G1,tn1)
       (\H res ee G2 tn2 u. ?v2. res = INL v2 /\ P2 v1 mid G1 tn1 t H v2 ee G2 tn2 u)
       (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r)) /\
  (!m1 v1 mid G1 tn1 t m2 v2 ee G2 tn2 u.
     (!tail. ^operand1 (es with gas_obs := gas_explicit m1 s.vs_gas_readings ++ tail) =
              (INL v1,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\ ~t.vs_halted /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==> P1 H v1 mid G1 tn1 t) /\
     (!tail. ^operand2 (mid with gas_obs := gas_explicit m2 t.vs_gas_readings ++ tail) =
              (INL v2,ee with gas_obs := tail)) /\
     storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\ ~u.vs_halted /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> P2 v1 mid G1 tn1 t H v2 ee G2 tn2 u) ==>
     gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cenv.ce_modules cx st0 (suffix v1 v2) (ee,u,G2,tn2) Q R) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0
    (bind ^operand1 (\v1. bind ^operand2 (suffix v1))) (es,s,G,tn) Q R
Proof
  strip_tac >> irule reached_value_bind >> BETA_TAC >> rpt conj_tac
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result]
  >~ [`storage_trace_frame (bind (bind _ _) _)`]
  >- simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result] >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  qx_genl_tac [`m1`,`v1`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  irule reached_value_bind >> rpt conj_tac
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result]
  >~ [`storage_trace_frame (suffix _ _)`] >- simp[] >>
  qpat_assum `!m1 v1 mid G1 tn1 t. _ ==> gas_outcome_full_mods _ _ _ _ (bind (eval_expr _ e2) _) _ _ _`
    (irule_at Any) >>
  qexistsl_tac [`v1`,`m1`] >> simp[] >>
  qx_genl_tac [`m2`,`v2`,`ee`,`G2`,`tn2`,`u`] >> strip_tac >>
  qpat_assum `!m1 v1 mid G1 tn1 t m2 v2 ee G2 tn2 u. _ ==> gas_outcome_full_mods _ _ _ _ (suffix _ _) _ _ _`
    irule >> simp[] >> qexistsl_tac [`G1`,`m1`,`m2`,`mid`,`t`,`tn1`] >> simp[]
QED

(* Recover the clean source state for the next operand and transfer the
   constant cells and the storage horizon along the very same evaluation. *)
Theorem bop_bytestring_operand_source_mods:
  expr_body_pre_mods mods cenv cx env e es /\
  body_const_cells_agree_mods mods cx env es /\ ee.gas_obs = [] /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs ++ tail) =
           (INL v,ee with gas_obs := tail)) ==>
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) = (INL v,ee) /\
  expr_sim_inv_mods mods cenv cx env ee /\
  body_const_cells_agree_mods mods cx env ee /\
  value_runtime_typed env (expr_type e) v /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace)
Proof
  strip_tac >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qpat_x_assum `!tail. bind _ _ _ = _`
    (qspec_then `[]` (assume_tac o PURE_REWRITE_RULE [listTheory.APPEND_NIL])) >>
  qpat_assum `ee with gas_obs := [] = ee` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := obs) /\
   body_const_cells_agree_mods mods cx env (es with gas_obs := obs)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >> simp[] >>
  rpt strip_tac >>
  qpat_assum `bind _ _ _ = _` (mp_then Any mp_tac valid_horizon_frame) >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result]
QED
