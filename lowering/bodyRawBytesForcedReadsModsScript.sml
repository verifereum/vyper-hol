(* Reached two-read composition for a linked raw-call request.  The
   continuation is deliberately abstract: the caller supplies the linked
   address/Bytes posts and the eventual keyword/finish rule. *)
Theory bodyRawBytesForcedReadsMods
Ancestors
  bodyBopBytestringBindMods bodyReachedWordResultBindMods
  bodyFullPredsMods bodyFullPostsMods bodyForcedStorageFrameMods
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
Libs monadsyntax

val operand1 = ``bind (eval_expr cx e1) (read_result cx)``;
val operand2 = ``bind (eval_expr cx e2) (read_result cx)``;

Theorem raw_bytes_reached_value_bind[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (source : evaluation_state -> value evaluation_result) (es,s,G,tn)
    (\H res ee G' tn' t. ?v. res = INL v /\ P H v ee G' tn' t)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
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
      qpat_assum `gas_outcome_full_mods _ _ _ _ source _ _ _` (irule_at Any) >> simp[])
  >- (qx_genl_tac [`marks`,`res`,`ee`,`G'`,`tn'`,`t`] >> BETA_TAC >> strip_tac >>
      `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
        fs[storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >> gvs[] >>
      first_x_assum irule >> simp[] >> qexists_tac `marks` >> simp[])
QED

Theorem raw_bytes_forced_reads_mods:
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
  strip_tac >> irule raw_bytes_reached_value_bind >> BETA_TAC >> rpt conj_tac
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
          storage_trace_frame_read_result]
  >~ [`storage_trace_frame (bind (bind _ _) _)`]
  >- simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
          storage_trace_frame_read_result] >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  qx_genl_tac [`m1`,`v1`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  irule raw_bytes_reached_value_bind >> rpt conj_tac
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
          storage_trace_frame_read_result]
  >~ [`storage_trace_frame (suffix _ _)`] >- simp[] >>
  qpat_assum `!m1 v1 mid G1 tn1 t. _ ==> _` (irule_at Any) >>
  qexistsl_tac [`v1`,`m1`] >> simp[] >>
  qx_genl_tac [`m2`,`v2`,`ee`,`G2`,`tn2`,`u`] >> strip_tac >>
  first_assum (irule_at Any) >> simp[] >>
  qexistsl_tac [`G1`,`m1`,`m2`,`mid`,`t`,`tn1`] >> simp[]
QED
