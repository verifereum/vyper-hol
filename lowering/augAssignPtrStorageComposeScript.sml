Theory augAssignPtrStorageCompose
Ancestors
  augAssignPtrStorageCommon augAssignPtrMemoryCompose
  gasSummary gasSummaryComposePtr gasSummaryCompose gasExemptCert gasOutcome
  fragGasPathPtr fragGasMode fragExec stmtSimAugAssignPlaceMemory
  bodyPtrBytestringBuiltinsUnary vyperInterpreter vyperState vyperAST
  exprSimDefs loweringPosts

Theorem aug_place_storage_reads_outcome_ptr:
  st.gas_obs = [] /\ ~s.vs_halted /\
  read_place cx (StoragePlace tr slot tv) st = (INL cur,st) /\
  gas_outcome_ptr D tops (ctx,fn) PG (k cur tv) (st,s,G,tn) Q R ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (bind (read_place cx (StoragePlace tr slot tv))
      (\v. bind (place_type_value cx (StoragePlace tr slot tv)) (k v)))
    (st,s,G,tn) Q R
Proof
  strip_tac >>
  `st with gas_obs := [] = st` by (Cases_on `st` >> gvs[recordtype_evaluation_state_seldef_gas_obs_fupd_def]) >>
  `!gs. read_place cx (StoragePlace tr slot tv) (st with gas_obs := gs) =
    (INL cur,st with gas_obs := gs)` by
    (fs[read_place_def] >> metis_tac[read_storage_slot_gas_obs_ptr]) >>
  simp[place_type_value_def, bind_return] >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_ptr_def]) >>
  rewrite_tac[gas_outcome_ptr_def]
  >- (qexists_tac `marks` >> disj1_tac >>
      fs[gas_summary_ptr_at_def, bind_def] >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  `gas_marked_exec F (ctx,fn) (read_place cx (StoragePlace tr slot tv))
     (st,s) [] (INL cur) st (OK s)` by
    simp[gas_marked_exec_def, gas_explicit_def, gas_marked_path_def,
         fragGasPathTheory.gas_path_rules] >>
  drule gas_exempt_cert_bind_value >>
  disch_then (qspec_then `tops`
    (qspec_then `\v. ignore_bind (k v tv) (return ())` mp_tac)) >>
  fs[ignore_bind_def] >> metis_tac[]
QED

Theorem aug_place_storage_outer_place_outcome_ptr:
  gas_marked_exec_ptr D (ctx,fn) PG (eval_base_place cx bt)
    (es,s0,G0,tn0) marks (INL (PlaceR (StoragePlace tr slot tv))) raw G1 tn1 (OK t) /\
  gas_path_ptr D 0 ctx fn PG G1 tn1 t 0 G2 tn2 (OK u) /\
  read_place cx (StoragePlace tr slot tv) (raw with gas_obs := []) =
    (INL cur,raw with gas_obs := []) /\
  gas_outcome_ptr D tops (ctx,fn) PG (k (StoragePlace tr slot tv) cur tv)
    (raw with gas_obs := [],u,G2,tn2) Q R ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (bind (eval_target_place cx bt) (\p.
      bind (read_place cx p) (\v. bind (place_type_value cx p) (k p v))))
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >> rewrite_tac[aug_place_target_bind_base] >>
  irule gas_outcome_ptr_bind_normal >> goal_assum (drule_at Any) >>
  simp[get_place_def, bind_return] >> reverse conj_tac
  >- (irule gas_outcome_ptr_prefix >> goal_assum (drule_at Any) >>
      irule aug_place_storage_reads_outcome_ptr >> simp[] >>
      metis_tac[fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted]) >>
  rpt strip_tac >> irule gas_exempt_cert_bind_result >>
  goal_assum (drule_at Any) >> simp[get_place_def, bind_return]
QED

Theorem augassign_storage_rhs_outcome_ptr:
  gas_marked_exec_ptr D (ctx,fn) PG (eval_base_place cx bt)
    (es,s0,G0,tn0) marks (INL (PlaceR (StoragePlace tr slot tv))) raw G1 tn1 (OK t) /\
  gas_path_ptr D 0 ctx fn PG G1 tn1 t 0 G2 tn2 (OK u) /\
  read_place cx (StoragePlace tr slot tv) (raw with gas_obs := []) =
    (INL cur,raw with gas_obs := []) /\
  gas_outcome_ptr D tops (ctx,fn) PG
    (bind (eval_expr cx e) (read_result cx))
    (raw with gas_obs := [],u,G2,tn2) P E /\
  (!res ee G tn s. P res ee G tn s ==>
    ?rhs. res = INL rhs /\
      gas_outcome_ptr D tops (ctx,fn) PG
        (bind (lift_sum (evaluate_binop
          (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
          tv bop cur rhs)) (write_place cx (StoragePlace tr slot tv)))
        (ee,s,G,tn) Q R) /\
  (!res ee gt r. E res ee gt r ==>
    ?exc. res = INR exc /\ R (INR exc) ee gt r) ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (eval_stmt cx (AugAssign ty bt bop e)) (es,s0,G0,tn0) Q R
Proof
  strip_tac >> simp[Once evaluate_def] >>
  ho_match_mp_tac (GEN_ALL aug_place_storage_outer_place_outcome_ptr) >>
  goal_assum (drule_at (Pat `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `read_place _ _ _ = _`)) >>
  rewrite_tac[GSYM bind_assoc] >>
  irule gas_outcome_ptr_value_bind >>
  goal_assum (drule_at Any) >> qexists_tac `P` >> simp[] >> metis_tac[]
QED
