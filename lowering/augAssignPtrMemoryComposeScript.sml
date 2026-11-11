Theory augAssignPtrMemoryCompose
Ancestors
  gasSummaryComposePtr gasSummaryCompose gasExemptCert gasOutcome
  fragGasPathPtr fragExec stmtSimAugAssignPlaceMemory
  vyperInterpreter vyperState vyperAST exprSimLen exprSimDefs loweringPosts

Theorem aug_place_memory_reads_outcome_ptr:
  read_place cx (MemoryPlace id path) st = (INL cur,st) /\
  place_type_value cx (MemoryPlace id path) st = (INL ptv,st) /\
  gas_outcome_ptr D tops (ctx,fn) PG (k cur ptv) (st,s,G,tn) Q R ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (bind (read_place cx (MemoryPlace id path))
      (\v. bind (place_type_value cx (MemoryPlace id path)) (k v)))
    (st,s,G,tn) Q R
Proof
  strip_tac >>
  `!gs. read_place cx (MemoryPlace id path) (st with gas_obs := gs) =
    (INL cur,st with gas_obs := gs)` by simp[len_rp_obs] >>
  `!gs. place_type_value cx (MemoryPlace id path) (st with gas_obs := gs) =
    (INL ptv,st with gas_obs := gs)` by
    (Cases_on `lookup_scopes id st.scopes` >>
     gvs[place_type_value_def, get_scopes_def, bind_def, return_def,
         lift_option_type_def, raise_def] >>
     Cases_on `subscripts_type x.type path` >> gvs[return_def, raise_def]) >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_ptr_def]) >>
  rewrite_tac[gas_outcome_ptr_def]
  >- (qexists_tac `marks` >> disj1_tac >>
      fs[gas_summary_ptr_at_def, bind_def] >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule (aug_place_memory_reads_error_cert |> SPEC_ALL |> Q.INST
    [`k` |-> `\v pt. ignore_bind (h v pt) (return ())`] |>
    CONV_RULE (DEPTH_CONV BETA_CONV) |>
    REWRITE_RULE [ignore_bind_def, bind_assoc]) >>
  goal_assum (drule_at Any) >> fs[ignore_bind_def]
QED

Theorem aug_place_memory_outer_place_outcome_ptr:
  gas_marked_exec_ptr D (ctx,fn) PG (eval_base_place cx bt)
    (es,s0,G0,tn0) marks (INL (PlaceR (MemoryPlace id path))) raw G1 tn1 (OK t) /\
  gas_path_ptr D 0 ctx fn PG G1 tn1 t 0 G2 tn2 (OK u) /\
  read_place cx (MemoryPlace id path) (raw with gas_obs := []) =
    (INL cur,raw with gas_obs := []) /\
  place_type_value cx (MemoryPlace id path) (raw with gas_obs := []) =
    (INL ptv,raw with gas_obs := []) /\
  gas_outcome_ptr D tops (ctx,fn) PG (k (MemoryPlace id path) cur ptv)
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
      irule aug_place_memory_reads_outcome_ptr >> simp[]) >>
  rpt strip_tac >> irule gas_exempt_cert_bind_result >>
  goal_assum (drule_at Any) >> simp[get_place_def, bind_return]
QED
