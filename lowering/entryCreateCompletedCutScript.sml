(* Compare an operand's scoped full witness against the first exit on the
   selected caller path. Ghosts are not part of the path comparison. *)
Theory entryCreateCompletedCut
Ancestors
  createExprSizeExitDefs createSizePrefixReplay createMarkedPath
  gasOutcomeFull gasStorage gasExemptCert gasEventsFuel gasSummary
  analysisSimProofsBase venomExecProofs venomExecSemantics venomInst venomState
  fragExec fragGasOrigin fragGasOriginPtr vyperStorageFootprint vyperInterpreter
  vyperState relation list rich_list pair option

Theorem origin_edge_unique[local]:
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  gas_origin_edge m explicit ctx func u xs r /\
  gas_origin_edge n explicit ctx func u ys r' ==>
  xs = ys /\ r = r'
Proof
  pure_rewrite_tac[gas_origin_edge_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 assume_tac
        (qx_choosel_then [`fuel`,`bb`,`inst`,`middle`]
          (map_every assume_tac o CONJUNCTS)))
      (CONJUNCTS_THEN2 assume_tac
        (qx_choosel_then [`fuel'`,`bb'`,`inst'`,`middle'`]
          (map_every assume_tac o CONJUNCTS))))) >>
  `!err. step_inst fuel ctx inst u <> Error err` by
    (rpt strip_tac >> gvs[exit_result_def]) >>
  `bb' = bb` by metis_tac[SOME_11] >>
  `inst' = inst` by metis_tac[SOME_11] >>
  qpat_x_assum `inst' = inst` SUBST_ALL_TAC >>
  `!err. step_inst fuel' ctx inst u <> Error err` by
    (rpt strip_tac >> gvs[exit_result_def]) >>
  `step_inst fuel ctx inst u = step_inst fuel' ctx inst u /\
   gas_events_step fuel ctx func.fn_name inst u =
     gas_events_step fuel' ctx func.fn_name inst u` by
    (Cases_on `fuel <= fuel'` >>
     metis_tac[cj 1 gas_events_fuel_extension, arithmeticTheory.LESS_EQ_CASES]) >>
  `!lbl dest. lookup_block lbl func.fn_blocks = SOME dest ==>
      phi_prefix_length dest.bb_instructions = 0` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  gs[exit_result_def] >>
  fs[jump_to_def] >>
  rename1 `eval_phis _ dest.bb_instructions = OK entered` >>
  `phi_prefix_length dest.bb_instructions = 0` by metis_tac[] >>
  gvs[phi_prefix_length_zero_eval_phis_ok]
QED

Theorem deterministic_rtc_to_sink[local]:
  !x y. RTC R x y ==>
    (!a b c. R a b /\ R a c ==> b = c) ==>
    !z. RTC R x z /\ (!v. ~R z v) ==> RTC R y z
Proof
  ho_match_mp_tac RTC_INDUCT >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> disch_tac >> gen_tac >> strip_tac >>
  qpat_x_assum `RTC R _ _` (strip_assume_tac o ONCE_REWRITE_RULE[RTC_CASES1]) >>
  metis_tac[]
QED

Theorem create_prefix_to_exit[local]:
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_expr_prefix sa sb explicit ctx func s0 left u /\
  create_expr_prefix sa sb explicit ctx func s0 marks s /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?right. marks = left ++ right /\ create_expr_prefix sa sb explicit ctx func u right s
Proof
  simp[create_expr_prefix_marked] >> strip_tac >>
  qpat_assum `RTC _ (s0,[]) (u,left)` (mp_tac o MATCH_MP deterministic_rtc_to_sink) >>
  (impl_tac >-
    (simp[FORALL_PROD, create_marked_edge_def, create_prefix_step_def] >>
     metis_tac[origin_edge_unique, venomExecSemanticsTheory.exec_result_11])) >>
  disch_then (qspec_then `(s,marks)` mp_tac) >>
  simp[FORALL_PROD, create_marked_edge_def, create_prefix_step_def] >>
  disch_then (qspec_then `[]` mp_tac o MATCH_MP create_marked_rtc_rebase) >> simp[]
QED

Theorem create_prefix_uncons[local]:
  create_expr_prefix sa sb explicit ctx func u right s ==>
  (u = s /\ right = []) \/
  ?v head rest. create_prefix_step sa sb explicit ctx func u head v /\
                right = head ++ rest
Proof
  rewrite_tac[create_expr_prefix_marked] >> once_rewrite_tac[RTC_CASES1] >>
  simp[EXISTS_PROD, create_marked_edge_def] >> strip_tac >- simp[] >>
  drule create_marked_rtc_rebase >> disch_then (qspec_then `[]` strip_assume_tac) >>
  metis_tac[FST,SND]
QED

(* Recover memory validity only on the last edge of the selected path. *)
Theorem create_prefix_selected_terminal_edge:
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_expr_prefix a b E ctx f s [] u /\
  gas_origin_edge F E ctx f u [] r /\ exit_result r /\
  gas_origin_path T E ctx f s [] r ==>
  gas_origin_edge T E ctx f u [] r
Proof
  simp[create_expr_prefix_marked] >> strip_tac >>
  `!v. gas_origin_path T E ctx f v [] r ==>
        gas_origin_edge T E ctx f v [] r \/
        ?w. gas_origin_edge T E ctx f v [] (OK w) /\
            gas_origin_path T E ctx f w [] r` by
    (gen_tac >> disch_then (mp_tac o ONCE_REWRITE_RULE[gas_origin_path_cases]) >>
     simp[] >> strip_tac >> gvs[exit_result_def] >> metis_tac[]) >>
  `!x y. RTC (create_marked_edge (create_prefix_step a b E ctx f)) x y ==>
         SND y = [] ==> gas_origin_path T E ctx f (FST x) [] r ==>
                        gas_origin_path T E ctx f (FST y) [] r` by
    (ho_match_mp_tac RTC_INDUCT_RIGHT1 >> simp[] >>
     simp[FORALL_PROD,create_marked_edge_def,create_prefix_step_def] >>
     rpt strip_tac >> gvs[] >>
     metis_tac[origin_edge_unique,exit_result_def,exec_result_11]) >>
  `gas_origin_path T E ctx f u [] r` by metis_tac[FST,SND] >>
  metis_tac[origin_edge_unique,exit_result_def]
QED

(* A focus can stop at a caller cursor, or inside its pending INVOKE.
   In the latter case its remaining events are an initial part of the marks
   of the returned caller edge, if that edge completes. *)
Definition create_operand_focus_scope_def:
  create_operand_focus_scope sa sb explicit ctx func s0 marks <=>
    ?left u pending.
      create_expr_prefix sa sb explicit ctx func s0 left u /\
      marks = left ++ pending /\
      (pending = [] \/
       ((u.vs_current_bb <> sb.cs_current_bb \/
         u.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
        (!right v. create_prefix_step sa sb explicit ctx func u right v ==>
                   isPREFIX pending right)))
End

Theorem create_operand_focus_marks_prefix[local]:
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_operand_focus_scope sa sb explicit ctx func s0 focus /\
  create_expr_prefix sa sb explicit ctx func s0 marks s /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  isPREFIX focus marks
Proof
  simp[create_operand_focus_scope_def] >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  `?right. marks = left ++ right /\ create_expr_prefix sa sb explicit ctx func u right s`
    by metis_tac[create_prefix_to_exit] >>
  gvs[] >>
  qpat_x_assum `create_expr_prefix _ _ _ _ _ u _ s`
    (strip_assume_tac o MATCH_MP create_prefix_uncons) >>
  gvs[] >> fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]
QED

(* The three full-outcome branches have different scope obligations. In
   particular a terminal target witness must stop before the operand exit,
   rather than run through the exit into the enclosing continuation. *)
Definition create_operand_full_scope_def:
  create_operand_full_scope sa sb explicit ctx func s0 marks r <=>
    case r of
      OK u => create_expr_prefix sa sb explicit ctx func s0 marks u /\
              u.vs_current_bb = sb.cs_current_bb /\
              u.vs_inst_idx = LENGTH sb.cs_current_insts
    | _ => ?left u last.
        create_expr_prefix sa sb explicit ctx func s0 left u /\
        marks = left ++ last /\
        (u.vs_current_bb <> sb.cs_current_bb \/
         u.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
        gas_origin_edge T explicit ctx func u last r
End

Theorem create_operand_full_scope_match[local]:
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_operand_full_scope sa sb explicit ctx func s0 witness r /\
  create_expr_prefix sa sb explicit ctx func s0 marks s /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  r = OK s /\ witness = marks
Proof
  Cases_on `r` >> pure_rewrite_tac[create_operand_full_scope_def,exec_result_case_def] >> BETA_TAC >>
  disch_then (map_every strip_assume_tac o CONJUNCTS)
  >- (rename1 `create_expr_prefix _ _ _ _ _ s0 witness u` >>
      rename1 `create_expr_prefix _ _ _ _ _ s0 marks s` >>
      `?right. marks = witness ++ right /\ create_expr_prefix sa sb explicit ctx func u right s`
        by metis_tac[create_prefix_to_exit] >>
      qpat_x_assum `create_expr_prefix _ _ _ _ _ u _ s`
        (strip_assume_tac o MATCH_MP create_prefix_uncons) >>
      gvs[create_prefix_step_def]) >>
  rename1 `gas_origin_edge T _ _ _ u last _` >>
  rename1 `create_expr_prefix _ _ _ _ _ s0 left u` >>
  `?right. marks = left ++ right /\ create_expr_prefix sa sb explicit ctx func u right s`
    by metis_tac[create_prefix_to_exit] >>
  qpat_x_assum `create_expr_prefix _ _ _ _ _ u _ s`
    (strip_assume_tac o MATCH_MP create_prefix_uncons) >>
  gvs[create_prefix_step_def] >>
  metis_tac[origin_edge_unique, venomExecSemanticsTheory.exec_result_distinct]
QED

Definition scoped_operand_outcome_def:
  scoped_operand_outcome (DF, lo, explicit, ctx, func, PG) tops cx st0
    sa sb source (es, s, G, tn) Q R <=>
    ?marks.
      (gas_bad_storage_at cx st0 source es s marks /\
       create_operand_focus_scope sa sb explicit ctx func s marks /\
       ?H leaf leaf_pg leaf_g leaf_tn finish.
         (storage_trace_domain cx st0 es.storage_trace ==>
          valid_horizon cx st0 H es.storage_trace) /\
         gas_origin_ptr_focus (DF H, lo, explicit, ctx, func, PG)
           (s, G, tn) marks (leaf, leaf_pg, leaf_g, leaf_tn, finish)) \/
      (?res ee r G' tn'.
        create_operand_full_scope sa sb explicit ctx func s marks r /\
        (!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
                 (res, ee with gas_obs := tail)) /\
        storage_trace_domain cx st0 ee.storage_trace /\
        !H. valid_horizon cx st0 H ee.storage_trace ==>
          gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
            (s, G, tn) marks (r, G', tn') /\
          ((?t. r = OK t /\ Q H res (ee with gas_obs := []) G' tn' t) \/
           (exit_result r /\ R H res (ee with gas_obs := []) (G', tn') r))) \/
      (?err ee leaf leaf_pg leaf_g leaf_tn finish.
        create_operand_focus_scope sa sb explicit ctx func s marks /\
        gas_exempt_cert T tops (ctx, func) (ignore_bind source (return ()))
          (es, s) marks (err, ee) (leaf, finish) /\
        ?H. (storage_trace_domain cx st0 es.storage_trace ==>
             valid_horizon cx st0 H es.storage_trace) /\
            gas_origin_ptr_focus (DF H, lo, explicit, ctx, func, PG)
              (s, G, tn) marks (leaf, leaf_pg, leaf_g, leaf_tn, finish))
End

Theorem scoped_operand_outcome_full:
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0 sa sb
    source (es,s,G,tn) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source (es,s,G,tn) Q R
Proof
  rw[scoped_operand_outcome_def,gas_outcome_full_def] >> qexists_tac `marks` >>
  metis_tac[]
QED

Theorem valid_horizon_intrinsic[local]:
  valid_horizon cx st0 H obs ==> storage_trace_domain cx st0 obs
Proof
  simp[storage_trace_domain_def, valid_horizon_def, storage_trace_horizon_def,
       storage_observations_ok_def, EVERY_MEM] >> strip_tac >>
  rpt conj_tac
  >- (fs[regions_consistent_def] >> metis_tac[])
  >- (fs[storage_locks_separated_def] >> metis_tac[])
  >- (fs[storage_well_formed_on_def] >> metis_tac[]) >>
  fs[storage_trace_backends_well_formed_def, EVERY_MEM] >> rpt strip_tac >>
  Cases_on `observation` >> gvs[] >>
  rename1 `MEM (StorageBackend accounts transient) obs` >>
  qpat_x_assum `!observation. MEM observation obs ==> _`
    (qspec_then `StorageBackend accounts transient` mp_tac) >>
  simp[storage_well_formed_on_def] >> metis_tac[]
QED

Theorem scoped_focus_source_input[local]:
  isPREFIX left marks ==>
  ?suffix. gas_explicit marks readings ++ tail =
           gas_explicit left readings ++ suffix
Proof
  simp[IS_PREFIX_APPEND] >> strip_tac >> simp[gas_explicit_append, APPEND_ASSOC]
QED

Theorem scoped_outcome_completed_operand:
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0 sa sb
    source (es,s0,G0,tn0) Q R ==>
  gas_completed_operand (DF,lo,explicit,ctx,func,PG) tops cx st0 sa sb
    source (es,s0,G0,tn0) Q
Proof
  simp[scoped_operand_outcome_def,gas_completed_operand_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `witness` assume_tac)) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `_ \/ _` (DISJ_CASES_THEN2 strip_assume_tac
    (DISJ_CASES_THEN strip_assume_tac))
  >- (drule_all create_operand_focus_marks_prefix >> strip_tac >>
      `?suffix. gas_explicit marks s0.vs_gas_readings ++ tail =
               gas_explicit witness s0.vs_gas_readings ++ suffix`
        by metis_tac[scoped_focus_source_input] >>
      qpat_x_assum `gas_bad_storage_at _ _ _ _ _ _`
        (qspec_then `suffix` mp_tac o REWRITE_RULE[gas_bad_storage_at_def]) >>
      pop_assum (fn th => simp[GSYM th]) >>
      metis_tac[valid_horizon_intrinsic])
  >- (drule_all create_operand_full_scope_match >> strip_tac >> gvs[] >>
      qpat_assum `!tail. source _ = _` (qspec_then `tail` assume_tac) >>
      gvs[] >> disj1_tac >> qexistsl_tac [`G'`,`tn'`] >>
      fs[exit_result_def])
  >> drule_all create_operand_focus_marks_prefix >> strip_tac >>
  `?suffix. gas_explicit marks s0.vs_gas_readings ++ tail =
           gas_explicit witness s0.vs_gas_readings ++ suffix`
    by metis_tac[scoped_focus_source_input] >>
  drule gas_exempt_cert_execution >>
  disch_then (CONJUNCTS_THEN2 (qspec_then `suffix` mp_tac) strip_assume_tac) >>
  fs[ignore_bind_def,bind_def] >>
  Cases_on `res` >> simp[return_def] >> metis_tac[]
QED

(* Retain the source equation used to build the normal witness, not just
   its specialization to the tail in the completed-operand query. *)
Theorem scoped_completed_operand_landing:
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0 sa sb
    source (es,s0,G0,tn0) Q R ==>
  gas_completed_operand (DF,lo,explicit,ctx,func,PG) tops cx st0 sa sb
    source (es,s0,G0,tn0)
    (\H res ee G tn t. Q H res ee G tn t /\
      !left. create_expr_prefix sa sb explicit ctx func s0 left t /\
             t.vs_current_bb = sb.cs_current_bb /\
             t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
        (!tail. source (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ tail) =
                  (res, ee with gas_obs := tail)) /\
        storage_trace_domain cx st0 ee.storage_trace /\
        !H'. valid_horizon cx st0 H' ee.storage_trace ==>
          gas_origin_ptr_path (DF H',lo,explicit,ctx,func,PG)
            (s0,G0,tn0) left (OK t,G,tn) /\
          Q H' res ee G tn t)
Proof
  strip_tac >> irule scoped_outcome_completed_operand >> simp[] >>
  qexists_tac `R` >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[scoped_operand_outcome_def]) >>
  simp[scoped_operand_outcome_def] >>
  disch_then (qx_choose_then `marks` assume_tac) >>
  qexists_tac `marks` >>
  qpat_x_assum `_ \/ _` (DISJ_CASES_THEN2 assume_tac
    (DISJ_CASES_THEN2 strip_assume_tac assume_tac))
  >- simp[]
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (drule_then strip_assume_tac) >> gvs[exit_result_def] >>
      gen_tac >> strip_tac >>
      drule_all create_operand_full_scope_match >> strip_tac >>
      gvs[exit_result_def]) >>
  simp[]
QED
