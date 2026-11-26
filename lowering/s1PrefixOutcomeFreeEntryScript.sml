(* An entry that produces no source observations has no request-site queries. *)
Theory s1PrefixOutcomeFreeEntry
Ancestors
  s1PrefixDefs s1PrefixProps sourceUnitExecution gasOutcomeFull
  fragGasOriginPtr gasExplicitSites gasSummary venomInst venomState
  vyperCall vyperContext finite_map

Theorem outcome_free_entry_prefix_cert:
  ~vs.vs_halted /\
  source_unit_execution_correct_with shadow_ctx marks tops ret am tx unit vs /\
  (!tail res am' rqs obs. call_external_trace (SOME vs.vs_outcomes)
    (gas_explicit marks vs.vs_gas_readings ++ tail) am tx = (res,am',rqs,obs) ==>
    obs = []) /\
  (marks = [] \/
   ?fn (H : (bool # bytes32 # type_value) list # num list).
     venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
     ((?r G tn. gas_origin_ptr_path
        (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
         0,gas_explicit_sites unit.cu_context shadow_ctx,unit.cu_context,fn,[])
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
         FEMPTY,entry_taint) marks (r,G,tn)) \/
      (?leaf leaf_pg leaf_g leaf_tn finish. gas_origin_ptr_focus
        (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
         0,gas_explicit_sites unit.cu_context shadow_ctx,unit.cu_context,fn,[])
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
         FEMPTY,entry_taint) marks (leaf,leaf_pg,leaf_g,leaf_tn,finish)))) ==>
  unit_prefix_cert shadow_ctx tops am tx unit vs
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `source_unit_execution_correct_with _ _ _ _ _ _ _ _`
    (qx_choosel_then [`fn`,`shadow_fn`]
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac (K ALL_TAC))) o
     REWRITE_RULE [source_unit_execution_correct_with_def]) >>
  pure_rewrite_tac[unit_prefix_cert_def] >> qexistsl_tac [`fn`,`marks`] >>
  asm_rewrite_tac[] >> reverse conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_x_assum `!tail res am' rqs obs. call_external_trace _ _ _ _ = _ ==> _`
        drule >> simp[]) >>
  qpat_x_assum `marks = [] \/ _` strip_assume_tac
  >- (qexistsl_tac [`([],[])`,`fn`,`[]`,`FEMPTY`,`entry_taint`,
         `vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>`] >>
      simp[gas_origin_ptr_focus_nil]) >>
  gvs[] >> qexists_tac `H`
  >- (drule gas_origin_ptr_path_focus >> simp[]) >>
  goal_assum (drule_at Any)
QED
