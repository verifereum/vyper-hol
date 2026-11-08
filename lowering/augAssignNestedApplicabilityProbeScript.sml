(* Remaining frozen-premise and fragment-entry audit. *)
Theory augAssignNestedApplicabilityProbe
Ancestors
  augAssignNestedObservationProbe targetPlaceSimCases exprSimHypsDefs
  gasContext exprLoweringProps loweringPosts stmtSimDefs
Libs finite_mapLib computeLib

val () = computeLib.upd_compset add_finite_map_compset

Theorem nested_applicability_syntax:
  (!id. target_root nested_reach_target <> NameTarget id) /\
  ~supported_target_pure nested_reach_tops nested_reach_target /\
  (?b k. nested_reach_target = SubscriptTarget b k) /\
  supported_stmt nested_reach_tops []
    (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
      (Literal (BaseT (UintT 256)) (IntL 1))) /\
  ~immutable_root nested_initial_cx nested_reach_target
Proof
  EVAL_TAC >> simp[vyperStateTheory.find_var_decl_by_name_def]
QED

Theorem nested_applicability_admissible:
  gas_admissible
    (eval_stmt nested_initial_cx
      (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1))))
    (stmt_res_ok NoLoop) nested_premise_es
Proof
  rewrite_tac[gas_admissible_def] >> rpt strip_tac >>
  qspec_then `gs` mp_tac nested_initial_source_replay >>
  gvs[stmt_res_ok_def]
QED

Theorem nested_applicability_call_safe:
  call_evaluation_safe nested_initial_cx [(NONE,"f")]
Proof
  rewrite_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def] >>
  qexistsl [`[((NONE,""),(NONE,"f"))]`, `(NONE,"")`, `[]`] >>
  EVAL_TAC >> simp[] >> conj_tac
  >- (qmatch_goalsub_abbrev_tac `TC R` >>
      `transitive R` by
        (simp[Abbr `R`, relationTheory.transitive_def,
          vyperTypeCallGraphSoundnessTheory.call_edge_rel_def]) >>
      drule relationTheory.transitive_TC_identity >>
      disch_then SUBST1_TAC >>
      simp[Abbr `R`, relationTheory.irreflexive_def,
        vyperTypeCallGraphSoundnessTheory.call_edge_rel_def]) >>
  simp[vyperInterpreterTheory.lookup_function_def] >>
  rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem nested_applicability_indices:
  target_indices_pre nested_premise_cenv nested_initial_cx
    nested_premise_env nested_reach_target
Proof
  rewrite_tac[augAssignNestedReachProbeTheory.nested_reach_target_def,
    targetPlaceSimTheory.target_indices_pre_def, expr_body_pre_def] >>
  `get_tenv nested_initial_cx = type_env (cx_tops nested_initial_cx)` by EVAL_TAC >>
  simp[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``call_evaluation_safe``, ``expr_sim_inv``, ``nested_premise_cenv``, ``nested_premise_env``, ``nested_initial_cx``]) >>
  `call_evaluation_safe nested_initial_cx []` by
    (irule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_mono >>
     qexists `[(NONE,"f")]` >> simp[nested_applicability_call_safe]) >>
  simp[nested_applicability_call_safe] >>
  gen_tac >> disch_then kall_tac >> conj_tac
  >- (EVAL_TAC >> simp[]) >>
  qexists `nested_reach_tops` >> EVAL_TAC >>
  simp[vyperStateTheory.find_var_decl_by_name_def]
QED

Theorem nested_applicability_entry_code:
  fn_has_code (initial_compile_state "entry") nested_observation_state
    nested_observation_function /\
  fn_inst_ids_distinct nested_observation_function /\
  local_ptrs_reserved nested_premise_cenv (initial_compile_state "entry") /\
  ret_pc_ok nested_premise_cenv (initial_compile_state "entry")
    nested_observation_start /\
  ~block_is_terminated (initial_compile_state "entry") /\
  ~nested_observation_start.vs_halted /\
  nested_observation_start.vs_current_bb =
    (initial_compile_state "entry").cs_current_bb /\
  nested_observation_start.vs_inst_idx =
    LENGTH (initial_compile_state "entry").cs_current_insts
Proof
  conj_tac
  >- (`nested_observation_state.cs_blocks = []` by EVAL_TAC >>
      simp[fragExecTheory.fn_has_code_def, nested_observation_function_def,
        venomInstTheory.mk_raw_function_def, fragExecTheory.emitted_blocks_def] >>
      qexists `<|bb_label := nested_observation_state.cs_current_bb;
        bb_instructions := nested_observation_state.cs_current_insts ++
          [<|inst_id := nested_observation_state.cs_next_id;
             inst_opcode := STOP; inst_operands := []; inst_outputs := []|>]|>` >>
      simp[venomInstTheory.lookup_block_def, listTheory.FIND_thm,
        GSYM listTheory.SNOC_APPEND]) >>
  EVAL_TAC >> simp[]
QED

Theorem nested_applicability_entry_excluded:
  ~stmt_state_rel nested_premise_unit.cu_context nested_observation_function
    nested_premise_cenv nested_initial_cx nested_premise_es nested_observation_start
Proof
  simp[stmt_state_rel_def, compileEnvTheory.state_rel_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``nested_premise_unit``]) >> simp[]
QED

Theorem nested_applicability_call_context_excluded:
  ~call_ctx_rel nested_initial_cx.txn nested_observation_start.vs_call_ctx
    nested_observation_start.vs_tx_ctx nested_observation_start.vs_block_ctx
Proof
  EVAL_TAC
QED
