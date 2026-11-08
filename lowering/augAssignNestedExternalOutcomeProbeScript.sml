(* Outcome audit at the certified common External entry, not the old synthetic function. *)
Theory augAssignNestedExternalOutcomeProbe
Ancestors
  augAssignNestedExternalArtifactProjection augAssignNestedExternalRelatedEntryProbe
  augAssignNestedExternalEntryProbe augAssignNestedExternalCallerProbe
  augAssignEffectfulContractProbe augAssignNestedExternalPremises
  augAssignNestedExternalSemanticAudit augAssignNestedExternalBodyInv
  augAssignNestedExternalArtifactAudit gasOutcome gasSummary gasExemptCert
  fragExec fragGasPath stmtSimDefs loweringPosts venomExecSemantics venomState
  vyperInterpreter vyperState
Libs finite_mapLib computeLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (wordsLib.add_words_compset true)
val () = computeLib.upd_compset (computeLib.add_thms [nested_external_functions])

Theorem nested_external_target_run:
  ?t. run_from 100 nested_external_unit.cu_context nested_external_entry_fn
      nested_external_runtime_entry = Abort Revert_abort t
Proof
  rewrite_tac[nested_external_entry_fn_def, nested_external_functions] >>
  CONV_TAC (RESTR_EVAL_CONV [``nested_external_unit``, ``exec_block``, ``run_blocks``]) >>
  simp[nested_external_functions] >>
  CONV_TAC (RESTR_EVAL_CONV [``nested_external_unit``, ``run_blocks``]) >>
  simp[nested_external_functions] >>
  CONV_TAC (RESTR_EVAL_CONV [``nested_external_unit``, ``run_blocks``]) >>
  simp[nested_external_functions] >>
  CONV_TAC (RESTR_EVAL_CONV [``nested_external_unit``]) >> simp[]
QED

Theorem nested_external_endpoint_halts:
  !t. t.vs_current_bb = nested_external_slice_end.cs_current_bb /\
      t.vs_inst_idx = LENGTH nested_external_slice_end.cs_current_insts ==>
    run_from 0 nested_external_unit.cu_context nested_external_entry_fn t =
      Halt (halt_state (t with vs_returndata := []))
Proof
  gen_tac >>
  rewrite_tac[nested_external_slice_end_def, nested_external_slice_cenv_def,
    nested_external_compile_env] >>
  CONV_TAC (LAND_CONV (RESTR_EVAL_CONV [``function_selector``, ``calldata_method_id``])) >>
  strip_tac >>
  simp[run_from_def, nested_external_entry_fn_def, nested_external_functions] >>
  CONV_TAC (RESTR_EVAL_CONV [``exec_block``, ``run_blocks``, ``halt_state``, ``nested_external_unit``]) >>
  simp[Once exec_block_def, venomInstTheory.get_instruction_def, step_inst_non_invoke] >>
  simp[Once step_inst_base_def, venomInstTheory.is_terminator_def]
QED

Theorem nested_external_no_endpoint_path:
  !n t. ~(gas_path nested_external_unit.cu_context nested_external_entry_fn
    nested_external_runtime_entry n (OK t) /\
    t.vs_current_bb = nested_external_slice_end.cs_current_bb /\
    t.vs_inst_idx = LENGTH nested_external_slice_end.cs_current_insts)
Proof
  rpt strip_tac >>
  drule gas_path_normal >> strip_tac >>
  drule_all nested_external_endpoint_halts >> strip_tac >>
  first_x_assum (qspecl_then [`0`, `Halt (halt_state (t with vs_returndata := []))`] mp_tac) >>
  simp[] >> strip_tac >> spose_not_then assume_tac >>
  rename1 `run_from m _ _ nested_external_runtime_entry = Halt _` >>
  mp_tac nested_external_target_run >> strip_tac >>
  `run_from (m + 100) nested_external_unit.cu_context nested_external_entry_fn
      nested_external_runtime_entry = Halt (halt_state (t with vs_returndata := []))` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `m` >> simp[]) >>
  `run_from (m + 100) nested_external_unit.cu_context nested_external_entry_fn
      nested_external_runtime_entry = Abort Revert_abort t'` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `100` >> simp[]) >>
  metis_tac[exec_result_distinct]
QED

Theorem nested_external_no_summary:
  ~gas_summary (nested_external_unit.cu_context, nested_external_entry_fn)
    (eval_stmt nested_external_cx
      (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1))))
    (nested_premise_es, nested_external_runtime_entry)
    (stmt_post nested_external_unit.cu_context nested_external_entry_fn
      nested_external_cx lctx nested_external_slice_cenv cenv' sa
      nested_external_slice_end nested_external_runtime_entry)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  pure_rewrite_tac[gas_summary_def] >>
  rpt strip_tac >>
  `res = INL ()` by
    (qpat_x_assum `!tail. _ = _` (qspec_then `[]` mp_tac) >>
     disch_then (mp_tac o AP_TERM ``FST : (unit + exception) # evaluation_state -> unit + exception``) >>
     simp[nested_external_source_replay]) >>
  gvs[stmt_post_def, loweringPostsTheory.stmt_lands_def,
      stmt_exit_loop_ctl] >>
  metis_tac[nested_external_no_endpoint_path]
QED

Theorem nested_external_no_outcome:
  ~gas_outcome memory tops
    (nested_external_unit.cu_context, nested_external_entry_fn)
    (eval_stmt nested_external_cx
      (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1))))
    (nested_premise_es, nested_external_runtime_entry)
    (stmt_post nested_external_unit.cu_context nested_external_entry_fn
      nested_external_cx lctx nested_external_slice_cenv cenv' sa
      nested_external_slice_end nested_external_runtime_entry)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  rpt strip_tac
  >- metis_tac[gas_summary_at_summary, nested_external_no_summary] >>
  qpat_x_assum `gas_exempt_cert _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[GSYM IMP_F] >>
  irule source_replay_excludes_gas_exempt_cert >>
  rpt gen_tac >>
  qspec_then `obs` mp_tac nested_external_source_replay >>
  Cases_on `eval_stmt nested_external_cx
      (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1)))
      (nested_premise_es with gas_obs := obs)` >>
  simp[ignore_bind_def, bind_def, return_def] >>
  strip_tac >> gvs[]
QED

Theorem nested_external_not_stmt_frag:
  !RetQ. ~stmt_frag nested_external_unit.cu_context nested_external_entry_fn
    nested_external_cx NoLoop RetQ nested_external_slice_cenv
    (stmt_env nested_external_slice_cenv NoLoop NoneT
      (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1))))
    (eval_stmt nested_external_cx
      (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1)))) nested_premise_es
Proof
  rw[stmt_frag_def, stmt_framed_frag_def] >>
  mp_tac nested_external_runtime_entry_domain >> strip_tac >>
  qexistsl [`nested_external_slice_start`, `nested_external_slice_end`,
    `nested_external_runtime_entry`, `cenv'`] >>
  simp[nested_external_no_outcome]
QED

(* All frozen antecedents hold on this one tuple, but its conclusion fails.
   The RHS simulation is unconditional, hence supplies the conditional premise. *)
Theorem nested_external_frozen_counterexample:
  (!id. target_root nested_reach_target <> NameTarget id) /\
  ~supported_target_pure nested_external_tops nested_reach_target /\
  ((?b fld. nested_reach_target = AttributeTarget b fld) \/
   (?b k. nested_reach_target = SubscriptTarget b k)) /\
  body_inv nested_external_tops nested_external_unit.cu_context
    nested_external_slice_cenv nested_external_cx /\
  supported_stmt nested_external_tops []
    (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
      (Literal (BaseT (UintT 256)) (IntL 1))) /\
  type_stmt nested_external_artifact_env NoneT
    (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
      (Literal (BaseT (UintT 256)) (IntL 1))) = SOME nested_external_artifact_env /\
  target_case F nested_external_unit.cu_context nested_external_entry_fn
    nested_external_slice_cenv nested_external_cx nested_reach_target /\
  ~immutable_root nested_external_cx nested_reach_target /\
  target_indices_pre nested_external_slice_cenv nested_external_cx
    nested_external_artifact_env nested_reach_target /\
  ((?s p s1 s2 cur s3 s4 ptv s5.
      eval_target_place nested_external_cx nested_reach_target s = (INL p,s1) /\
      read_place nested_external_cx p s2 = (INL cur,s3) /\
      place_type_value nested_external_cx p s4 = (INL ptv,s5)) ==>
    expr_sim_case F nested_external_unit.cu_context nested_external_entry_fn
      nested_external_slice_cenv nested_external_cx
      (Literal (BaseT (UintT 256)) (IntL 1))) /\
  expr_body_pre nested_external_slice_cenv nested_external_cx
    nested_external_artifact_env (Literal (BaseT (UintT 256)) (IntL 1))
    nested_premise_es /\
  (!RetQ. ~stmt_frag nested_external_unit.cu_context nested_external_entry_fn
    nested_external_cx NoLoop RetQ nested_external_slice_cenv
    (stmt_env nested_external_slice_cenv NoLoop NoneT
      (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1))))
    (eval_stmt nested_external_cx
      (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1)))) nested_premise_es)
Proof
  mp_tac nested_external_target_syntax >> strip_tac >>
  simp[nested_external_body_inv, nested_external_stmt_supported,
    nested_external_artifact_stmt_typed, nested_external_target_case,
    nested_external_indices, nested_external_rhs_case,
    nested_external_rhs_pre, nested_external_not_stmt_frag] >>
  metis_tac[nested_external_target_case, nested_external_body_inv]
QED
