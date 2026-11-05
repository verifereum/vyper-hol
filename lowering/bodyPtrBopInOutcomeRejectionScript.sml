Theory bodyPtrBopInOutcomeRejection
Ancestors
  bodyPtrBopInMachineConditions bodyPtrBopInMachineFrame
  bodyPtrBopInActualSuffix bodyPtrBopInUnit fragGasPathPtr
  ptrSafeRun ptrDiscipline venomExecSemantics venomInst venomState
  bodyPtrBopInUnitBody bodyPtrBopInUnitPackaging finite_map list
  bodyPtrBopInJointSource bodyPtrBopInSourceFrame bodyPtrBopInLocalSuffix
  gasExemptCert gasSummary gasCount fragExec vyperInterpreter vyperState vyperContext

Theorem joint_first_instruction:
  lookup_block joint_machine.vs_current_bb
    (equality_runtime_function equality_selector).fn_blocks = SOME bb /\
  get_instruction bb joint_machine.vs_inst_idx = SOME inst ==>
  inst = LAST (actual_suffix_end equality_selector).cs_current_insts
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem joint_no_pointer_edge:
  ~gas_path_ptr_edge D lo (equality_runtime_context equality_selector)
    (equality_runtime_function equality_selector) PG joint_provenance tn
    joint_machine n G' tn' r
Proof
  strip_tac >> fs[gas_path_ptr_edge_def] >>
  `inst = LAST (actual_suffix_end equality_selector).cs_current_insts` by
    metis_tac[joint_first_instruction] >> gvs[] >>
  `~access_ok lo joint_provenance (equality_runtime_function equality_selector)
     (LAST (actual_suffix_end equality_selector).cs_current_insts) joint_machine` by
    (irule actual_suffix_access_rejected >>
     simp[joint_provenance_def, FLOOKUP_UPDATE]) >>
  gvs[Once ptr_safe_defs, ptr_inst_ok_def]
QED

Theorem joint_pointer_path_reflexive:
  gas_path_ptr D lo (equality_runtime_context equality_selector)
    (equality_runtime_function equality_selector) PG joint_provenance tn
    joint_machine n G' tn' r ==>
  n = 0 /\ G' = joint_provenance /\ tn' = tn /\ r = OK joint_machine
Proof
  once_rewrite_tac[gas_path_ptr_cases] >>
  simp[joint_no_pointer_edge] >> rpt strip_tac >> simp[]
QED

Theorem joint_membership_all_observations:
  eval_expr joint_cx local_membership_fixture (joint_es with gas_obs := gs) =
    (INL (Value (BoolV T)),joint_es with gas_obs := gs)
Proof
  simp[local_membership_fixture_def, vyperInterpreterTheory.evaluate_def,
       bind_def, return_def, ignore_bind_def, read_result_def,
       type_check_def, assert_def, get_scopes_def, get_accounts_def,
       builtin_args_length_ok_def, vyperValueTheory.compatible_bound_def,
       vyperASTTheory.expr_type_def, joint_es_def, probe_es_def,
       probe_make_array_builtin, probe_in_builtin, lookup_scopes_def,
       read_place_def, read_memory_path_def, lift_option_type_def, lift_sum_def,
       evaluate_subscripts_def, FLOOKUP_UPDATE]
QED

Theorem joint_membership_no_exempt:
  ~gas_exempt_cert F tops (ctx,func)
    (ignore_bind (eval_expr joint_cx local_membership_fixture) (return ()))
    (joint_es,s) marks (err,ee) (leaf,final_state)
Proof
  strip_tac >> drule gas_exempt_cert_execution >>
  simp[ignore_bind_def, bind_def, joint_membership_all_observations, return_def]
QED

Theorem joint_suffix_index_differs:
  joint_machine.vs_inst_idx <>
    LENGTH (actual_suffix_end equality_selector).cs_current_insts
Proof
  EVAL_TAC
QED

Theorem joint_membership_outcome_rejected:
  (!res ee G tn t. Q res ee G tn t ==>
    t.vs_inst_idx = LENGTH (actual_suffix_end equality_selector).cs_current_insts) ==>
  ~gas_outcome_ptr D tops
    (equality_runtime_context equality_selector,equality_runtime_function equality_selector)
    PG (eval_expr joint_cx local_membership_fixture)
    (joint_es,joint_machine,joint_provenance,tn0) Q R
Proof
  strip_tac >> strip_tac >>
  fs[gas_outcome_ptr_def, joint_membership_no_exempt,
     gas_summary_ptr_at_def] >>
  drule joint_pointer_path_reflexive >> strip_tac >> gvs[exit_result_def] >>
  metis_tac[joint_suffix_index_differs]
QED
