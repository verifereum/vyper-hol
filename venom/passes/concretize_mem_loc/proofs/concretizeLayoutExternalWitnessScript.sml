Theory concretizeLayoutExternalWitness
Ancestors concretizeLayoutExternalOutcomeProbe o1PassContract
  unitTransformDefs lowerDloadDefs venomInst venomState
Libs wordsLib

val () = augment_srw_ss [wordsLib.SIZES_ss, wordsLib.WORD_GROUND_ss];

Definition external_witness_fn_def:
  external_witness_fn = mk_raw_function "entry"
    [<| bb_label := "entry";
        bb_instructions := [external_probe_inst; mk_inst 1 STOP [] []] |>]
End

Definition external_witness_context_def:
  external_witness_context =
    mk_venom_context [external_witness_fn] (SOME "entry")
End

Theorem external_probe_initial_state_excluded:
  ~o1_run_state_ok external_probe_source
Proof
  simp[o1_run_state_ok_def, o1_initial_state_ok_def,
       external_probe_source_def, init_venom_state_def,
       code_layout_valid_def, empty_call_context_def] >> EVAL_TAC
QED

Definition external_witness_source_def:
  external_witness_source = (init_venom_state "entry") with
    vs_labels := FEMPTY |+ ("code_end",0w)
End

Definition external_witness_request_def:
  external_witness_request =
    venom_call_request external_witness_source 256w 0w 0w 0w T
End

Definition external_witness_target_def:
  external_witness_target = external_witness_source with vs_outcomes :=
    [failed_outcome external_witness_request with co_returnData := [0w]]
End

Theorem external_witness_initial_state:
  o1_run_state_ok external_witness_source /\
  external_witness_source.vs_allocas = FEMPTY
Proof
  simp[o1_run_state_ok_def, o1_initial_state_ok_def,
       external_witness_source_def, init_venom_state_def,
       code_layout_valid_def, empty_call_context_def] >> EVAL_TAC
QED

Theorem external_witness_return_lengths:
  ?post tpost.
    step_inst_base external_probe_inst external_witness_source = OK post /\
    step_inst_base external_probe_inst external_witness_target = OK tpost /\
    LENGTH post.vs_returndata = 0 /\ LENGTH tpost.vs_returndata = 1
Proof
  simp[external_probe_dispatch, update_var_def] >>
  EVAL_TAC
QED

Theorem external_witness_no_local_successor:
  step_inst_base external_probe_inst external_witness_source = OK post ==>
  ~(?tpost. step_inst_base external_probe_inst external_witness_target = OK tpost /\
    local_rel P pr B R (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost)
Proof
  strip_tac >> strip_tac >>
  mp_tac external_witness_return_lengths >> strip_tac >> gvs[] >>
  gvs[frameRelocationLocalTheory.local_rel_def,
      ptrDisciplineTheory.dead_result_rel_def]
QED

Theorem external_witness_unchecked_call_excluded:
  ~o1_ctx_shape external_witness_context /\
  ~unitShapeDefs$call_checks_ok external_witness_fn
Proof
  EVAL_TAC
QED

Definition external_checked_fn_def:
  external_checked_fn = mk_raw_function "entry"
    [<| bb_label := "entry"; bb_instructions :=
      [external_probe_inst; mk_inst 1 ASSERT [Var "result"] [];
       mk_inst 2 STOP [] []] |>]
End

Definition external_checked_context_def:
  external_checked_context =
    mk_venom_context [external_checked_fn] (SOME "entry")
End

Theorem external_checked_shape:
  unitShapeDefs$call_checks_ok external_checked_fn /\
  EVERY wf_function external_checked_context.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) external_checked_context.ctx_functions /\
  ctx_inst_ids_distinct external_checked_context /\
  EVERY (\fn. fn.fn_eom = NONE) external_checked_context.ctx_functions
Proof
  EVAL_TAC
QED
