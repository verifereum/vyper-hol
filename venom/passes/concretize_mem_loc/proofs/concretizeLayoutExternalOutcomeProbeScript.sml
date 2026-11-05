Theory concretizeLayoutExternalOutcomeProbe
Ancestors frameRelocationEnvironment frameRelocationLocal frameRelocationValues
  concretizeLayoutReaderContext
  venomCallOracleDefs venomExecSemantics venomState venomInst extCallOracle
  ptrDiscipline venomWf words list
Libs wordsLib

val () = augment_srw_ss [wordsLib.SIZES_ss, wordsLib.WORD_GROUND_ss];

Theorem outcome_update_incoming:
  relocation_env s (t with vs_outcomes := os) = relocation_env s t /\
  relocation_reader_context s (t with vs_outcomes := os) =
    relocation_reader_context s t /\
  local_rel P pr B R (\s t. dead_result_rel D (Halt s) (Halt t))
    s (t with vs_outcomes := os) =
  local_rel P pr B R (\s t. dead_result_rel D (Halt s) (Halt t)) s t
Proof
  simp[relocation_env_def, relocation_reader_context_def, local_rel_def,
       local_values_def, variable_domains_def, variables_agree_on_def,
       lookup_var_def, dead_result_rel_def]
QED

Definition external_probe_inst_def:
  external_probe_inst = mk_inst 0 STATICCALL
    [Lit 7w; Lit 256w; Lit 0w; Lit 0w; Lit 0w; Lit 0w] ["result"]
End

Definition external_probe_source_def:
  external_probe_source = init_venom_state "entry"
End

Definition external_probe_request_def:
  external_probe_request =
    venom_call_request external_probe_source 256w 0w 0w 0w T
End

Definition external_probe_target_def:
  external_probe_target = external_probe_source with vs_outcomes :=
    [failed_outcome external_probe_request with co_returnData := [0w]]
End

Theorem external_probe_dispatch:
  step_inst_base external_probe_inst s =
    OK (update_var "result"
      (FST (consume_call_outcome (venom_call_request s 256w 0w 0w 0w T) 0 0 s))
      (SND (consume_call_outcome (venom_call_request s 256w 0w 0w 0w T) 0 0 s)))
Proof
  simp[external_probe_inst_def, mk_inst_def, step_inst_base_def,
       eval_operand_def, exec_ext_call_def]
QED

val external_probe_defs =
  [external_probe_source_def, external_probe_target_def,
   external_probe_request_def, init_venom_state_def, empty_call_context_def,
   venom_call_request_def, read_memory_def, consume_call_outcome_eq,
   take_outcome_def, computed_precompile_addresses, failed_outcome_def,
   update_var_def, w2w_n2w];

Theorem external_probe_return_lengths:
  ?post tpost.
    step_inst_base external_probe_inst external_probe_source = OK post /\
    step_inst_base external_probe_inst external_probe_target = OK tpost /\
    LENGTH post.vs_returndata = 0 /\ LENGTH tpost.vs_returndata = 1
Proof
  simp[external_probe_dispatch, update_var_def] >>
  simp external_probe_defs >> EVAL_TAC
QED

Theorem external_probe_no_observation:
  step_inst_base external_probe_inst external_probe_source = OK post /\
  step_inst_base external_probe_inst external_probe_target = OK tpost ==>
  ~dead_result_rel D (Halt post) (Halt tpost)
Proof
  strip_tac >>
  mp_tac external_probe_return_lengths >> strip_tac >>
  gvs[] >> simp[dead_result_rel_def]
QED

(* The obstruction is at the mandatory observation, independent of every
   relocation mask, pointer relation and demand chosen by the caller. *)
Theorem external_probe_no_local_successor:
  step_inst_base external_probe_inst external_probe_source = OK post ==>
  ~(?tpost. step_inst_base external_probe_inst external_probe_target = OK tpost /\
    local_rel P pr B R (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost)
Proof
  strip_tac >> strip_tac >>
  drule local_rel_observation >> simp[] >>
  metis_tac[external_probe_no_observation]
QED

Theorem external_probe_access_taint:
  access_ok lo G fn external_probe_inst s /\
  taint_ok fn entry_taint external_probe_inst s
Proof
  simp[access_ok_def, taint_ok_def, external_probe_inst_def, mk_inst_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.memory_range_of_operands_def,
       eval_operand_def, entry_taint_def, op_taint_def] >>
  Cases_on `op` >> simp[]
QED

Theorem external_probe_well_formed:
  inst_wf external_probe_inst /\
  ~is_terminator external_probe_inst.inst_opcode /\
  external_probe_inst.inst_opcode <> INVOKE
Proof
  EVAL_TAC
QED
