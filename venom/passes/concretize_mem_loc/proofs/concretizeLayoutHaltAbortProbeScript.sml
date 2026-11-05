Theory concretizeLayoutHaltAbortProbe
Ancestors concretizeLayoutLocalLog concretizeLayoutLocalValues
  frameRelocationBinding frameJointTaint venomExecSemantics venomState ptrDiscipline
  frameRelocationLocal frameRelocationDemand frameRelocationEnvironment
  concretizeLayoutReaderContext

Theorem final_demand_excludes_taint:
  EL (LENGTH es) (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  a IN tn.t_mem ==>
  ~joint_relocation_demand lo positions q0 es qs (LENGTH es) a z
Proof
  rpt strip_tac >> fs[joint_relocation_demand_def] >>
  `j = LENGTH es` by decide_tac >>
  gvs[joint_observed_read_def, joint_mem_taint_def]
QED

Definition probe_return_def:
  probe_return = <| inst_id := 0; inst_opcode := RETURN;
    inst_operands := [Lit 0w; Lit 1w]; inst_outputs := [] |>
End

Definition probe_state_def:
  probe_state b = (init_venom_state "entry") with vs_memory := [b]
End

Theorem probe_return_zero:
  step_inst_base probe_return (probe_state 0w) =
  Halt (halt_state (set_returndata [0w] (probe_state 0w)))
Proof
  EVAL_TAC >> simp[wordsTheory.word_0_n2w, wordsTheory.word_1_n2w,
                   wordsTheory.w2n_n2w] >> EVAL_TAC
QED

Theorem probe_return_one:
  step_inst_base probe_return (probe_state 1w) =
  Halt (halt_state (set_returndata [1w] (probe_state 1w)))
Proof
  EVAL_TAC >> simp[wordsTheory.word_0_n2w, wordsTheory.word_1_n2w,
                   wordsTheory.w2n_n2w] >> EVAL_TAC
QED

Theorem probe_return_not_related:
  D.d_ret [0w] = {} ==>
  ~dead_result_rel D
    (step_inst_base probe_return (probe_state 0w))
    (step_inst_base probe_return (probe_state 1w))
Proof
  simp[probe_return_zero, probe_return_one, dead_result_rel_def,
       halt_state_def, set_returndata_def, probe_state_def,
       init_venom_state_def] >>
  rpt strip_tac >> first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

(* RETURN's discipline explicitly permits tainted payload bytes. *)
Theorem return_payload_taint_allowed:
  taint_ok fn tn probe_return s
Proof
  simp[taint_ok_def, probe_return_def] >>
  rpt strip_tac >> Cases_on `op` >> simp[op_taint_def]
QED

Theorem probe_return_taint_lane:
  ret_taint (entry_taint with t_mem := {0}) probe_return (probe_state 0w) = {0}
Proof
  simp[ret_taint_def, probe_return_def, eval_operand_def,
       wordsTheory.word_0_n2w, wordsTheory.word_1_n2w,
       wordsTheory.w2n_n2w, pred_setTheory.EXTENSION]
QED

Theorem probe_return_context:
  relocation_env (probe_state 0w) (probe_state 1w) /\
  relocation_reader_context (probe_state 0w) (probe_state 1w)
Proof
  simp[relocation_env_def, relocation_reader_context_def, probe_state_def]
QED

Theorem probe_return_incoming_observation:
  dead_result_rel D (Halt (probe_state 0w)) (Halt (probe_state 1w))
Proof
  simp[dead_result_rel_def, probe_state_def, init_venom_state_def,
       accounts_agree_except_def, transient_agree_except_def,
       storage_agree_except_def, imms_agree_except_def,
       word_agree_except_def]
QED

Theorem probe_return_local_relation:
  local_rel (\u. F) ptr B (\a z. F)
    (\s t. dead_result_rel D (Halt s) (Halt t))
    (probe_state 0w) (probe_state 1w)
Proof
  simp[local_rel_def, local_values_def, demand_agree_def,
       probe_return_incoming_observation,
       frameRelocationValuesTheory.variable_domains_def,
       frameRelocationValuesTheory.variables_agree_on_def,
       probe_state_def, init_venom_state_def, lookup_var_def]
QED

Definition probe_alloc_def:
  probe_alloc = <| inst_id := 0; inst_opcode := ALLOCA;
    inst_operands := [Lit 1w]; inst_outputs := ["p"] |>
End

Definition probe_allocated_def:
  probe_allocated = update_var "p" 0w
    ((init_venom_state "entry") with
      <| vs_allocas := FEMPTY |+ (0,(0,1)); vs_alloca_next := 1 |> )
End

Theorem probe_alloc_step:
  step_inst_base probe_alloc (init_venom_state "entry") = OK probe_allocated
Proof
  EVAL_TAC >> simp[wordsTheory.word_1_n2w, wordsTheory.w2n_n2w]
QED

Theorem probe_alloc_fresh_byte:
  0 IN (step_taint probe_alloc (init_venom_state "entry")
          probe_allocated entry_taint).t_mem
Proof
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
       probe_allocated_def, update_var_def, init_venom_state_def,
       entry_taint_def, step_writes_def, probe_alloc_def,
       range_bytes_def, written_taint_def,
       codegenRelTheory.source_memory_write_ranges_def,
       memLocDefsTheory.mem_write_ops_def,
       wordsTheory.word_0_n2w, wordsTheory.w2n_n2w] >>
  qexistsl_tac [`0`, `1`] >> simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Definition probe_alloc_return_def:
  probe_alloc_return = probe_return with
    <| inst_id := 1; inst_operands := [Var "p"; Lit 1w] |>
End

Definition probe_function_def:
  probe_function = venomInst$mk_raw_function "main"
    [<| bb_label := "entry";
        bb_instructions := [probe_alloc; probe_alloc_return] |>]
End

Definition probe_context_def:
  probe_context = venomInst$mk_venom_context [probe_function] (SOME "main")
End

Theorem probe_alloc_return_step:
  step_inst_base probe_alloc_return probe_allocated =
  Halt (halt_state (set_returndata [0w] probe_allocated))
Proof
  EVAL_TAC >> simp[wordsTheory.word_0_n2w, wordsTheory.word_1_n2w,
                   wordsTheory.w2n_n2w] >> EVAL_TAC
QED
