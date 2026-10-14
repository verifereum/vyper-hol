(* TASK041: live assembly oracle/GAS regressions and retained counterevidence.
 * No assembly/EVM relation is strengthened here. *)
Theory asmOracleRegression
Ancestors
  asmSem codegenRel asmWf symbolResolve extCallOracle venomState
  venomExecSemantics vfmExecution vfmContext vfmOperation finite_map
Libs finite_mapLib

val () = computeLib.upd_compset add_finite_map_compset

Definition asm_oracle_initial_def:
  asm_oracle_initial =
    <| as_stack := []; as_memory := []; as_accounts := empty_accounts;
       as_transient := empty_transient_storage; as_returndata := [];
       as_logs := []; as_pc := 0; as_call_ctx := empty_call_context;
       as_tx_ctx := empty_tx_context; as_block_ctx := empty_block_context;
       as_code := []; as_prev_hashes := []; as_outcomes := [];
       as_requests := []; as_gas_readings := [] |>
End

Definition gas_counter_asm_def:
  gas_counter_asm = asm_oracle_initial with as_code := assemble [AsmOp "GAS"]
End

Definition gas_counter_evm_def:
  gas_counter_evm = make_asm_call_state gas_counter_asm 0w 100 0 []
                     (assemble [AsmOp "GAS"]) F
End

Theorem gas_code[simp]:
  assemble [AsmOp "GAS"] = [0x5aw] /\
  parse_code 0 FEMPTY [0x5aw] = FEMPTY |+ (0, Gas)
Proof
  conj_tac >- EVAL_TAC >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def,
       wordsTheory.dimword_8] >> simp[Once parse_code_def]
QED

val gas_eval_tac =
  simp[gas_code, step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       step_inst_def, step_context_def, push_stack_def, consume_gas_def,
       assert_def, inc_pc_or_jump_def, is_call_def, opcode_def,
       static_gas_def, LET_THM, FLOOKUP_UPDATE];

(* The old step theorem admitted GAS because it fell through to AsmError.
 * With GAS active, its existing pre-relation ignores readings; empty asm
 * readings push 0, whereas the concrete EVM pushes 98, without an exception.
 * This theorem is built BEFORE the old step theorem is minimally restricted. *)
Theorem gas_existing_relation_counterexample:
  asm_encoding_wf [AsmOp "GAS"] /\
  asm_evm_rel [AsmOp "GAS"] gas_counter_asm gas_counter_evm /\
  LENGTH gas_counter_evm.contexts = 1 /\
  gas_counter_asm.as_pc = 0 /\
  LENGTH gas_counter_asm.as_stack < vfmConstants$stack_limit /\
  ~is_data_inst (AsmOp "GAS") /\
  asm_step FEMPTY FEMPTY (AsmOp "GAS") gas_counter_asm =
    AsmOK (asm_next (gas_counter_asm with as_stack := [0w])) /\
  FST (step gas_counter_evm) = INL () /\
  (FST (HD (SND (step gas_counter_evm)).contexts)).stack = [98w] /\
  ~asm_evm_rel [AsmOp "GAS"]
    (asm_next (gas_counter_asm with as_stack := [0w]))
    (SND (step gas_counter_evm))
Proof
  conj_tac >- (
    rw[asm_encoding_wf_def, compute_label_offsets_def,
       asm_inst_size_def] >> EVAL_TAC) >>
  simp[asm_evm_rel_def, gas_counter_asm_def, gas_counter_evm_def,
       asm_oracle_initial_def, make_asm_call_state_def,
       empty_call_context_def, empty_tx_context_def, empty_block_context_def,
       asm_to_tx_params_def, make_sub_tx_def, make_rollback_def,
       vfmContextTheory.initial_context_def,
       vfmContextTheory.initial_msg_params_def,
       transfer_value_def, vfmContextTheory.empty_return_destination_def,
       asm_pc_to_offset_def, is_data_inst_def,
       asm_step_def, asm_step_op_def, asm_step_arith_def,
       asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
       asm_step_control_def, asm_step_extcall_def, asm_step_copy_def,
       asm_step_context_def, asm_gas_def, asm_push_val_def, asm_next_def] >>
  rpt conj_tac >| [suspend "step_success", suspend "step_stack",
                   suspend "step_unrelated"]
QED

Resume gas_existing_relation_counterexample[step_success]:
  gas_eval_tac
QED
Resume gas_existing_relation_counterexample[step_stack]:
  gas_eval_tac
QED
Resume gas_existing_relation_counterexample[step_unrelated]:
  gas_eval_tac >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]
QED
Finalise gas_existing_relation_counterexample

(* Exact old successful-step disjunction is false on the retained witness.
 * The old syntactic premises (including no calls) hold for [GAS]. *)
Theorem gas_old_step_claim_false:
  gas_counter_asm.as_pc < LENGTH [AsmOp "GAS"] /\
  (!j. j <= gas_counter_asm.as_pc ==>
       ~is_data_inst (EL j [AsmOp "GAS"])) /\
  (!i name. i < LENGTH [AsmOp "GAS"] /\ EL i [AsmOp "GAS"] = AsmOp name ==>
       ~(name = "CALL" \/ name = "STATICCALL" \/ name = "DELEGATECALL" \/
         name = "CREATE" \/ name = "CREATE2" \/ name = "SELFDESTRUCT")) /\
  ~((?es1 exc. step gas_counter_evm = (INR (SOME exc), es1) /\
                exc <> StackOverflow) \/
    (?es1. step gas_counter_evm = (INL (), es1) /\
      asm_evm_rel [AsmOp "GAS"]
        (asm_next (gas_counter_asm with as_stack := [0w])) es1 /\
      LENGTH es1.contexts = 1))
Proof
  strip_assume_tac gas_existing_relation_counterexample >>
  simp[gas_counter_asm_def, asm_oracle_initial_def, is_data_inst_def] >>
  Cases_on `step gas_counter_evm` >>
  gvs[gas_counter_asm_def, asm_oracle_initial_def]
QED
