(* Raw gas accounting for arithmetic and control instructions. *)
Theory asmNonCallCheapGas
Ancestors
  asmFrameRel asmRunBounded frameStep asmFrameLocalStep asmCallGasArithmetic
  vfmExecution vfmExecutionProp vfmOperation

Theorem step_inst_fixed_arithmetic_gas_budget:
  MEM op [Add; Mul; Sub; Div; SDiv; Mod; SMod; AddMod; MulMod;
          SignExtend; LT; GT; SLT; SGT; Eq; IsZero; And; Or; XOr;
          Not; Byte; ShL; ShR; SAR; CLZ] /\
  es.contexts = (c,rb)::rest /\ c.gasUsed <= c.msgParams.gasLimit /\
  8 <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_inst op es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  simp[listTheory.MEM] >> strip_tac >> gvs[step_inst_def]
  >>~- ([`step_monop _ _ es = (r,s')`],
        drule step_monop_gas_budget >>
        disch_then (qspecl_then [`c`,`rb`,`rest`,`B`] mp_tac) >>
        simp[static_gas_def] >> decide_tac)
  >>~- ([`step_modop _ _ es = (r,s')`],
        drule step_modop_gas_budget >>
        disch_then (qspecl_then [`c`,`rb`,`rest`,`B`] mp_tac) >>
        simp[static_gas_def] >> decide_tac) >>
  drule step_binop_gas_budget >>
  disch_then (qspecl_then [`c`,`rb`,`rest`,`B`] mp_tac) >>
        simp[static_gas_def] >> decide_tac
QED

Theorem step_exp_gas_budget:
  es.contexts = (c,rb)::rest /\ wf_context c /\
  1610 <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_exp es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  strip_tac >>
  gvs[step_exp_def, pop_stack_def, consume_gas_def, push_stack_def,
      bind_def, ignore_bind_def, get_current_context_def, return_def,
      set_current_context_def, assert_def, fail_def, LET_THM,
      wf_context_def, static_gas_def, vfmConstantsTheory.exp_per_byte_cost_def,
      AllCaseEqs()] >>
  fs[frame_gas_left_def] >>
  (qmatch_asmsub_abbrev_tac `w2n exponent` >>
  Cases_on `exponent = 0w` >- (gvs[] >> decide_tac) >>
  `LOG2 (w2n exponent) <= 255` by
    simp[wordsTheory.LOG2_w2n, venomLayoutTheory.dimindex_256] >>
  `LOG2 (w2n exponent) DIV 8 <= 31` by
    (simp[arithmeticTheory.DIV_LE_X] >> decide_tac) >>
  gvs[] >> decide_tac)
QED

Theorem step_inst_stack_gas_budget:
  (op = Pop \/ (?n ws. op = Push n ws) \/
   (?n. op = Dup n) \/ (?n. op = Swap n)) /\
  es.contexts = (c,rb)::rest /\ c.gasUsed <= c.msgParams.gasLimit /\
  3 <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_inst op es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  strip_tac >>
  gvs[step_inst_def, step_pop_def, step_push_def, step_dup_def,
      step_swap_def, pop_stack_def, consume_gas_def, push_stack_def,
      bind_def, ignore_bind_def, get_current_context_def, return_def,
      set_current_context_def, assert_def, fail_def, LET_THM,
      static_gas_def, AllCaseEqs()] >>
  fs[frame_gas_left_def] >> decide_tac
QED

Theorem step_context_gas_budget:
  step_context op f es = (r,s') /\
  es.contexts = (c,rb)::rest /\ c.gasUsed <= c.msgParams.gasLimit /\
  static_gas op <= B /\ B <= c.msgParams.gasLimit - c.gasUsed ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  strip_tac >>
  gvs[step_context_def, consume_gas_def, push_stack_def,
      bind_def, ignore_bind_def, get_current_context_def, return_def,
      set_current_context_def, assert_def, fail_def, LET_THM,
      AllCaseEqs()] >>
  fs[frame_gas_left_def] >> decide_tac
QED

Theorem step_txParams_gas_budget:
  step_txParams op f es = (r,s') /\
  es.contexts = (c,rb)::rest /\ c.gasUsed <= c.msgParams.gasLimit /\
  static_gas op <= B /\ B <= c.msgParams.gasLimit - c.gasUsed ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  strip_tac >>
  gvs[step_txParams_def, get_tx_params_def, consume_gas_def, push_stack_def,
      bind_def, ignore_bind_def, get_current_context_def, return_def,
      set_current_context_def, assert_def, fail_def, LET_THM,
      AllCaseEqs()] >>
  fs[frame_gas_left_def] >> decide_tac
QED

Theorem step_inst_environment_gas_budget:
  MEM op [Address; Origin; Caller; CallValue; CallDataSize; CodeSize;
          GasPrice; ReturnDataSize; CoinBase; TimeStamp; Number; PrevRandao;
          GasLimit; ChainId; BaseFee; BlobBaseFee; PC; MSize; Gas] /\
  es.contexts = (c,rb)::rest /\ c.gasUsed <= c.msgParams.gasLimit /\
  3 <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_inst op es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  simp[listTheory.MEM] >> strip_tac >>
  gvs[step_inst_def, step_msgParams_def]
  >>~- ([`step_context _ _ es = (r,s')`],
        drule step_context_gas_budget >>
        disch_then (qspecl_then [`rest`,`rb`,`c`,`B`] mp_tac) >>
        simp[static_gas_def] >> decide_tac) >>
  drule step_txParams_gas_budget >>
  disch_then (qspecl_then [`rest`,`rb`,`c`,`B`] mp_tac) >>
  simp[static_gas_def] >> decide_tac
QED

Theorem step_inst_control_gas_budget:
  MEM op [Jump; JumpI; JumpDest; Stop; Invalid] /\
  es.contexts = (c,rb)::rest /\ c.gasUsed <= c.msgParams.gasLimit /\
  10 <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_inst op es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  simp[listTheory.MEM] >> strip_tac >>
  gvs[step_inst_def, step_jump_def, step_jumpi_def, set_jump_dest_def,
      set_return_data_def, finish_def, pop_stack_def, consume_gas_def,
      bind_def, ignore_bind_def, get_current_context_def, return_def,
      set_current_context_def, assert_def, fail_def, LET_THM,
      static_gas_def, AllCaseEqs()] >>
  fs[frame_gas_left_def] >> decide_tac
QED

Theorem step_inst_load_gas_budget:
  MEM op [CallDataLoad; BlockHash; BlobHash; SelfBalance] /\
  es.contexts = (c,rb)::rest /\ c.gasUsed <= c.msgParams.gasLimit /\
  20 <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_inst op es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  simp[listTheory.MEM] >> strip_tac >>
  gvs[step_inst_def] >>
  rule_assum_tac (PURE_REWRITE_RULE [step_call_data_load_def, step_block_hash_def,
      step_blob_hash_def, step_self_balance_def, get_call_data_def,
      get_tx_params_def, get_accounts_def, get_callee_def,
      pop_stack_def, consume_gas_def, push_stack_def,
      bind_def, ignore_bind_def, get_current_context_def, return_def,
      set_current_context_def, assert_def, fail_def, LET_THM,
      static_gas_def, AllCaseEqs()]) >>
  gvs[bind_def, ignore_bind_def, get_current_context_def,
      get_tx_params_def, get_accounts_def, get_callee_def, get_call_data_def,
      set_current_context_def, return_def, assert_def, fail_def,
      frame_gas_left_def, AllCaseEqs()] >> decide_tac
QED

