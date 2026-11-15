(* Raw gas accounting for arithmetic and control instructions. *)
Theory asmNonCallCheapGas
Ancestors
  asmFrameRel asmRunBounded frameStep asmFrameLocalStep asmCallGasArithmetic
  vfmExecution vfmExecutionProp vfmOperation asmCheapOpcodeClassify asmDataSuffixProps

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

Theorem step_inst_access_gas_budget:
  MEM op [Balance; ExtCodeSize; ExtCodeHash] /\
  es.contexts = (c,rb)::rest /\ wf_context c /\
  2700 <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_inst op es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  simp[listTheory.MEM] >> strip_tac >> gvs[step_inst_def] >>
  gvs[step_balance_def, step_ext_code_size_def, step_ext_code_hash_def] >>
  gvs[pop_stack_def, bind_def, ignore_bind_def, get_current_context_def,
      set_current_context_def, assert_def, return_def, fail_def,
      wf_context_def, AllCaseEqs()] >>
  drule access_address_gas_observation >> strip_tac >>
  gvs[consume_gas_def, push_stack_def, get_accounts_def,
      bind_def, ignore_bind_def, get_current_context_def, return_def,
      set_current_context_def, assert_def, fail_def, LET_THM,
      frame_gas_left_def, AllCaseEqs()] >> decide_tac
QED

Theorem asm_noncall_cheap_gas_conditional:
  (!op es c rb rest B r s'.
    MEM op [Balance; ExtCodeSize; ExtCodeHash] /\
    es.contexts = (c,rb)::rest /\ wf_context c /\
    2700 <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
    step_inst op es = (r,s') ==>
    r <> INR (SOME OutOfGas) /\
    frame_gas_left es <= frame_gas_left s' + B) ==>
  !prog data es0 a es H.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
    a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
    EL a.as_pc prog <> AsmOp "RETURNDATACOPY" /\
    asm_inst_gas_ok H (EL a.as_pc prog) a.as_stack /\
    50000 + 8 * H + memory_cost H <= frame_gas_left es /\
    EL a.as_pc prog <> AsmOp "CALL" /\
    EL a.as_pc prog <> AsmOp "STATICCALL" /\
    ~MEM (EL a.as_pc prog) [AsmOp "DELEGATECALL"; AsmOp "CREATE";
      AsmOp "CREATE2"; AsmOp "SELFDESTRUCT"] /\
    ~(?name. EL a.as_pc prog = AsmOp name /\
       MEM name ["SLOAD";"SSTORE";"TLOAD";"TSTORE";"MLOAD";"MSTORE";
         "MSTORE8";"SHA3";"RETURN";"REVERT";"CALLDATACOPY";"CODECOPY";
         "EXTCODECOPY";"MCOPY";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]) ==>
    !op r s'.
      next_opcode (FST (HD es.contexts)) = SOME op /\
      step_inst op es = (r,s') /\
      LENGTH s'.contexts = LENGTH es.contexts ==>
      r <> INR (SOME OutOfGas) /\
      frame_gas_left es <= frame_gas_left s' +
        (50000 + 8 * H + memory_cost H)
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  fs[asm_frame_rel_def] >>
  `wf_context c` by gvs[wf_state_def] >>
  drule frame_next_opcode >>
  disch_then drule >> disch_then drule >>
  simp[] >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[] >>
  `encoding_wf_inst (EL a.as_pc prog) (SND (compute_label_offsets prog))` by
    (irule asmToBytecodeProofsTheory.asm_encoding_wf_el >>
     gvs[asm_frame_prog_ok_def]) >>
  `c.gasUsed <= c.msgParams.gasLimit` by gvs[wf_context_def] >>
  `50000 + 8 * H + memory_cost H <= c.msgParams.gasLimit - c.gasUsed` by
    gvs[frame_gas_left_def] >>
  `8 <= 50000 + 8 * H + memory_cost H /\
   3 <= 50000 + 8 * H + memory_cost H /\
   10 <= 50000 + 8 * H + memory_cost H /\
   20 <= 50000 + 8 * H + memory_cost H /\
   1610 <= 50000 + 8 * H + memory_cost H /\
   2700 <= 50000 + 8 * H + memory_cost H` by decide_tac >>
  Cases_on `?name. EL a.as_pc prog = AsmOp name`
  >- suspend "asmop" >>
  suspend "non_asmop"
QED

Resume asm_noncall_cheap_gas_conditional[asmop]:
      pop_assum strip_assume_tac >> gvs[] >>
      drule cheap_asmop_classify >>
      disch_then (qspecl_then
        [`SND (compute_label_offsets (prog ++ [AsmDataItem data]))`,`name`] mp_tac) >>
      (impl_tac >- gvs[asmToBytecodeProofsTheory.encoding_wf_inst_def,
          asm_inst_gas_ok_def, listTheory.MEM]) >>
      strip_tac >>
      `r <> INR (SOME OutOfGas) /\ frame_gas_left es <=
        frame_gas_left s' + (50000 + 8 * H + memory_cost H)` suffices_by
        simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >> all_tac
      >~ [`MEM op [Add; Mul; Sub; Div; SDiv; Mod; SMod; AddMod; MulMod;
        SignExtend; LT; GT; SLT; SGT; Eq; IsZero; And; Or; XOr; Not; Byte;
        ShL; ShR; SAR; CLZ]`] >-
        (irule step_inst_fixed_arithmetic_gas_budget >> simp[] >> qexists_tac `op` >>
         simp[Excl "MEM"] >> qpat_x_assum `MEM op _` mp_tac >> simp[listTheory.MEM]) 
      >~ [`MEM op [Address; Origin; Caller; CallValue; CallDataSize; CodeSize;
        GasPrice; ReturnDataSize; CoinBase; TimeStamp; Number; PrevRandao;
        GasLimit; ChainId; BaseFee; BlobBaseFee; PC; MSize; Gas]`] >-
        (irule step_inst_environment_gas_budget >> simp[] >> qexists_tac `op` >>
         simp[Excl "MEM"] >> qpat_x_assum `MEM op _` mp_tac >> simp[listTheory.MEM])
      >~ [`MEM op [Jump; JumpI; JumpDest; Stop; Invalid]`] >-
        (irule step_inst_control_gas_budget >> simp[] >> qexists_tac `op` >>
         simp[Excl "MEM"] >> qpat_x_assum `MEM op _` mp_tac >> simp[listTheory.MEM])
      >~ [`MEM op [CallDataLoad; BlockHash; BlobHash; SelfBalance]`] >-
        (irule step_inst_load_gas_budget >> simp[] >> qexists_tac `op` >>
         simp[Excl "MEM"] >> qpat_x_assum `MEM op _` mp_tac >> simp[listTheory.MEM])
      >~ [`MEM op [Balance; ExtCodeSize; ExtCodeHash]`] >-
        (CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV arithmeticTheory.ADD_COMM))) >>
         first_x_assum irule >> simp[] >> qexists_tac `op` >>
         qpat_x_assum `MEM op _` mp_tac >> simp[listTheory.MEM]) >>
      all_tac >~ [`op = Exp`] >- (
        qpat_x_assum `op = Exp` SUBST_ALL_TAC >>
        irule step_exp_gas_budget >> simp[GSYM step_inst_def]) >>
      irule step_inst_stack_gas_budget >> simp[] >>
      qexists_tac `op` >> simp[]
QED

Resume asm_noncall_cheap_gas_conditional[non_asmop]:
  `encoding_wf_inst (EL a.as_pc prog)
     (SND (compute_label_offsets (prog ++ [AsmDataItem data])))` by
    (mp_tac (Q.SPECL [`prog ++ [AsmDataItem data]`,`a.as_pc`]
       asmToBytecodeProofsTheory.asm_encoding_wf_el) >>
     simp[data_suffix_encoding_wf, listTheory.EL_APPEND_EQN] >>
     gvs[asm_frame_prog_ok_def]) >>
  drule cheap_non_asmop_classify >>
  disch_then (qspec_then `op` mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  `r <> INR (SOME OutOfGas) /\ frame_gas_left es <=
    frame_gas_left s' + (50000 + 8 * H + memory_cost H)` suffices_by
    simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  all_tac
  >~ [`op = Push n ws`] >-
    (irule step_inst_stack_gas_budget >> simp[] >>
     conj_tac >- gvs[] >> qexists_tac `op` >> simp[]) >>
  irule step_inst_control_gas_budget >> simp[] >>
  conj_tac >- gvs[] >> qexists_tac `op` >> simp[]
QED

Finalise asm_noncall_cheap_gas_conditional

Theorem asm_noncall_cheap_gas:
  !prog data es0 a es H.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
    a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
    EL a.as_pc prog <> AsmOp "RETURNDATACOPY" /\
    asm_inst_gas_ok H (EL a.as_pc prog) a.as_stack /\
    50000 + 8 * H + memory_cost H <= frame_gas_left es /\
    EL a.as_pc prog <> AsmOp "CALL" /\
    EL a.as_pc prog <> AsmOp "STATICCALL" /\
    ~MEM (EL a.as_pc prog) [AsmOp "DELEGATECALL"; AsmOp "CREATE";
      AsmOp "CREATE2"; AsmOp "SELFDESTRUCT"] /\
    ~(?name. EL a.as_pc prog = AsmOp name /\
       MEM name ["SLOAD";"SSTORE";"TLOAD";"TSTORE";"MLOAD";"MSTORE";
         "MSTORE8";"SHA3";"RETURN";"REVERT";"CALLDATACOPY";"CODECOPY";
         "EXTCODECOPY";"MCOPY";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]) ==>
    !op r s'.
      next_opcode (FST (HD es.contexts)) = SOME op /\
      step_inst op es = (r,s') /\
      LENGTH s'.contexts = LENGTH es.contexts ==>
      r <> INR (SOME OutOfGas) /\
      frame_gas_left es <= frame_gas_left s' +
        (50000 + 8 * H + memory_cost H)
Proof
  mp_tac asm_noncall_cheap_gas_conditional >>
  (impl_tac >- metis_tac[step_inst_access_gas_budget]) >>
  simp[]
QED
