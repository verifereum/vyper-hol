(* Single-range instruction gas accounting before exception handling. *)
Theory asmNonCallMemoryGas
Ancestors
  asmFrameRel asmRunBounded frameStep asmFrameLocalStep asmCallGasArithmetic
  vfmExecution vfmExecutionProp vfmConstants vfmOperation asmFrameCallStep codegenRel vfmState asmSem asmWf asmEncodeParse symbolResolve

Theorem step_mload_gas_budget:
  es.contexts = (c,rb)::rest /\ wf_context c /\
  asm_inst_gas_ok H (AsmOp "MLOAD") c.stack /\
  3 + memory_cost H <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_mload es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `c.stack`
  >- gvs[step_mload_def, pop_stack_def, bind_def, ignore_bind_def,
         get_current_context_def, assert_def, fail_def, return_def,
         frame_gas_left_def] >>
  rename1 `c.stack = off::stk` >>
  `w2n off + 32 <= H` by
    gvs[asm_inst_gas_ok_def, asm_mem_ranges_def] >>
  `memory_expansion_cost (buffer_length c.memory)
     (word_size (w2n off + 32) * 32) <= memory_cost H` by
    (irule memory_expansion_cost_bound >> simp[]) >>
  gvs[step_mload_def, pop_stack_def, memory_expansion_info_def,
      LET_THM, bind_def, ignore_bind_def, get_current_context_def,
      return_def, set_current_context_def, assert_def, fail_def] >>
  gvs[consume_gas_def, expand_memory_def, read_memory_def, push_stack_def,
      bind_def, ignore_bind_def, get_current_context_def, return_def,
      set_current_context_def, assert_def, fail_def, LET_THM,
      wf_context_def, AllCaseEqs()] >>
  gvs[frame_gas_left_def] >> decide_tac
QED

Theorem step_mstore_gas_budget:
  es.contexts = (c,rb)::rest /\ wf_context c /\
  (op = MStore /\ asm_inst_gas_ok H (AsmOp "MSTORE") c.stack \/
   op = MStore8 /\ asm_inst_gas_ok H (AsmOp "MSTORE8") c.stack) /\
  3 + memory_cost H <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_mstore op es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `c.stack`
  >- gvs[step_mstore_def, pop_stack_def, bind_def, ignore_bind_def,
         get_current_context_def, assert_def, fail_def, return_def,
         frame_gas_left_def] >>
  rename1 `c.stack = off::stk` >> Cases_on `stk`
  >- gvs[step_mstore_def, pop_stack_def, bind_def, ignore_bind_def,
         get_current_context_def, assert_def, fail_def, return_def,
         frame_gas_left_def] >>
  `w2n off + (if op = MStore8 then 1 else 32) <= H` by
    gvs[asm_inst_gas_ok_def, asm_mem_ranges_def] >>
  `memory_expansion_cost (buffer_length c.memory)
     (word_size (w2n off + (if op = MStore8 then 1 else 32)) * 32)
     <= memory_cost H` by
    (irule memory_expansion_cost_bound >> simp[]) >>
  gvs[step_mstore_def, pop_stack_def, memory_expansion_info_def,
      LET_THM, bind_def, ignore_bind_def, get_current_context_def,
      return_def, set_current_context_def, assert_def, fail_def] >>
  gvs[consume_gas_def, expand_memory_def, write_memory_def,
      bind_def, ignore_bind_def, get_current_context_def, return_def,
      set_current_context_def, assert_def, fail_def, LET_THM,
      wf_context_def, AllCaseEqs()] >>
  gvs[frame_gas_left_def] >> decide_tac
QED

Theorem step_return_gas_budget:
  es.contexts = (c,rb)::rest /\ wf_context c /\
  asm_inst_gas_ok H (AsmOp (if b then "RETURN" else "REVERT")) c.stack /\
  memory_cost H <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_return b es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  strip_tac >> Cases_on `c.stack`
  >- gvs[step_return_def, pop_stack_def, bind_def, ignore_bind_def,
         get_current_context_def, assert_def, fail_def, return_def,
         frame_gas_left_def] >>
  rename1 `c.stack = off::stk` >> Cases_on `stk`
  >- gvs[step_return_def, pop_stack_def, bind_def, ignore_bind_def,
         get_current_context_def, assert_def, fail_def, return_def,
         frame_gas_left_def] >>
  rename1 `c.stack = off::sz::stk'` >>
  `w2n sz = 0 \/ w2n off + w2n sz <= H` by
    (Cases_on `b` >> gvs[asm_inst_gas_ok_def, asm_mem_ranges_def]) >>
  `memory_expansion_cost (buffer_length c.memory)
    (if 0 < w2n sz then word_size (w2n off + w2n sz) * 32 else 0)
     <= memory_cost H` by
    (Cases_on `w2n sz = 0` >> simp[] >>
     once_rewrite_tac[arithmeticTheory.MULT_COMM] >>
     irule memory_expansion_cost_bound >> gvs[]) >>
  Cases_on `b` >>
  gvs[step_return_def, pop_stack_def, memory_expansion_info_def,
      LET_THM, bind_def, ignore_bind_def, get_current_context_def,
      return_def, set_current_context_def, assert_def, fail_def] >>
  gvs[consume_gas_def, expand_memory_def, read_memory_def, set_return_data_def,
      finish_def, revert_def, bind_def, ignore_bind_def,
      get_current_context_def, return_def, set_current_context_def,
      assert_def, fail_def, LET_THM, wf_context_def, AllCaseEqs()] >>
  gvs[frame_gas_left_def] >> decide_tac
QED

Theorem step_keccak256_gas_budget:
  es.contexts = (c,rb)::rest /\ wf_context c /\
  asm_inst_gas_ok H (AsmOp "SHA3") c.stack /\
  30 + 8 * H + memory_cost H <= B /\
  B <= c.msgParams.gasLimit - c.gasUsed /\
  step_keccak256 es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  strip_tac >> Cases_on `c.stack`
  >- gvs[step_keccak256_def, pop_stack_def, bind_def, ignore_bind_def,
         get_current_context_def, assert_def, fail_def, return_def,
         frame_gas_left_def] >>
  rename1 `c.stack = off::stk` >> Cases_on `stk`
  >- gvs[step_keccak256_def, pop_stack_def, bind_def, ignore_bind_def,
         get_current_context_def, assert_def, fail_def, return_def,
         frame_gas_left_def] >>
  rename1 `c.stack = off::sz::stk'` >>
  `w2n sz = 0 \/ w2n off + w2n sz <= H` by
    gvs[asm_inst_gas_ok_def, asm_mem_ranges_def] >>
  `memory_expansion_cost (buffer_length c.memory)
    (if 0 < w2n sz then word_size (w2n off + w2n sz) * 32 else 0)
     <= memory_cost H` by
    (Cases_on `w2n sz = 0` >> simp[] >>
     once_rewrite_tac[arithmeticTheory.MULT_COMM] >>
     irule memory_expansion_cost_bound >> gvs[]) >>
  `6 * word_size (w2n sz) <= 8 * H` by
    (Cases_on `w2n sz = 0` >- simp[word_size_def] >>
     `word_size (w2n sz) <= w2n sz` by
       (simp[word_size_def, arithmeticTheory.DIV_LE_X]) >> decide_tac) >>
  gvs[step_keccak256_def, pop_stack_def, memory_expansion_info_def,
      LET_THM, bind_def, ignore_bind_def, get_current_context_def,
      return_def, set_current_context_def, assert_def, fail_def] >>
  gvs[consume_gas_def, expand_memory_def, read_memory_def, push_stack_def,
      keccak256_per_word_cost_def, bind_def, ignore_bind_def,
      get_current_context_def, return_def, set_current_context_def,
      assert_def, fail_def, LET_THM, wf_context_def, AllCaseEqs()] >>
  gvs[frame_gas_left_def] >> decide_tac
QED

Theorem asm_frame_memory_decode[local]:
  asm_frame_prog_ok prog /\ asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp name /\
  MEM name ["MLOAD";"MSTORE";"MSTORE8";"SHA3";"RETURN";"REVERT"] ==>
  next_opcode (FST (HD es.contexts)) = SOME
    (if name = "MLOAD" then MLoad else if name = "MSTORE" then MStore
     else if name = "MSTORE8" then MStore8 else if name = "SHA3" then Keccak256
     else if name = "RETURN" then Return else Revert)
Proof
  strip_tac >> irule asm_frame_opcode_decode >>
  (conj_tac >- gvs[listTheory.MEM, wf_opname_def]) >>
  qexistsl_tac [`a`, `data`, `prog`] >>
  gvs[listTheory.MEM, is_data_inst_def, encode_inst_def, evm_opcode_byte_def,
      evm_opcode_table_def, wf_opname_def, opcode_def]
QED

Theorem asm_frame_memory_raw_gas:
  !prog data es0 a es H.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
    a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
    EL a.as_pc prog <> AsmOp "RETURNDATACOPY" /\
    asm_inst_gas_ok H (EL a.as_pc prog) a.as_stack /\
    50000 + 8 * H + memory_cost H <= frame_gas_left es /\
    EL a.as_pc prog <> AsmOp "CALL" /\
    EL a.as_pc prog <> AsmOp "STATICCALL" /\
    (?name. EL a.as_pc prog = AsmOp name /\
      MEM name ["MLOAD";"MSTORE";"MSTORE8";"SHA3";"RETURN";"REVERT"]) ==>
    !op r s'.
      next_opcode (FST (HD es.contexts)) = SOME op /\
      step_inst op es = (r,s') /\
      LENGTH s'.contexts = LENGTH es.contexts ==>
      r <> INR (SOME OutOfGas) /\
      frame_gas_left es <= frame_gas_left s' + (50000 + 8 * H + memory_cost H)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `asm_frame_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [asm_frame_rel_def]) >>
  `c.stack = a.as_stack` by gvs[asm_evm_rel_def] >>
  `wf_context c` by gvs[wf_state_def] >>
  `50000 + 8 * H + memory_cost H <= c.msgParams.gasLimit - c.gasUsed` by
    gvs[frame_gas_left_def] >>
  drule_all asm_frame_memory_decode >> strip_tac >>
  gvs[listTheory.MEM] >>
  rpt gen_tac >> strip_tac >> gvs[step_inst_def] >>
  `3 + memory_cost H <= 50000 + 8 * H + memory_cost H` by decide_tac >>
  `30 + 8 * H + memory_cost H <= 50000 + 8 * H + memory_cost H` by decide_tac >>
  `memory_cost H <= 50000 + 8 * H + memory_cost H` by decide_tac >>
  (qsuff_tac `r <> INR (SOME OutOfGas) /\
    frame_gas_left es <= frame_gas_left s' + (50000 + 8 * H + memory_cost H)`
   >- (strip_tac >> gvs[] >> decide_tac))
  >~ [`step_mload es = (r,s')`]
    >- (irule step_mload_gas_budget >> simp[] >> qexists_tac `H` >> simp[])
  >~ [`step_mstore MStore es = (r,s')`]
    >- (irule step_mstore_gas_budget >> simp[] >> metis_tac [arithmeticTheory.ADD_SYM, arithmeticTheory.ADD_ASSOC])
  >~ [`step_mstore MStore8 es = (r,s')`]
    >- (irule step_mstore_gas_budget >> simp[] >> qexistsl_tac [`H`, `MStore8`] >> simp[])
  >~ [`step_keccak256 es = (r,s')`]
    >- (irule step_keccak256_gas_budget >> simp[] >> qexists_tac `H` >> simp[])
  >~ [`step_return T es = (r,s')`]
    >- (irule step_return_gas_budget >> simp[] >> qexistsl_tac [`H`, `T`] >> simp[]) >>
  irule step_return_gas_budget >> simp[] >> qexistsl_tac [`H`, `F`] >> simp[]
QED
