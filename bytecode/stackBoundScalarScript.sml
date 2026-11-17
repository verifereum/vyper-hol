(* Scalar instructions: only the untouched operand suffix is observable. *)
Theory stackBoundScalar
Ancestors
  stackBoundInterface stackBoundDefs vfmExecution vfmExecutionProp vfmConstants vfmContext
  list rich_list pair option finite_map words

Theorem sb_scalar_rule[local]:
  !op n cost f.
    ~is_call op /\
    (!s c rb rest. s.contexts = (c,rb)::rest ==>
      step_inst op s = bind (pop_stack n) (\args.
      bind (consume_gas (cost args)) (\u.
      bind get_current_context (\c.
      bind get_tx_params (\tx. push_stack (f args c tx))))) s) /\
    (!c a. sb_decoded c op /\ wf_context c ==>
      sb_successors c.msgParams.code (c.pc,a) =
        if n <= LENGTH a then
          [(c.pc + LENGTH (opcode op), NONE::DROP n a)] else []) ==>
    sb_opcode_contract op
Proof
  rpt gen_tac >> strip_tac >> simp[sb_opcode_contract_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >>
  PairCases_on `h` >> gvs[] >>
  `wf_context h0` by gvs[wf_state_def] >>
  `LENGTH a = LENGTH h0.stack` by
    metis_tac[bytecode_stack_describes_length] >>
  `bytecode_stack_describes (DROP n a) (DROP n h0.stack)` by
    metis_tac[bytecode_stack_describes_drop] >>
  simp[] >>
  Cases_on `n <= LENGTH h0.stack` >>
  Cases_on `cost (TAKE n h0.stack) + h0.gasUsed <= h0.msgParams.gasLimit` >>
  simp[pop_stack_def, consume_gas_def, push_stack_def,
       get_current_context_def, set_current_context_def, get_tx_params_def,
       bind_def, ignore_bind_def, assert_def, return_def, fail_def,
       sb_inner_def, inc_pc_or_jump_def] >>
  Cases_on `LENGTH h0.stack < n + stack_limit` >>
  gvs[sb_at_def, bytecode_stack_describes_def,
      set_current_context_def, return_def]
QED

Theorem sb_pop_push_rule[local]:
  !op n cost f.
    ~is_call op /\
    (step_inst op = bind (pop_stack n) (\args.
      bind (consume_gas (cost args)) (\u. push_stack (f args)))) /\
    (!c a. sb_decoded c op /\ wf_context c ==>
      sb_successors c.msgParams.code (c.pc,a) =
        if n <= LENGTH a then
          [(c.pc + LENGTH (opcode op), NONE::DROP n a)] else []) ==>
    sb_opcode_contract op
Proof
  rpt gen_tac >> strip_tac >> irule sb_scalar_rule >> simp[] >>
  qexistsl [`cost`, `\args c tx. f args`, `n`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `n <= LENGTH c.stack` >>
  Cases_on `cost (TAKE n c.stack) + c.gasUsed <= c.msgParams.gasLimit` >>
  simp[pop_stack_def, consume_gas_def, push_stack_def,
       get_current_context_def, set_current_context_def, get_tx_params_def,
       bind_def, ignore_bind_def, assert_def, return_def, fail_def] >>
  gvs[execution_state_component_equality]
QED

Theorem sb_binop_rule[local]:
  !op f.
    ~is_call op /\ step_inst op = step_binop op f /\
    (!c a. sb_decoded c op /\ wf_context c ==>
      sb_successors c.msgParams.code (c.pc,a) =
        if 2 <= LENGTH a then
          [(c.pc + LENGTH (opcode op), NONE::DROP 2 a)] else []) ==>
    sb_opcode_contract op
Proof
  rpt gen_tac >> strip_tac >> irule sb_pop_push_rule >> simp[] >>
  qexistsl [`K (static_gas op)`, `\args. f (EL 0 args) (EL 1 args)`, `2`] >>
  simp[step_binop_def, ignore_bind_def]
QED

Theorem sb_monop_rule[local]:
  !op f.
    ~is_call op /\ step_inst op = step_monop op f /\
    (!c a. sb_decoded c op /\ wf_context c ==>
      sb_successors c.msgParams.code (c.pc,a) =
        if 1 <= LENGTH a then
          [(c.pc + LENGTH (opcode op), NONE::DROP 1 a)] else []) ==>
    sb_opcode_contract op
Proof
  rpt gen_tac >> strip_tac >> irule sb_pop_push_rule >> simp[] >>
  qexistsl [`K (static_gas op)`, `\args. f (EL 0 args)`, `1`] >>
  simp[step_monop_def, ignore_bind_def]
QED

Theorem sb_modop_rule[local]:
  !op f.
    ~is_call op /\ step_inst op = step_modop op f /\
    (!c a. sb_decoded c op /\ wf_context c ==>
      sb_successors c.msgParams.code (c.pc,a) =
        if 3 <= LENGTH a then
          [(c.pc + LENGTH (opcode op), NONE::DROP 3 a)] else []) ==>
    sb_opcode_contract op
Proof
  rpt gen_tac >> strip_tac >> irule sb_pop_push_rule >> simp[] >>
  qexistsl [`K (static_gas op)`,
    `\args. if w2n (EL 2 args) = 0 then 0w else
      n2w (f (w2n (EL 0 args)) (w2n (EL 1 args)) MOD w2n (EL 2 args))`, `3`] >>
  simp[step_modop_def, ignore_bind_def]
QED

Theorem sb_binary_contracts[local]:
  MEM op [Add; Mul; Sub; Div; SDiv; Mod; SMod; SignExtend;
          LT; GT; SLT; SGT; Eq; And; Or; XOr; Byte; ShL; ShR; SAR] ==>
  sb_opcode_contract op
Proof
  simp[MEM] >> strip_tac >> gvs[] >>
  irule sb_binop_rule >> simp[is_call_def, step_inst_def] >>
  (reverse conj_tac >- metis_tac[]) >>
  rpt gen_tac >> simp[sb_decoded_def, wf_context_def, sb_successors_def] >>
  Cases_on `FLOOKUP (parse_code 0 FEMPTY c.msgParams.code) c.pc` >>
  simp[] >> strip_tac >>
  gvs[AllCaseEqs(), bytecode_stack_successors_def, bytecode_stack_io_def,
      REPLICATE_compute]
QED

Theorem sb_unary_contracts[local]:
  MEM op [IsZero; Not; CLZ] ==> sb_opcode_contract op
Proof
  simp[MEM] >> strip_tac >> gvs[] >>
  irule sb_monop_rule >> simp[is_call_def, step_inst_def] >>
  (reverse conj_tac >- metis_tac[]) >>
  rpt gen_tac >> simp[sb_decoded_def, wf_context_def, sb_successors_def] >>
  Cases_on `FLOOKUP (parse_code 0 FEMPTY c.msgParams.code) c.pc` >>
  simp[] >> strip_tac >>
  gvs[AllCaseEqs(), bytecode_stack_successors_def, bytecode_stack_io_def,
      REPLICATE_compute]
QED

Theorem sb_modular_contracts[local]:
  MEM op [AddMod; MulMod] ==> sb_opcode_contract op
Proof
  simp[MEM] >> strip_tac >> gvs[] >>
  irule sb_modop_rule >> simp[is_call_def, step_inst_def] >>
  (reverse conj_tac >- metis_tac[]) >>
  rpt gen_tac >> simp[sb_decoded_def, wf_context_def, sb_successors_def] >>
  Cases_on `FLOOKUP (parse_code 0 FEMPTY c.msgParams.code) c.pc` >>
  simp[] >> strip_tac >>
  gvs[AllCaseEqs(), bytecode_stack_successors_def, bytecode_stack_io_def,
      REPLICATE_compute]
QED

Theorem sb_exp_contract[local]:
  sb_opcode_contract Exp
Proof
  irule sb_pop_push_rule >> simp[is_call_def] >>
  qexistsl [`\args. static_gas Exp + exp_per_byte_cost *
    (if EL 1 args = 0w then 0 else SUC (LOG2 (w2n (EL 1 args)) DIV 8))`,
    `\args. word_exp (EL 0 args) (EL 1 args)`, `2`] >>
  simp[step_inst_def, step_exp_def, ignore_bind_def] >>
  rpt gen_tac >> simp[sb_decoded_def, wf_context_def, sb_successors_def] >>
  Cases_on `FLOOKUP (parse_code 0 FEMPTY c.msgParams.code) c.pc` >>
  simp[] >> strip_tac >>
  gvs[AllCaseEqs(), bytecode_stack_successors_def, bytecode_stack_io_def,
      REPLICATE_compute]
QED

Theorem sb_context_rule[local]:
  !op f.
    ~is_call op /\ step_inst op = step_context op f /\
    (!c a. sb_decoded c op /\ wf_context c ==>
      sb_successors c.msgParams.code (c.pc,a) =
        [(c.pc + LENGTH (opcode op), NONE::a)]) ==>
    sb_opcode_contract op
Proof
  rpt gen_tac >> strip_tac >> irule sb_scalar_rule >> simp[] >>
  qexistsl [`K (static_gas op)`, `\args c tx. f c`, `0`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `static_gas op + c.gasUsed <= c.msgParams.gasLimit` >>
  simp[step_context_def, pop_stack_def, consume_gas_def, push_stack_def,
       get_current_context_def, set_current_context_def, get_tx_params_def,
       bind_def, ignore_bind_def, assert_def, return_def, fail_def] >>
  gvs[execution_state_component_equality]
QED

Theorem sb_txParams_rule[local]:
  !op f.
    ~is_call op /\ step_inst op = step_txParams op f /\
    (!c a. sb_decoded c op /\ wf_context c ==>
      sb_successors c.msgParams.code (c.pc,a) =
        [(c.pc + LENGTH (opcode op), NONE::a)]) ==>
    sb_opcode_contract op
Proof
  rpt gen_tac >> strip_tac >> irule sb_scalar_rule >> simp[] >>
  qexistsl [`K (static_gas op)`, `\args c tx. f tx`, `0`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `static_gas op + c.gasUsed <= c.msgParams.gasLimit` >>
  simp[step_txParams_def, pop_stack_def, consume_gas_def, push_stack_def,
       get_current_context_def, set_current_context_def, get_tx_params_def,
       bind_def, ignore_bind_def, assert_def, return_def, fail_def] >>
  gvs[execution_state_component_equality]
QED

Theorem sb_context_contracts[local]:
  MEM op [Address; Caller; CallValue; CallDataSize; CodeSize;
          ReturnDataSize; PC; MSize; Gas] ==> sb_opcode_contract op
Proof
  simp[MEM] >> strip_tac >> gvs[] >>
  irule sb_context_rule >> simp[is_call_def, step_inst_def, step_msgParams_def] >>
  (reverse conj_tac >- metis_tac[]) >>
  rpt gen_tac >> simp[sb_decoded_def, wf_context_def, sb_successors_def] >>
  Cases_on `FLOOKUP (parse_code 0 FEMPTY c.msgParams.code) c.pc` >>
  simp[] >> strip_tac >>
  gvs[AllCaseEqs(), bytecode_stack_successors_def, bytecode_stack_io_def,
      REPLICATE_compute]
QED

Theorem sb_txParams_contracts[local]:
  MEM op [Origin; GasPrice; CoinBase; TimeStamp; Number; PrevRandao;
          GasLimit; ChainId; BaseFee; BlobBaseFee] ==> sb_opcode_contract op
Proof
  simp[MEM] >> strip_tac >> gvs[] >>
  irule sb_txParams_rule >> simp[is_call_def, step_inst_def] >>
  (reverse conj_tac >- metis_tac[]) >>
  rpt gen_tac >> simp[sb_decoded_def, wf_context_def, sb_successors_def] >>
  Cases_on `FLOOKUP (parse_code 0 FEMPTY c.msgParams.code) c.pc` >>
  simp[] >> strip_tac >>
  gvs[AllCaseEqs(), bytecode_stack_successors_def, bytecode_stack_io_def,
      REPLICATE_compute]
QED

Theorem sb_scalar_contracts:
  MEM op [Add; Mul; Sub; Div; SDiv; Mod; SMod; AddMod; MulMod; Exp;
          SignExtend; LT; GT; SLT; SGT; Eq; IsZero; And; Or; XOr; Not;
          Byte; ShL; ShR; SAR; CLZ;
          Address; Origin; Caller; CallValue; CallDataSize; CodeSize;
          GasPrice; ReturnDataSize; CoinBase; TimeStamp; Number; PrevRandao;
          GasLimit; ChainId; BaseFee; BlobBaseFee; PC; MSize; Gas] ==>
  sb_opcode_contract op
Proof
  strip_tac >>
  `MEM op [Add; Mul; Sub; Div; SDiv; Mod; SMod; SignExtend;
           LT; GT; SLT; SGT; Eq; And; Or; XOr; Byte; ShL; ShR; SAR] \/
   MEM op [IsZero; Not; CLZ] \/ MEM op [AddMod; MulMod] \/ op = Exp \/
   MEM op [Address; Caller; CallValue; CallDataSize; CodeSize;
           ReturnDataSize; PC; MSize; Gas] \/
   MEM op [Origin; GasPrice; CoinBase; TimeStamp; Number; PrevRandao;
           GasLimit; ChainId; BaseFee; BlobBaseFee]` by gvs[MEM] >>
  metis_tac[sb_binary_contracts, sb_unary_contracts, sb_modular_contracts,
            sb_exp_contract, sb_context_contracts, sb_txParams_contracts]
QED
