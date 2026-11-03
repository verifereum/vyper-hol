Theory regularEmitSim
Ancestors
  regularPlanSim regularPureEmitSim regularReadEmitSim regularWriteEmitSim
  regularCallEmitSim stackPlanGen stackModel opcodeClass venomWf asmIR
  venomInst venomExecSemantics venomEffects list finite_map codegenRel
  contextCodegenRel asmSem

Theorem named_nonpure_not_commutative[local]:
  venom_to_evm_name opc = SOME name /\
  ~MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; LT; GT; SLT; SGT;
    EQ; AND; OR; XOR; SHL; SHR; SAR; SIGNEXTEND; BYTE; NOT; ISZERO;
    ADDMOD; MULMOD] ==> ~is_commutative opc
Proof
  Cases_on `opc` >> simp[venom_to_evm_name_def, is_commutative_def]
QED

Theorem named_nonpure_families[local]:
  venom_to_evm_name inst.inst_opcode = SOME name /\
  step_inst fuel ctx inst vs = OK vs' /\
  ~MEM inst.inst_opcode [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; LT; GT; SLT; SGT;
    EQ; AND; OR; XOR; SHL; SHR; SAR; SIGNEXTEND; BYTE; NOT; ISZERO;
    ADDMOD; MULMOD] ==>
  (ef_read0 inst.inst_opcode \/ ef_read1 inst.inst_opcode \/ inst.inst_opcode = SHA3) \/
  MEM inst.inst_opcode [MSTORE; MSTORE8; MCOPY; SSTORE; TSTORE;
    CALLDATACOPY; RETURNDATACOPY; CODECOPY; EXTCODECOPY] \/
  MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]
Proof
  strip_tac >> drule_all regular_named_ok_families >>
  Cases_on `inst.inst_opcode` >>
  gvs[ef_pure1_def, ef_arith1_def, ef_arith2_def, ef_cmp_def,
      ef_bits_def, ef_pure3_def, ef_read0_def, ef_read1_def,
      venom_to_evm_name_def]
QED

Theorem regular_emit_ok_sim:
  venom_to_evm_name inst.inst_opcode = SOME name /\
  inst.inst_opcode <> GAS /\ ~is_pre_codegen_opcode inst.inst_opcode /\
  inst_wf inst /\ (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
  step_inst fuel ctx inst vs = OK vs' /\
  (selected = compute_operands inst \/
   (is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst) /\
    selected = TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
      [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
       EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)])) /\
  venom_asm_rel lo ps vs st /\ plan_slots_bounded sb ps /\
  ps.ps_stack = residual ++ selected /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op vs = operand_val vs lo op) /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    inst.inst_outputs) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs) /\
  EVERY (\(off,len). len = 0 \/ off + len <= ps.ps_alloc.sa_spill_base \/
    ps.ps_alloc.sa_next_offset <= off) (source_memory_read_ranges inst vs) /\
  inst_memory_safe ps.ps_alloc inst vs vs' ==>
  ?st'. asm_step_op o2pc name st = AsmOK st' /\
    venom_asm_rel lo
      (ps with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
        (stack_pop (LENGTH (compute_operands inst)) ps.ps_stack) inst.inst_outputs)
      vs' st' /\ st'.as_pc = st.as_pc + 1
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `MEM inst.inst_opcode
    [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; LT; GT; SLT; SGT;
     EQ; AND; OR; XOR; SHL; SHR; SAR; SIGNEXTEND; BYTE; NOT; ISZERO;
     ADDMOD; MULMOD]`
  >- (irule pure_arranged_emit_sim >> metis_tac[]) >>
  `~is_commutative inst.inst_opcode` by
    (irule named_nonpure_not_commutative >> metis_tac[]) >>
  `selected = compute_operands inst` by metis_tac[] >>
  qpat_x_assum `selected = compute_operands inst` SUBST_ALL_TAC >>
  drule_all named_nonpure_families >> disch_then DISJ_CASES_TAC
  >- (drule_all read_arranged_emit_sim >> metis_tac[]) >>
  pop_assum DISJ_CASES_TAC
  >- suspend "write"
  >> suspend "external"
QED

Resume regular_emit_ok_sim[write]:
  `inst.inst_outputs = []` by
    (qpat_x_assum `MEM _ _` mp_tac >>
     pure_rewrite_tac [MEM] >> strip_tac >> fs[inst_wf_def]) >>
  drule_all write_arranged_emit_sim >> simp[] >> metis_tac[]
QED

Resume regular_emit_ok_sim[external]:
  `LENGTH inst.inst_outputs = 1` by
    (qpat_x_assum `MEM _ _` mp_tac >>
     pure_rewrite_tac [MEM] >> strip_tac >> fs[inst_wf_def]) >>
  `?out. inst.inst_outputs = [out]` by
    (Cases_on `inst.inst_outputs` >> fs[] >>
     rename1 `LENGTH rest = 0` >> Cases_on `rest` >> fs[]) >>
  `EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack` by
    (qpat_x_assum `EVERY _ ps.ps_stack` mp_tac >> simp[]) >>
  `!op. op IN FDOM ps.ps_spilled ==>
    case op of Var x => x <> out | _ => T` by
    (qpat_x_assum `!op. op IN FDOM _ ==> _` mp_tac >> simp[]) >>
  drule_all external_arranged_emit_sim >> simp[] >> metis_tac[]
QED
Finalise regular_emit_ok_sim
