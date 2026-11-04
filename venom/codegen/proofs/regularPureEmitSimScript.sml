Theory regularPureEmitSim
Ancestors
  emitSim asmOpSim asmIR stackPlanGen venomExecSemantics venomEffects
  instSimHelpers list rich_list words venomInst venomState asmSem regularWordBridgeSim

Theorem pure_ordinary_value_step:
  MEM inst.inst_opcode
    [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; LT; GT; SLT; SGT;
     EQ; AND; OR; XOR; SHL; SHR; SAR; SIGNEXTEND; BYTE; NOT; ISZERO;
     ADDMOD; MULMOD] /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?values out result.
    inst.inst_outputs = [out] /\
    eval_operands (REVERSE (compute_operands inst)) vs = SOME values /\
    LENGTH values = LENGTH (compute_operands inst) /\
    vs' = update_var out result vs /\
    (!st. st.as_stack = values ++ DROP (LENGTH values) st.as_stack ==>
      asm_step_op o2pc name st =
        AsmOK (asm_next (st with as_stack := result :: DROP (LENGTH values) st.as_stack)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `MEM _ _` mp_tac >> simp[] >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def, AllCaseEqs()] >>
  strip_tac >>
  gvs[venom_to_evm_name_def, compute_operands_def, python_stack_operands_def,
      ir_specific_operand_order_def] >>
  simp[eval_operands_def] >>
  qmatch_goalsub_abbrev_tac `update_var out answer vs` >>
  qexists_tac `answer` >> simp[] >> rpt strip_tac >>
  (* Staged by what each pass unfolds: one pass over all 25 opcodes'
     string dispatch sits at the step budget under load. *)
  CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss())
    [asm_step_op_def, asm_step_arith_def, asm_unop_def, asm_binop_def,
     asm_ternop_def])) >>
  CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss())
    [asm_step_compare_def, asm_step_bitwise_def, asm_unop_def,
     asm_binop_def, asm_ternop_def])) >>
  qpat_assum `st.as_stack = _` (fn th => once_rewrite_tac [th]) >>
  simp[Abbr `answer`, asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_unop_def, asm_binop_def, asm_ternop_def,
       safe_div_def, safe_sdiv_def, safe_mod_def, safe_smod_def,
       addmod_def, mulmod_def, b2w_eq_bool_to_word] >>
  simp[asm_sign_extend_eq_venom, asm_byte_eq_evm_byte]
QED

Theorem pure_swapped_value_step[local]:
  is_commutative inst.inst_opcode /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  step_inst fuel ctx inst vs = OK vs' /\
  2 <= LENGTH (compute_operands inst) /\
  selected = TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
    [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
     EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)] ==>
  ?values out result.
    inst.inst_outputs = [out] /\
    eval_operands (REVERSE selected) vs = SOME values /\
    LENGTH values = LENGTH (compute_operands inst) /\
    LENGTH selected = LENGTH (compute_operands inst) /\
    vs' = update_var out result vs /\
    (!st. st.as_stack = values ++ DROP (LENGTH values) st.as_stack ==>
      asm_step_op o2pc name st =
        AsmOK (asm_next (st with as_stack := result :: DROP (LENGTH values) st.as_stack)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `inst.inst_opcode` >> gvs[is_commutative_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()] >>
  strip_tac >>
  gvs[venom_to_evm_name_def, compute_operands_def, python_stack_operands_def,
      ir_specific_operand_order_def] >>
  simp[eval_operands_def] >>
  qmatch_goalsub_abbrev_tac `update_var out answer vs` >>
  qexists_tac `answer` >> simp[] >> rpt strip_tac >>
  qpat_assum `st.as_stack = _` (fn th =>
    CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss())
      [asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_binop_def])) >>
    once_rewrite_tac [th]) >>
  simp[Abbr `answer`, asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_binop_def, b2w_eq_bool_to_word,
       WORD_ADD_COMM, WORD_MULT_COMM, WORD_AND_COMM, WORD_OR_COMM, WORD_XOR_COMM] >>
  rename1 `bool_to_word (y = x)` >>
  Cases_on `x = y` >> gvs[]
QED

Theorem pure_selected_value_step:
  MEM inst.inst_opcode
    [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; LT; GT; SLT; SGT;
     EQ; AND; OR; XOR; SHL; SHR; SAR; SIGNEXTEND; BYTE; NOT; ISZERO;
     ADDMOD; MULMOD] /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  step_inst fuel ctx inst vs = OK vs' /\
  (selected = compute_operands inst \/
   (is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst) /\
    selected = TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
      [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
       EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)])) ==>
  ?values out result.
    inst.inst_outputs = [out] /\
    eval_operands (REVERSE selected) vs = SOME values /\
    LENGTH values = LENGTH (compute_operands inst) /\
    LENGTH selected = LENGTH (compute_operands inst) /\
    vs' = update_var out result vs /\
    (!st. st.as_stack = values ++ DROP (LENGTH values) st.as_stack ==>
      asm_step_op o2pc name st =
        AsmOK (asm_next (st with as_stack := result :: DROP (LENGTH values) st.as_stack)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `_ \/ _` mp_tac >> strip_tac
  >- (qpat_x_assum `selected = _` SUBST_ALL_TAC >>
      drule_all pure_ordinary_value_step >> simp[]) >>
  drule_all pure_swapped_value_step >> simp[]
QED

Theorem swapped_inputs_mem[local]:
  2 <= LENGTH xs /\
  selected = TAKE (LENGTH xs - 2) xs ++
    [EL (LENGTH xs - 1) xs; EL (LENGTH xs - 2) xs] /\
  MEM op selected ==> MEM op xs
Proof
  strip_tac >> gvs[MEM_APPEND]
  >- metis_tac[MEM_TAKE] >>
  irule EL_MEM >> simp[]
QED

Theorem pure_arranged_emit_sim:
  MEM inst.inst_opcode
    [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; LT; GT; SLT; SGT;
     EQ; AND; OR; XOR; SHL; SHR; SAR; SIGNEXTEND; BYTE; NOT; ISZERO;
     ADDMOD; MULMOD] /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  step_inst fuel ctx inst vs = OK vs' /\
  (selected = compute_operands inst \/
   (is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst) /\
    selected = TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
      [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
       EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)])) /\
  venom_asm_rel lo ps vs st /\
  ps.ps_stack = residual ++ selected /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op vs = operand_val vs lo op) /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    inst.inst_outputs) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs) ==>
  ?st'. asm_step_op o2pc name st = AsmOK st' /\
    venom_asm_rel lo
      (ps with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
        (stack_pop (LENGTH (compute_operands inst)) ps.ps_stack) inst.inst_outputs)
      vs' st' /\ st'.as_pc = st.as_pc + 1
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!op. MEM op selected ==> MEM op (compute_operands inst)` by
    (qpat_x_assum `_ \/ _` mp_tac >> strip_tac
     >- gvs[] >> metis_tac[swapped_inputs_mem]) >>
  drule_all pure_selected_value_step >>
  disch_then (qspec_then `o2pc` (qx_choose_then `values` (qx_choose_then `out`
    (qx_choose_then `result` strip_assume_tac)))) >>
  `st.as_stack = values ++ DROP (LENGTH (REVERSE selected)) st.as_stack` by
    (irule arranged_eval_operands_stack >>
     conj_tac >- (gvs[EVERY_MEM] >> metis_tac[MEM_REVERSE]) >>
     qexistsl_tac [`lo`, `ps`, `residual`, `vs`] >>
     simp[] >> metis_tac[MEM_REVERSE]) >>
  `asm_step_op o2pc name st =
    AsmOK (asm_next (st with as_stack := result :: DROP (LENGTH values) st.as_stack))` by
    (first_x_assum irule >> gvs[]) >>
  `venom_asm_rel lo
    (ps with ps_stack := stack_push (Var out)
      (stack_pop (LENGTH values) ps.ps_stack))
    (update_var out result vs)
    (asm_next (st with as_stack := result :: DROP (LENGTH values) st.as_stack))` by
    (irule emit_output_venom_asm_rel >>
     conj_tac
     >- (qpat_x_assum `!op. op IN FDOM _ ==> _` mp_tac >> simp[]) >>
     simp[] >>
     qpat_x_assum `EVERY _ ps.ps_stack` mp_tac >> simp[]) >>
  qexists_tac `asm_next (st with as_stack := result :: DROP (LENGTH values) st.as_stack)` >>
  simp[asm_next_def] >>
  qpat_x_assum `venom_asm_rel lo (ps with ps_stack := _) _ _` mp_tac >>
  simp[asm_next_def]
QED
