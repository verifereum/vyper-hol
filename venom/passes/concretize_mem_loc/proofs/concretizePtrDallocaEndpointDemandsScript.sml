Theory concretizePtrDallocaEndpointDemands
Ancestors
  concretizePtrDallocaRuntimeSteps concretizePtrDallocaDisciplineTransport
  concretizePtrValueTransport ptrDiscipline venomState venomInst
  contextCodegenRel finite_map pred_set words list

(* A tainted MUL operand need not preserve the unit selector.  Its other
   operand can be the clean zero selector, so this violates no discipline. *)
Theorem ptr_dalloca_mul_selector_probe:
  word_agree_except UNIV (1w:bytes32) 2w /\
  taint_ok fn (entry_taint with t_var := FEMPTY |+ ("x",UNIV))
    ((ARB:instruction) with <| inst_opcode := MUL;
      inst_operands := [Var "x"; Lit 0w] |>)
    ((ARB:venom_state) with vs_vars := FEMPTY |+ ("x",1w)) /\
  ~(eval_operand (Var "x")
      ((ARB:venom_state) with vs_vars := FEMPTY |+ ("x",1w)) = SOME 1w <=>
    eval_operand (Var "x")
      ((ARB:venom_state) with vs_vars := FEMPTY |+ ("x",2w)) = SOME 1w)
Proof
  simp[word_agree_except_def, taint_ok_def, entry_taint_def,
       op_taint_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
       source_memory_read_ranges_def, dimword_def] >>
  rpt strip_tac >> gvs[op_taint_def] >>
  simp[eval_operand_def]
QED
