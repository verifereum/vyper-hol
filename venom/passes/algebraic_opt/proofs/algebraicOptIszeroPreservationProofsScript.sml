Theory algebraicOptIszeroPreservationProofs
Ancestors
  algebraicOptReadClosureProofs algebraicOptChainAvailabilityProofs
  algebraicOptReachabilityProofs algebraicOptDefs venomExecSemantics venomState venomInst
Libs
  listTheory

Theorem ao_resolve_iszero_self:
  ao_resolve_iszero_op targets ISZERO op = op
Proof
  Cases_on `op` >> simp[ao_resolve_iszero_op_def] >>
  Cases_on `ALOOKUP targets s` >> simp[]
QED

Theorem ao_transform_iszero:
  inst.inst_opcode = ISZERO /\ inst.inst_operands = [op] ==>
  ao_transform_inst dfg ra lbl idx targets fr inst = [inst]
Proof
  strip_tac >>
  `ao_resolve_iszero_inst targets inst = inst` by
    simp[ao_resolve_iszero_inst_def, ao_resolve_iszero_self,
         instruction_component_equality] >>
  simp[ao_transform_inst_def, ao_opt_producer_def,
       ao_pre_flip_inst_def, ao_peephole_inst_def, ao_post_flip_inst_def]
QED

Theorem ao_transform_iszero_step_exact:
  inst.inst_opcode = ISZERO /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\ eval_operand op s = SOME u /\
  eval_operand op t = SOME v /\ (u = 0w <=> v = 0w) ==>
  ?word.
    step_inst fuel ctx inst s = OK (update_var out word s) /\
    (!inst'. MEM inst' (ao_transform_inst dfg ra lbl idx targets fr inst) ==>
      step_inst fuel ctx inst' t = OK (update_var out word t)) /\
    lookup_var out (update_var out word s) =
    lookup_var out (update_var out word t)
Proof
  strip_tac >> qexists_tac `bool_to_word (u = 0w)` >>
  `bool_to_word (u = 0w) = bool_to_word (v = 0w)` by
    simp[bool_to_word_def, ao_iszero_exact_from_truth] >>
  simp[ao_transform_iszero, step_inst_non_invoke, step_inst_base_def,
       exec_pure1_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED
