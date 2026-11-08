Theory algebraicOptComposeProofs
Ancestors
  algebraicOptSequenceLocalProofs algebraicOptRelationProofs
  venomExecSemantics venomState list algebraicOptDefs instIdxIndep
  algebraicOptCmpChunkProofs

Theorem ao_scalar_exact_input_transport:
  !inst s t r.
    MEM inst.inst_opcode
      [SHL; SHR; SAR; SIGNEXTEND; Exp; ADD; SUB; XOR; AND; MUL;
       Div; SDIV; Mod; SMOD; OR; EQ; GT; LT; SGT; SLT] /\
    step_inst_base inst s = OK t /\
    (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
       eval_operand a r = SOME w) ==>
    ?x v. inst.inst_outputs = [x] /\ t = update_var x v s /\
          step_inst_base inst r = OK (update_var x v r)
Proof
  rpt gen_tac >> pure_rewrite_tac [MEM] >> strip_tac >>
  gvs[step_inst_base_opcode_eqs] >>
  gvs[exec_pure2_def, AllCaseEqs()] >>
  metis_tac[]
QED

(* One commutation boundary shared by both operand-placement passes. *)
Theorem ao_commutative_swap_base:
  !i a b s t.
    (i.inst_opcode = ADD \/ i.inst_opcode = MUL \/
     i.inst_opcode = AND \/ i.inst_opcode = OR \/
     i.inst_opcode = XOR \/ i.inst_opcode = EQ) /\
    i.inst_operands = [a;b] /\ step_inst_base i s = OK t ==>
    step_inst_base (i with inst_operands := [b;a]) s = OK t
Proof
  rpt gen_tac >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()] >>
  simp[wordsTheory.WORD_ADD_COMM, wordsTheory.WORD_MULT_COMM,
       wordsTheory.WORD_AND_COMM, wordsTheory.WORD_OR_COMM,
       wordsTheory.WORD_XOR_COMM, EQ_SYM_EQ]
QED

Theorem ao_pre_flip_base_ok:
  !i s t. step_inst_base i s = OK t ==>
    step_inst_base (ao_pre_flip_inst i) s = OK t
Proof
  rpt strip_tac >>
  Cases_on `i.inst_operands` >> simp[ao_pre_flip_inst_def] >>
  rename1 `i.inst_operands = a::rest` >>
  Cases_on `rest` >> simp[ao_pre_flip_inst_def] >>
  rename1 `i.inst_operands = a::b::tail` >>
  Cases_on `tail` >> simp[ao_pre_flip_inst_def] >>
  IF_CASES_TAC >> gvs[] >>
  irule ao_commutative_swap_base >> metis_tac[]
QED

Theorem ao_post_flip_base_ok:
  !i s t. step_inst_base i s = OK t ==>
    step_inst_base (ao_post_flip_inst i) s = OK t
Proof
  rpt strip_tac >>
  Cases_on `i.inst_operands` >> simp[ao_post_flip_inst_def] >>
  rename1 `i.inst_operands = a::rest` >>
  Cases_on `rest` >> simp[ao_post_flip_inst_def] >>
  rename1 `i.inst_operands = a::b::tail` >>
  Cases_on `tail` >> simp[ao_post_flip_inst_def] >>
  IF_CASES_TAC >> gvs[] >>
  irule ao_commutative_swap_base >> metis_tac[]
QED

Theorem ao_post_flip_step_ok:
  !fuel ctx i s t. step_inst fuel ctx i s = OK t ==>
    step_inst fuel ctx (ao_post_flip_inst i) s = OK t
Proof
  rpt strip_tac >>
  Cases_on `i.inst_operands` >> simp[ao_post_flip_inst_def] >>
  rename1 `i.inst_operands = a::rest` >>
  Cases_on `rest` >> simp[ao_post_flip_inst_def] >>
  rename1 `i.inst_operands = a::b::tail` >>
  Cases_on `tail` >> simp[ao_post_flip_inst_def] >>
  IF_CASES_TAC >> gvs[step_inst_non_invoke] >>
  irule ao_commutative_swap_base >> metis_tac[]
QED

Theorem ao_post_flip_chunk_ok:
  !xs fuel ctx s t. ao_cmp_exec_chunk fuel ctx xs s = OK t ==>
    ao_cmp_exec_chunk fuel ctx (MAP ao_post_flip_inst xs) s = OK t
Proof
  Induct >> simp[ao_cmp_exec_chunk_def] >>
  rpt gen_tac >>
  Cases_on `step_inst fuel ctx h s` >>
  simp[ao_cmp_exec_chunk_def] >> strip_tac >>
  drule ao_post_flip_step_ok >> simp[]
QED
