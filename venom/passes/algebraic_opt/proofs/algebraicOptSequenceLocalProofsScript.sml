Theory algebraicOptSequenceLocalProofs
Ancestors
  algebraicOptLocalProofs algebraicOptRangeLocalProofs algebraicOptCmpChunkProofs
  instIdxIndep venomExecSemantics venomState

(* The general non-INVOKE wrapper and nonterminator index covariance already
   exist: step_inst_non_invoke and step_inst_inst_idx_indep.  This boundary
   composes them with the canonical singleton chunk equation. *)
Theorem ao_base_step_chunk_single:
  !inst s t fuel ctx n.
    inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK t ==>
    ao_cmp_exec_chunk fuel ctx [inst] (s with vs_inst_idx := n) =
      OK (t with vs_inst_idx := SUC n)
Proof
  rpt strip_tac >>
  simp[ao_cmp_exec_chunk_single, step_inst_non_invoke,
       step_inst_inst_idx_indep, exec_result_map_def]
QED

Theorem ao_not_iszero_chunk:
  !i j a tmp out s w fuel ctx.
    i.inst_opcode = NOT /\ i.inst_operands = [a] /\
    i.inst_outputs = [tmp] /\
    j.inst_opcode = ISZERO /\ j.inst_operands = [Var tmp] /\
    j.inst_outputs = [out] /\ eval_operand a s = SOME w ==>
    ao_cmp_exec_chunk fuel ctx [i;j] s =
      OK ((update_var out (bool_to_word (~w = 0w))
             (update_var tmp (~w) s)) with
          vs_inst_idx := s.vs_inst_idx + 2)
Proof
  rpt strip_tac >>
  `step_inst fuel ctx i s = OK (update_var tmp (~w) s)` by
    (simp[step_inst_non_invoke, step_inst_base_NOT,
          exec_pure1_def]) >>
  drule ao_cmp_exec_chunk_two >> disch_then (qspec_then `j` SUBST1_TAC) >>
  simp[ao_cmp_exec_chunk_single, step_inst_non_invoke,
       step_inst_base_ISZERO, exec_pure1_def, eval_operand_def,
       lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       arithmeticTheory.ADD1]
QED
