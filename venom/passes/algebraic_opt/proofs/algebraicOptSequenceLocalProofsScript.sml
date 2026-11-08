Theory algebraicOptSequenceLocalProofs
Ancestors
  algebraicOptLocalProofs algebraicOptRangeLocalProofs algebraicOptCmpChunkProofs
  instIdxIndep venomExecSemantics venomState algebraicOptDefs

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

Theorem ao_opt_eq_chunk_correct:
  !dfg fr inst s t fuel ctx.
    inst.inst_opcode = EQ /\ step_inst_base inst s = OK t /\
    SND (fr "not") <> SND (fr "iz") /\
    (!x. x = SND (fr "not") \/ x = SND (fr "iz") ==>
      ~MEM (Var x) inst.inst_operands /\ ~MEM x inst.inst_outputs) /\
    fr "xor" = fr "not" ==>
    ?u. ao_cmp_exec_chunk fuel ctx (ao_opt_eq dfg fr inst) s = OK u /\
      (u with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>) = t /\
      u.vs_inst_idx = s.vs_inst_idx + LENGTH (ao_opt_eq dfg fr inst) /\
      (!x. x <> SND (fr "not") /\ x <> SND (fr "iz") ==>
        lookup_var x u = lookup_var x t)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()] >>
  rename1 `inst.inst_operands = [a;b]` >>
  Cases_on `a = b`
  >- (gvs[ao_opt_eq_def] >>
      simp[ao_cmp_exec_chunk_single, step_inst_non_invoke,
           step_inst_base_opcode_eqs, exec_pure1_def, eval_operand_def,
           bool_to_word_def, update_var_def, lookup_var_def]) >>
  Cases_on `lit_eq b 0w`
  >- (Cases_on `b` >>
      gvs[passSharedDefsTheory.lit_eq_def, eval_operand_def, ao_opt_eq_def] >>
      simp[ao_cmp_exec_chunk_single, step_inst_non_invoke,
           step_inst_base_opcode_eqs, exec_pure1_def,
           update_var_def, lookup_var_def]) >>
  Cases_on `lit_eq b (0w - 1w)`
  >- (Cases_on `b` >>
      gvs[passSharedDefsTheory.lit_eq_def, eval_operand_def] >>
      simp[ao_opt_eq_def, passSharedDefsTheory.lit_eq_def] >>
      Cases_on `fr "not"` >>
      `ao_cmp_exec_chunk fuel ctx
         [<|inst_id := q; inst_opcode := NOT; inst_operands := [a];
            inst_outputs := [r]|>;
          inst with <|inst_opcode := ISZERO; inst_operands := [Var r]|>] s =
         OK ((update_var out (bool_to_word (~x = 0w))
                (update_var r (~x) s)) with vs_inst_idx := s.vs_inst_idx + 2)` by
        (irule ao_not_iszero_chunk >> simp[]) >>
      simp[] >>
      `(~x = 0w) = (x = 0w - 1w)` by
        (POP_ASSUM_LIST (K all_tac) >>
         rewrite_tac[wordsTheory.WORD_SUB_LZERO] >>
         metis_tac[wordsTheory.WORD_NOT_NOT, wordsTheory.WORD_NOT_0,
                   wordsTheory.WORD_NEG_1]) >>
      simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  Cases_on `ao_all_prefer_iszero dfg inst`
  >- (gvs[ao_opt_eq_def] >>
      Cases_on `fr "not"` >> gvs[] >>
      `step_inst fuel ctx
         <|inst_id := q; inst_opcode := XOR; inst_operands := [a;b];
           inst_outputs := [r]|> s = OK (update_var r (x ?? y) s)` by
        (simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure2_def]) >>
      drule ao_cmp_exec_chunk_two >>
      disch_then (qspec_then `inst with <|inst_opcode := ISZERO;
                                      inst_operands := [Var r]|>` SUBST1_TAC) >>
      `(x ?? y = 0w) = (x = y)` by
        (POP_ASSUM_LIST (K all_tac) >> eq_tac
         >- (disch_then (mp_tac o AP_TERM ``\w:bytes32. w ?? y``) >>
             simp[wordsTheory.WORD_XOR_ASSOC, wordsTheory.WORD_XOR_CLAUSES]) >>
         strip_tac >> simp[wordsTheory.WORD_XOR_CLAUSES]) >>
      simp[ao_cmp_exec_chunk_single, step_inst_non_invoke,
           step_inst_base_opcode_eqs, exec_pure1_def, eval_operand_def,
           lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
           arithmeticTheory.ADD1]) >>
  gvs[ao_opt_eq_def] >>
  simp[ao_cmp_exec_chunk_single, step_inst_non_invoke,
       step_inst_base_opcode_eqs, exec_pure2_def,
       update_var_def, lookup_var_def]
QED
