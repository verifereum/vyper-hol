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

(* Endpoint facts are shared by all signed comparator templates. *)
Theorem ao_signed_comparator_extremes[local]:
  !x:bytes32. ~(i2w INT256_MAX < x) /\ ~(x < i2w INT256_MIN)
Proof
  gen_tac >>
  qspec_then `x` assume_tac integer_wordTheory.w2i_le >>
  qspec_then `x` assume_tac integer_wordTheory.w2i_ge >>
  simp[integer_wordTheory.WORD_LTi] >>
  gvs[valueRangeDefsTheory.INT256_MAX_def,
      valueRangeDefsTheory.INT256_MIN_def] >>
  `w2i (i2w (integer_word$INT_MAX (:256)) : bytes32) =
     integer_word$INT_MAX (:256)` by
    (irule integer_wordTheory.w2i_i2w >>
     simp[integer_wordTheory.INT_MIN_def] >> intLib.ARITH_TAC) >>
  `w2i (i2w (integer_word$INT_MIN (:256)) : bytes32) =
     integer_word$INT_MIN (:256)` by
    (irule integer_wordTheory.w2i_i2w >>
     simp[integer_wordTheory.INT_MIN_def] >> intLib.ARITH_TAC) >>
  gvs[integer_wordTheory.INT_MAX, integer_wordTheory.INT_MIN] >>
  intLib.ARITH_TAC
QED

Theorem ao_signed_comparator_endpoints[local]:
  !x:bytes32.
    (i2w INT256_MAX - 1w < x <=> x = i2w INT256_MAX) /\
    (x < i2w INT256_MIN + 1w <=> x = i2w INT256_MIN) /\
    (i2w INT256_MIN < x <=> x <> i2w INT256_MIN) /\
    (x < i2w INT256_MAX <=> x <> i2w INT256_MAX)
Proof
  gen_tac >>
  `i2w INT256_MAX <> (i2w INT256_MIN : bytes32)` by
    (simp[valueRangeDefsTheory.INT256_MAX_def,
          valueRangeDefsTheory.INT256_MIN_def,
          integer_wordTheory.INT_MAX, integer_wordTheory.INT_MIN,
          wordsTheory.INT_MIN_def, wordsTheory.INT_MAX_def,
          fcpLib.INDEX_CONV ``dimindex(:256)``] >>
     EVAL_TAC >> CONV_TAC wordsLib.WORD_EVAL_CONV) >>
  simp[algebraicOptCmpLocalProofsTheory.ao_signed_lt_complement,
       algebraicOptCmpLocalProofsTheory.ao_signed_gt_complement] >>
  qspec_then `x` strip_assume_tac ao_signed_comparator_extremes >>
  metis_tac[wordsTheory.WORD_LESS_LESS_CASES, wordsTheory.WORD_LESS_REFL]
QED

Theorem ao_unsigned_comparator_endpoints[local]:
  !x:bytes32.
    ~((0w - 1w) <+ x) /\ ~(x <+ 0w) /\
    ((0w - 1w) - 1w <+ x <=> x = 0w - 1w) /\
    (x <+ 0w + 1w <=> x = 0w) /\
    (0w <+ x <=> x <> 0w) /\
    (x <+ 0w - 1w <=> x <> 0w - 1w)
Proof
  gen_tac >>
  simp[wordsTheory.WORD_SUB_LZERO,
       wordsTheory.WORD_LO_word_T, wordsTheory.WORD_LO_word_0,
       algebraicOptCmpLocalProofsTheory.ao_unsigned_lt_complement,
       algebraicOptCmpLocalProofsTheory.ao_unsigned_gt_complement]
QED

Theorem ao_iszero_iszero_chunk:
  !i j a tmp out s w fuel ctx.
    i.inst_opcode = ISZERO /\ i.inst_operands = [a] /\
    i.inst_outputs = [tmp] /\
    j.inst_opcode = ISZERO /\ j.inst_operands = [Var tmp] /\
    j.inst_outputs = [out] /\ eval_operand a s = SOME w ==>
    ao_cmp_exec_chunk fuel ctx [i;j] s =
      OK ((update_var out (bool_to_word (w <> 0w))
             (update_var tmp (bool_to_word (w = 0w)) s)) with
          vs_inst_idx := s.vs_inst_idx + 2)
Proof
  rpt strip_tac >>
  `step_inst fuel ctx i s = OK (update_var tmp (bool_to_word (w = 0w)) s)` by
    (simp[step_inst_non_invoke, step_inst_base_ISZERO, exec_pure1_def]) >>
  drule ao_cmp_exec_chunk_two >> disch_then (qspec_then `j` SUBST1_TAC) >>
  simp[ao_cmp_exec_chunk_single, step_inst_non_invoke,
       step_inst_base_ISZERO, exec_pure1_def, eval_operand_def,
       lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       arithmeticTheory.ADD1] >>
  Cases_on `w = 0w` >> simp[bool_to_word_def]
QED

Theorem ao_step_iszero_iszero_chunk:
  !i j k tmp iz out s w fuel ctx.
    step_inst fuel ctx i s = OK (update_var tmp w s) /\
    j.inst_opcode = ISZERO /\ j.inst_operands = [Var tmp] /\
    j.inst_outputs = [iz] /\
    k.inst_opcode = ISZERO /\ k.inst_operands = [Var iz] /\
    k.inst_outputs = [out] ==>
    ao_cmp_exec_chunk fuel ctx [i;j;k] s =
      OK ((update_var out (bool_to_word (w <> 0w))
             (update_var iz (bool_to_word (w = 0w)) (update_var tmp w s))) with
          vs_inst_idx := s.vs_inst_idx + 3)
Proof
  rpt strip_tac >>
  `ao_cmp_exec_chunk fuel ctx [j;k]
     ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx) =
    OK ((update_var out (bool_to_word (w <> 0w))
           (update_var iz (bool_to_word (w = 0w))
             ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx))) with
         vs_inst_idx :=
           (update_var tmp w s with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx + 2)` by
    (irule ao_iszero_iszero_chunk >>
     simp[eval_operand_def, lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE]) >>
  simp[Once ao_cmp_exec_chunk_def] >>
  gvs[update_var_def, arithmeticTheory.ADD1]
QED
