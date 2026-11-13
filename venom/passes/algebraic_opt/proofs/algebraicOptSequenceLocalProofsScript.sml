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

Theorem ao_word_not_zero[local]:
  !x:bytes32. (~x = 0w) = (x = 0w - 1w)
Proof
  gen_tac >> rewrite_tac[wordsTheory.WORD_SUB_LZERO] >>
  metis_tac[wordsTheory.WORD_NOT_NOT, wordsTheory.WORD_NOT_0,
            wordsTheory.WORD_NEG_1]
QED

Theorem ao_word_xor_zero[local]:
  !x y:bytes32. (x ?? y = 0w) = (x = y)
Proof
  rpt gen_tac >> eq_tac
  >- (disch_then (mp_tac o AP_TERM ``\w:bytes32. w ?? y``) >>
      simp[wordsTheory.WORD_XOR_ASSOC, wordsTheory.WORD_XOR_CLAUSES]) >>
  strip_tac >> simp[wordsTheory.WORD_XOR_CLAUSES]
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
      simp[ao_word_not_zero] >>
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
      simp[ao_word_xor_zero] >>
      simp[ao_cmp_exec_chunk_single, step_inst_non_invoke,
           step_inst_base_opcode_eqs, exec_pure1_def, eval_operand_def,
           lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
           arithmeticTheory.ADD1, ao_word_xor_zero]) >>
  gvs[ao_opt_eq_def] >>
  simp[ao_cmp_exec_chunk_single, step_inst_non_invoke,
       step_inst_base_opcode_eqs, exec_pure2_def,
       update_var_def, lookup_var_def]
QED

(* Endpoint facts are shared by all signed comparator templates. *)
Theorem ao_signed_endpoints_not_unsigned[local]:
  (i2w INT256_MAX : bytes32) <> 0w /\
  (i2w INT256_MAX : bytes32) <> -1w /\
  (i2w INT256_MIN : bytes32) <> 0w /\
  (i2w INT256_MIN : bytes32) <> -1w
Proof
  simp[valueRangeDefsTheory.INT256_MAX_def,
       valueRangeDefsTheory.INT256_MIN_def,
       integer_wordTheory.INT_MAX, integer_wordTheory.INT_MIN,
       wordsTheory.INT_MIN_def, wordsTheory.INT_MAX_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  EVAL_TAC >> CONV_TAC wordsLib.WORD_EVAL_CONV
QED

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
     simp[integer_wordTheory.INT_MIN_def] >> Omega.OMEGA_TAC) >>
  `w2i (i2w (integer_word$INT_MIN (:256)) : bytes32) =
     integer_word$INT_MIN (:256)` by
    (irule integer_wordTheory.w2i_i2w >>
     simp[integer_wordTheory.INT_MIN_def] >> Omega.OMEGA_TAC) >>
  gvs[integer_wordTheory.INT_MAX, integer_wordTheory.INT_MIN] >>
  Omega.OMEGA_TAC
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

Theorem ao_cmp_prefer_iz_zero_chunk:
  !fr a inst out s w fuel ctx.
    inst.inst_outputs = [out] /\ eval_operand a s = SOME w ==>
    ao_cmp_exec_chunk fuel ctx (ao_cmp_prefer_iz_zero fr a inst) s =
      OK ((update_var out (bool_to_word (w <> 0w))
             (update_var (SND (fr "iz")) (bool_to_word (w = 0w)) s)) with
          vs_inst_idx := s.vs_inst_idx + 2)
Proof
  rpt strip_tac >> Cases_on `fr "iz"` >>
  simp[ao_cmp_prefer_iz_zero_def] >>
  irule ao_iszero_iszero_chunk >> simp[]
QED

Theorem ao_cmp_prefer_iz_max_chunk:
  !fr a inst out s w fuel ctx.
    inst.inst_outputs = [out] /\ eval_operand a s = SOME w ==>
    ao_cmp_exec_chunk fuel ctx (ao_cmp_prefer_iz_max fr a inst) s =
      OK ((update_var out (bool_to_word (~w <> 0w))
             (update_var (SND (fr "iz")) (bool_to_word (~w = 0w))
               (update_var (SND (fr "not")) (~w) s))) with
          vs_inst_idx := s.vs_inst_idx + 3)
Proof
  rpt strip_tac >> Cases_on `fr "not"` >> Cases_on `fr "iz"` >>
  simp[ao_cmp_prefer_iz_max_def] >>
  irule ao_step_iszero_iszero_chunk >>
  simp[step_inst_non_invoke, step_inst_base_NOT, exec_pure1_def]
QED

Theorem ao_cmp_prefer_iz_general_chunk:
  !fr a b inst out s x y fuel ctx.
    inst.inst_outputs = [out] /\ eval_operand a s = SOME x /\
    eval_operand b s = SOME y ==>
    ao_cmp_exec_chunk fuel ctx (ao_cmp_prefer_iz_general fr a b inst) s =
      OK ((update_var out (bool_to_word (x ?? y <> 0w))
             (update_var (SND (fr "iz")) (bool_to_word (x ?? y = 0w))
               (update_var (SND (fr "xor")) (x ?? y) s))) with
          vs_inst_idx := s.vs_inst_idx + 3)
Proof
  rpt strip_tac >> Cases_on `fr "xor"` >> Cases_on `fr "iz"` >>
  simp[ao_cmp_prefer_iz_general_def] >>
  irule ao_step_iszero_iszero_chunk >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure2_def]
QED

Theorem ao_opt_comparator_chunk_correct:
  !dfg ra lbl idx fr inst s t fuel ctx.
    (inst.inst_opcode = GT \/ inst.inst_opcode = LT \/
     inst.inst_opcode = SGT \/ inst.inst_opcode = SLT) /\
    step_inst_base inst s = OK t /\
    SND (fr "not") <> SND (fr "iz") /\
    (!x. x = SND (fr "not") \/ x = SND (fr "iz") ==>
      ~MEM (Var x) inst.inst_operands /\ ~MEM x inst.inst_outputs) /\
    fr "xor" = fr "not" /\
    (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
       in_range (range_get_range ra lbl idx a) w) ==>
    ?u. ao_cmp_exec_chunk fuel ctx
          (ao_opt_comparator dfg ra lbl idx fr inst) s = OK u /\
      (u with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>) = t /\
      u.vs_inst_idx = s.vs_inst_idx +
        LENGTH (ao_opt_comparator dfg ra lbl idx fr inst) /\
      (!x. x <> SND (fr "not") /\ x <> SND (fr "iz") ==>
        lookup_var x u = lookup_var x t)
Proof
  rpt gen_tac >> strip_tac >>
  (gvs[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()] >>
   rename1 `inst.inst_operands = [a;b]` >>
   Cases_on `a = b`
   >- (gvs[ao_opt_comparator_def] >>
       simp[ao_cmp_exec_chunk_single, step_inst_non_invoke,
            step_inst_base_opcode_eqs, exec_pure1_def, eval_operand_def,
            bool_to_word_def, update_var_def, lookup_var_def,
            wordsTheory.WORD_GREATER, wordsTheory.WORD_HIGHER]) >>
   Cases_on `ao_opt_cmp_range ra lbl idx inst
      (inst.inst_opcode = GT \/ inst.inst_opcode = SGT)
      (inst.inst_opcode = SGT \/ inst.inst_opcode = SLT)`
   >- (
     reverse (Cases_on `is_lit_op b`)
     >- (gvs[ao_opt_comparator_def, ao_signed_boundaries_def,
             ao_unsigned_boundaries_def] >>
         simp[ao_cmp_exec_chunk_single, step_inst_non_invoke,
              step_inst_base_opcode_eqs, exec_pure2_def,
              update_var_def, lookup_var_def]) >>
     Cases_on `b` >> gvs[passSharedDefsTheory.is_lit_op_def, eval_operand_def] >>
     gvs[ao_opt_comparator_def, ao_signed_boundaries_def,
         ao_unsigned_boundaries_def, passSharedDefsTheory.is_lit_op_def,
         passSharedDefsTheory.lit_eq_def] >>
     gvs[arithmeticTheory.GREATER_DEF, GSYM wordsTheory.WORD_LO,
         wordsTheory.WORD_GREATER] >>
     IF_CASES_TAC
     >- (gvs[] >>
         simp[ao_cmp_exec_chunk_single, step_inst_non_invoke,
              step_inst_base_opcode_eqs, exec_pure1_def, eval_operand_def,
              ao_signed_comparator_extremes, ao_unsigned_comparator_endpoints,
              wordsTheory.WORD_SUB_LZERO, wordsTheory.WORD_LO_word_T,
              bool_to_word_def, update_var_def, lookup_var_def]) >>
     IF_CASES_TAC
     >- (gvs[] >> Cases_on `fr "not"` >> gvs[] >>
         simp[ao_cmp_exec_chunk_def, step_inst_non_invoke,
              step_inst_base_opcode_eqs, exec_pure1_def, exec_pure2_def,
              eval_operand_def, lookup_var_def, update_var_def,
              finite_mapTheory.FLOOKUP_UPDATE,
              SRULE [] ao_signed_comparator_endpoints,
              ao_signed_endpoints_not_unsigned, ao_unsigned_comparator_endpoints,
              arithmeticTheory.ADD1, ao_word_not_zero,
              SRULE [] ao_unsigned_comparator_endpoints]) >>
     IF_CASES_TAC
     >- (`ao_cmp_exec_chunk fuel ctx
             (ao_cmp_prefer_iz_general fr a (Lit c) inst) s =
            OK ((update_var out (bool_to_word (x ?? c <> 0w))
                   (update_var (SND (fr "iz")) (bool_to_word (x ?? c = 0w))
                     (update_var (SND (fr "xor")) (x ?? c) s))) with
                 vs_inst_idx := s.vs_inst_idx + 3)` by
           (irule ao_cmp_prefer_iz_general_chunk >> simp[eval_operand_def]) >>
         gvs[] >>
         drule_all ao_cmp_prefer_iz_zero_chunk >>
         disch_then (qspecl_then [`fr`, `fuel`, `ctx`] assume_tac) >>
         drule_all ao_cmp_prefer_iz_max_chunk >>
         disch_then (qspecl_then [`fr`, `fuel`, `ctx`] assume_tac) >>
         simp[eval_operand_def,
              SRULE [] ao_unsigned_comparator_endpoints,
              ao_signed_comparator_endpoints, ao_word_not_zero,
              ao_word_xor_zero, ao_signed_endpoints_not_unsigned] >>
         Cases_on `fr "not"` >> Cases_on `fr "iz"` >>
         simp[ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
              ao_cmp_prefer_iz_general_def, update_var_def, lookup_var_def,
              finite_mapTheory.FLOOKUP_UPDATE]) >>
     Cases_on `inst.inst_opcode = GT /\ c = 0w`
     >- (gvs[] >> Cases_on `fr "iz"` >> gvs[] >>
         simp[ao_cmp_exec_chunk_def, step_inst_non_invoke,
              step_inst_base_opcode_eqs, exec_pure1_def, eval_operand_def,
              lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
              arithmeticTheory.ADD1, SRULE [] ao_unsigned_comparator_endpoints] >>
         Cases_on `x = 0w` >> simp[bool_to_word_def]) >>
     gvs[] >>
     simp[ao_cmp_exec_chunk_single, step_inst_non_invoke,
          step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def,
          lookup_var_def, update_var_def, arithmeticTheory.GREATER_DEF,
          GSYM wordsTheory.WORD_LO, wordsTheory.WORD_GREATER]) >>
   `in_range (range_get_range ra lbl idx a) x /\
    in_range (range_get_range ra lbl idx b) y` by metis_tac[] >>
   drule ao_opt_cmp_range_value >> disch_then drule >>
   disch_then drule >>
   disch_then (drule_at (Pat `ao_opt_cmp_range _ _ _ _ _ _ = SOME _`)) >>
   simp[] >> strip_tac >>
   gvs[ao_opt_comparator_def, ao_wrap_lit_def, bool_to_word_def,
       wordsTheory.WORD_GREATER, integer_wordTheory.WORD_LTi] >>
   simp[ao_cmp_exec_chunk_single, step_inst_non_invoke,
        step_inst_base_opcode_eqs, exec_pure1_def, update_var_def, lookup_var_def,
        oneline bool_to_word_def, integerTheory.INT_GT, wordsTheory.WORD_GREATER,
        arithmeticTheory.GREATER_DEF, integer_wordTheory.WORD_LTi])
QED

