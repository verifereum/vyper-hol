Theory bodyPtrBytestringBuiltinsCalldataOutcome
Ancestors
  bodyPtrBytestringBuiltinsEval bodyPtrBytestringBuiltinsSliceEndpoint
  exprSimSource exprSimWordArgs exprSimDefs exprSimHypsDefs
  vyperTyping valueEncoding words integer compileEnv vyperValue loweringSlice

(* The marked operand evidence fixes both the source integer and its actual
   runtime word; no independent existential execution is introduced. *)
Theorem calldata_slice_operand_endpoint:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT 256) /\
  expr_post ctx func cenv cx e es sa sm s0 ee v op t /\
  (?marks ee0. ee = ee0 with gas_obs := [] /\
    !tail. vyperState$bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks readings ++ tail) =
      (INL v,ee0 with gas_obs := tail)) ==>
  ?a. v = IntV (&a) /\ a < 2 ** 256 /\
    eval_operand op t = SOME (n2w a) /\ expr_sim_inv cenv cx env ee
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all operand_eval_evidence_semantics >> strip_tac >>
  `?i. v = IntV i /\ 0 <= i /\ Num i < 2 ** 256` by
    (fs[is_word_type_def, evaluate_type_def] >> Cases_on `v` >>
     gvs[is_word_type_def, evaluate_type_def, value_has_type_def]) >>
  gvs[] >> qexists_tac `Num i` >> simp[] >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  drule expr_post_word_operand >>
  simp[is_word_type_def, evaluate_type_def, word_value_def, val_to_w256_def,
    integer_wordTheory.i2w_def]
QED
