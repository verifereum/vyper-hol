Theory algebraicOptReadClosureProofs
Ancestors
  algebraicOptChainProofs algebraicOptDefs venomState venomExecSemantics list arithmetic

Theorem ao_iszero_exact_from_truth:
  (u = 0w <=> v = 0w) ==>
  ((if u = 0w then 1w else 0w):bytes32) = (if v = 0w then 1w else 0w)
Proof
  strip_tac >> Cases_on `u = 0w` >> gvs[]
QED

Theorem ao_resolve_iszero_cross_exact:
  ALOOKUP targets v = SOME chn /\ chn <> [] /\ LAST chn = Var v /\
  LENGTH ws = LENGTH chn /\ ao_word_chain ws /\
  (!j. j < LENGTH chn ==> eval_operand (EL j chn) s = SOME (EL j ws)) /\
  (!j. 0 < j /\ j < LENGTH chn ==>
       eval_operand (EL j chn) t = SOME (EL j ws)) /\
  eval_operand (Var v) t = eval_operand (Var v) s /\
  use_opcode <> JNZ /\ use_opcode <> ASSERT /\ use_opcode <> ASSERT_UNREACHABLE ==>
  eval_operand (ao_resolve_iszero_op targets use_opcode (Var v)) t =
  eval_operand (Var v) s
Proof
  strip_tac >>
  `eval_operand (Var v) s = SOME (LAST ws)` by metis_tac[ao_chain_last_eval] >>
  simp[ao_resolve_iszero_op_def] >>
  Cases_on `use_opcode = ISZERO` >> simp[] >>
  reverse (Cases_on `2 - (LENGTH chn - 1) MOD 2 < LENGTH chn - 1 /\
                    2 - (LENGTH chn - 1) MOD 2 < LENGTH chn`)
  >- simp[] >>
  gvs[] >>
  `EL (2 - (LENGTH chn - 1) MOD 2) ws = LAST ws` by
    (irule ao_word_chain_keep_exact >> simp[] >> metis_tac[]) >>
  `0 < 2 - (LENGTH chn - 1) MOD 2` by
    (`(LENGTH chn - 1) MOD 2 < 2` by simp[] >> decide_tac) >>
  `2 - (LENGTH chn - 1) MOD 2 < LENGTH chn` by decide_tac >>
  metis_tac[]
QED

Theorem ao_resolve_iszero_cross_truth:
  ALOOKUP targets v = SOME chn /\ chn <> [] /\ LAST chn = Var v /\
  LENGTH ws = LENGTH chn /\ ao_word_chain ws /\
  (!j. j < LENGTH chn ==> eval_operand (EL j chn) s = SOME (EL j ws)) /\
  (!j. 0 < j /\ j < LENGTH chn ==>
       eval_operand (EL j chn) t = SOME (EL j ws)) /\
  eval_operand (Var v) t = eval_operand (Var v) s /\
  (?root. eval_operand (HD chn) t = SOME root /\ (root = 0w <=> HD ws = 0w)) /\
  (use_opcode = JNZ \/ use_opcode = ASSERT \/ use_opcode = ASSERT_UNREACHABLE) ==>
  ?w. eval_operand (ao_resolve_iszero_op targets use_opcode (Var v)) t = SOME w /\
      (w = 0w <=> LAST ws = 0w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?root. _` strip_assume_tac >>
  `use_opcode <> ISZERO` by
    (qpat_assum `use_opcode = JNZ \/ _` mp_tac >> strip_tac >> gvs[]) >>
  `eval_operand (Var v) s = SOME (LAST ws)` by metis_tac[ao_chain_last_eval] >>
  simp[ao_resolve_iszero_op_def] >>
  qpat_x_assum `use_opcode = JNZ \/ _` kall_tac >>
  reverse (Cases_on `(LENGTH chn - 1) MOD 2 < LENGTH chn - 1 /\
                    (LENGTH chn - 1) MOD 2 < LENGTH chn`)
  >- simp[] >>
  gvs[] >>
  `(EL ((LENGTH chn - 1) MOD 2) ws = 0w <=> LAST ws = 0w)` by
    (irule ao_word_chain_keep_truth >> simp[] >> metis_tac[]) >>
  Cases_on `(LENGTH chn - 1) MOD 2 = 0`
  >- (gvs[] >> metis_tac[]) >>
  `0 < (LENGTH chn - 1) MOD 2 /\ (LENGTH chn - 1) MOD 2 < LENGTH chn` by decide_tac >>
  metis_tac[]
QED
