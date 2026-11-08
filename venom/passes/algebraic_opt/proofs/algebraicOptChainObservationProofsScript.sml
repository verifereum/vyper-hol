Theory algebraicOptChainObservationProofs
Ancestors
  algebraicOptRelationProofs algebraicOptReadClosureProofs
  algebraicOptChainProofs venomState
Libs
  listTheory arithmeticTheory

Theorem ao_main_chain_positive_read:
  !fn V chn s r j.
    ao_chain_edges (fn_insts fn) chn /\
    ao_main_observations fn V s r /\
    (!i x. MEM i (fn_insts fn) /\
       (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) /\
    0 < j /\ j < LENGTH chn ==>
    eval_operand (EL j chn) r = eval_operand (EL j chn) s
Proof
  rpt strip_tac >> Cases_on `j` >> gvs[] >>
  gvs[ao_chain_edges_def] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  `ao_main_exact fn y` by metis_tac[ao_main_exact_iszero, MEM] >>
  `y IN V` by metis_tac[MEM] >>
  gvs[ao_main_observations_def] >>
  first_x_assum (qspec_then `y` mp_tac) >>
  simp[ao_main_lookup_def, eval_operand_def]
QED

Theorem ao_main_chain_root_read:
  !fn V chn ws s r.
    ao_chain_edges (fn_insts fn) chn /\ 1 < LENGTH chn /\
    LENGTH ws = LENGTH chn /\
    (!j. j < LENGTH chn ==> eval_operand (EL j chn) s = SOME (EL j ws)) /\
    ao_main_observations fn V s r /\ s.vs_labels = r.vs_labels /\
    (!i x. MEM i (fn_insts fn) /\
       (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) ==>
    ?root. eval_operand (HD chn) r = SOME root /\
           (root = 0w <=> HD ws = 0w)
Proof
  rpt strip_tac >>
  `eval_operand (HD chn) s = SOME (HD ws)` by
    (Cases_on `chn` >> Cases_on `ws` >> gvs[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qpat_x_assum `ao_chain_edges _ _` mp_tac >>
  simp[ao_chain_edges_def] >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `chn` >> gvs[] >>
  Cases_on `h` >> gvs[eval_operand_def] >>
  `s' IN V` by metis_tac[MEM] >>
  gvs[ao_main_observations_def] >>
  first_x_assum (qspec_then `s'` mp_tac) >>
  simp[ao_main_lookup_def] >>
  Cases_on `ao_main_exact fn s'` >> gvs[] >> metis_tac[]
QED

Theorem ao_main_resolve_chain_exact:
  !fn V chn ws s r targets v use_opcode.
    ao_chain_edges (fn_insts fn) chn /\ 1 < LENGTH chn /\
    LENGTH ws = LENGTH chn /\ ao_word_chain ws /\
    (!j. j < LENGTH chn ==> eval_operand (EL j chn) s = SOME (EL j ws)) /\
    ao_main_observations fn V s r /\ s.vs_labels = r.vs_labels /\
    (!i x. MEM i (fn_insts fn) /\
       (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) /\
    ALOOKUP targets v = SOME chn /\ LAST chn = Var v /\
    use_opcode <> JNZ /\ use_opcode <> ASSERT /\ use_opcode <> ASSERT_UNREACHABLE ==>
    eval_operand (ao_resolve_iszero_op targets use_opcode (Var v)) r =
    eval_operand (Var v) s
Proof
  rpt strip_tac >>
  `chn <> []` by (strip_tac >> gvs[]) >>
  `!j. 0 < j /\ j < LENGTH chn ==>
     eval_operand (EL j chn) r = eval_operand (EL j chn) s` by
    metis_tac[ao_main_chain_positive_read] >>
  `eval_operand (Var v) r = eval_operand (Var v) s` by
    (`EL (PRE (LENGTH chn)) chn = Var v` by metis_tac[LAST_EL] >>
     `0 < PRE (LENGTH chn) /\ PRE (LENGTH chn) < LENGTH chn` by decide_tac >>
     metis_tac[]) >>
  irule ao_resolve_iszero_cross_exact >>
  metis_tac[]
QED

Theorem ao_main_resolve_chain_truth:
  !fn V chn ws s r targets v use_opcode.
    ao_chain_edges (fn_insts fn) chn /\ 1 < LENGTH chn /\
    LENGTH ws = LENGTH chn /\ ao_word_chain ws /\
    (!j. j < LENGTH chn ==> eval_operand (EL j chn) s = SOME (EL j ws)) /\
    ao_main_observations fn V s r /\ s.vs_labels = r.vs_labels /\
    (!i x. MEM i (fn_insts fn) /\
       (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) /\
    ALOOKUP targets v = SOME chn /\ LAST chn = Var v /\
    (use_opcode = JNZ \/ use_opcode = ASSERT \/ use_opcode = ASSERT_UNREACHABLE) ==>
    ?w. eval_operand (ao_resolve_iszero_op targets use_opcode (Var v)) r = SOME w /\
        (w = 0w <=> LAST ws = 0w)
Proof
  rpt gen_tac >> strip_tac >>
  `chn <> []` by (strip_tac >> gvs[]) >>
  `!j. 0 < j /\ j < LENGTH chn ==>
     eval_operand (EL j chn) r = eval_operand (EL j chn) s` by
    metis_tac[ao_main_chain_positive_read] >>
  `eval_operand (Var v) r = eval_operand (Var v) s` by
    (`EL (PRE (LENGTH chn)) chn = Var v` by metis_tac[LAST_EL] >>
     `0 < PRE (LENGTH chn) /\ PRE (LENGTH chn) < LENGTH chn` by decide_tac >>
     metis_tac[]) >>
  `?root. eval_operand (HD chn) r = SOME root /\ (root = 0w <=> HD ws = 0w)` by
    metis_tac[ao_main_chain_root_read] >>
  irule ao_resolve_iszero_cross_truth >>
  metis_tac[]
QED
