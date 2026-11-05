(* Allocation/store interface probe, shared by fixed-input hash suffixes. *)
Theory bodyPtrHashBuiltinsKeccakFixed
Ancestors
  bodyPtrHashBuiltinsKeccak allocationPtr typedCopyPtr bodyPtrDefs ptrDiscipline venomState
  venomExecSemantics venomInst words finite_map

Theorem hash_store_covered_clean:
  !PG G tn s id p value a w.
    ptr_covers G tn p s 32 /\ lookup_var p s = SOME a /\
    eval_operand value s = SOME w /\ op_taint tn value = {} ==>
    ptr_covers
      (step_prov PG G (mk_inst id MSTORE [Var p;value] []) (mstore (w2n a) w s))
      (step_taint (mk_inst id MSTORE [Var p;value] []) s (mstore (w2n a) w s) tn)
      p (mstore (w2n a) w s) 32 /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==>
      i NOTIN (step_taint (mk_inst id MSTORE [Var p;value] []) s
        (mstore (w2n a) w s) tn).t_mem)
Proof
  rpt strip_tac >> drule_all mstore_ghost_frame >> strip_tac >>
  gvs[ptr_covers_def, op_taint_def, mstore_def, lookup_var_def]
QED

Theorem hash_alloca_store_input:
  !ctx func cenv cx es s id p s1 PG G tn G1 tn1 sid value w.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit 32w] [p]) (fn_insts func) /\
    step_inst_base (mk_inst id ALLOCA [Lit 32w] [p]) s = OK s1 /\
    G1 = step_prov PG G (mk_inst id ALLOCA [Lit 32w] [p]) s1 /\
    tn1 = step_taint (mk_inst id ALLOCA [Lit 32w] [p]) s s1 tn /\
    eval_operand value s1 = SOME w /\ op_taint tn1 value = {} ==>
    ?a. lookup_var p s1 = SOME a /\
      ptr_covers
        (step_prov PG G1 (mk_inst sid MSTORE [Var p;value] []) (mstore (w2n a) w s1))
        (step_taint (mk_inst sid MSTORE [Var p;value] []) s1
          (mstore (w2n a) w s1) tn1) p (mstore (w2n a) w s1) 32 /\
      (!i. w2n a <= i /\ i < w2n a + 32 ==>
        i NOTIN (step_taint (mk_inst sid MSTORE [Var p;value] []) s1
          (mstore (w2n a) w s1) tn1).t_mem)
Proof
  rpt gen_tac >> strip_tac >>
  `32 < dimword (:256)` by
    simp[dimword_def, fcpTheory.index_bit0, fcpTheory.finite_bit0,
         fcpTheory.index_one, fcpTheory.finite_one] >>
  `ptr_covers G1 tn1 p s1 32` by
    (gvs[] >> irule alloca_step_ptr_covers >> metis_tac[]) >>
  `?a. lookup_var p s1 = SOME a` by gvs[ptr_covers_def] >>
  qexists `a` >> simp[] >> irule hash_store_covered_clean >> gvs[]
QED

Theorem hash_fixed_input_sha3_ok:
  !D ctx fn G tn s id p out m fuel.
    ptr_covers G tn p s 32 /\ m <= 32 /\ ~ctx_has_dalloca ctx /\
    (!a i. lookup_var p s = SOME a /\ w2n a <= i /\ i < w2n a + 32 ==>
       i NOTIN tn.t_mem) ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id SHA3 [Var p; Lit (n2w m)] [out]) s
Proof
  rpt strip_tac >>
  `m < dimword (:256)` by
    (simp[dimword_def, fcpTheory.index_bit0, fcpTheory.finite_bit0,
          fcpTheory.index_one, fcpTheory.finite_one] >> decide_tac) >>
  gvs[ptr_covers_def] >>
  irule hash_sha3_inst_ok >>
  simp[eval_operand_def, op_taint_def, w2n_n2w] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_LESS_TRANS,
            arithmeticTheory.LESS_EQ_MONO_ADD_EQ]
QED
