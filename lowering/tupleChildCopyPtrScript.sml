(* A tuple expression supplies the padded source region for bytestring copying.
   Padding is transported by the copier, not assumed untainted. *)
Theory tupleChildCopyPtr
Ancestors tupleChildReadPtr typedCopyRobustFramePtr

Theorem compile_tuple_bytestring_child_robust_frag_ptr:
  !cx ctx PG R sa sb src dst G tn s a b len n tenv sty dty dtv
   func cenv t ea eb es vs p tvs w i.
    stmt_state_rel ctx func cenv cx es s /\
    expr_val_at cenv cx t ea eb es (ArrayV (TupleV vs)) (Var p) s /\
    ptr_val_ok cx t (ArrayV (TupleV vs)) (Var p) G tn s /\
    evaluate_type (get_tenv cx) t = SOME (TupleTV tvs) /\ ~is_word_type t /\
    values_have_types tvs vs /\ i < LENGTH tvs /\
    lookup_var p s = SOME w /\
    lookup_var src s = SOME a /\
    a = w + n2w (SUM (MAP type_memory_size (TAKE i tvs))) /\
    FLOOKUP G src = FLOOKUP G p /\ op_taint tn (Var src) = {} /\
    w2n a = w2n w + SUM (MAP type_memory_size (TAKE i tvs)) /\
    compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var dst s = SOME b /\
    n = 32 + 32 * ((len+31) DIV 32) /\
    len+31 < dimword(:256) /\ n < dimword(:256) /\
    ptr_covers G tn dst s n /\
    is_bytestring_type sty /\ is_bytestring_type dty /\
    evaluate_type tenv sty = SOME (EL i tvs) /\
    evaluate_type tenv dty = SOME dtv /\
    value_has_type (EL i tvs) (EL i vs) /\ value_has_type dtv (EL i vs) /\
    ((?bs. EL i vs = BytesV bs /\ len = LENGTH bs) \/
     (?str. EL i vs = StringV str /\ len = LENGTH str)) ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
      (!j. ~(w2n b <= j /\ j < w2n b+n) ==>
        mem_bytes_at j 1 sf.vs_memory = mem_bytes_at j 1 s.vs_memory) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
      (stor_taint_ok cx tn s ==> stor_taint_ok cx tnf sf) /\
      (!j. j < n ==> (w2n b+j IN tnf.t_mem <=> w2n a+j IN tn.t_mem)) /\
      (!j. ~(w2n b <= j /\ j < w2n b+n) ==>
        (j IN tnf.t_mem <=> j IN tn.t_mem)) /\
      (!q. not_fresh_at sa q ==>
        lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
        op_taint tnf (Var q) = op_taint tn (Var q)) /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory dtv (EL i vs) (w2n b) m) /\
      (!ft fv q. val_wf ft fv /\
        (q + type_memory_size ft <= w2n b \/ w2n b+n <= q) /\
        (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
          val_in_memory ft fv q m) ==>
        !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
          val_in_memory ft fv q m)
Proof
  rpt gen_tac >> strip_tac >>
  `val_store_size (EL i tvs) (EL i vs) = n` by
    (Cases_on `sty` >> gvs[compileEnvTheory.is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[compileEnvTheory.is_bytestring_type_def, vyperValueTheory.evaluate_type_def] >>
     gvs[AllCaseEqs()] >>
     qpat_x_assum `BaseTV _ = EL i tvs` (assume_tac o SYM) >>
     gvs[compileEnvTheory.is_bytestring_type_def,
       exprSimPropsTheory.val_store_size_def, vyperTypingTheory.value_has_type_def,
       vfmConstantsTheory.word_size_def]) >>
  `ptr_covers G tn src s n` by
    (qpat_assum `val_store_size _ _ = n` (SUBST1_TAC o SYM) >>
     irule expr_val_at_tuple_child_store_read_covers >> simp[] >>
     goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> qexistsl [`G`, `ctx`, `func`, `tn`] >> simp[]) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory (EL i tvs) (EL i vs) (w2n a) m` by
    (qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
     simp[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def,
       venomStateTheory.eval_operand_def] >> strip_tac >>
     `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
          tuple_in_memory vs tvs (w2n w) m` by
       (rpt strip_tac >> first_x_assum drule >>
        simp[valueEncodingTheory.val_in_memory_def]) >>
     qpat_x_assum `EL i vs = _` (SUBST1_TAC o SYM) >>
     once_rewrite_tac[arithmeticTheory.ADD_COMM] >> rpt strip_tac >>
     irule typedCopyLayoutPtrTheory.tuple_in_memory_robust_element >>
     simp[] >> conj_tac
     >- (qpat_x_assum `values_have_types _ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> qid_spec_tac `vs` >> Induct_on `tvs` >> Cases_on `vs` >>
         simp[vyperTypingTheory.value_has_type_def]) >>
     qexistsl [`s.vs_memory`, `tn`] >> simp[]) >>
  irule compile_store_bytestring_robust_ambient_frag_ptr >> simp[] >>
  gvs[] >> rpt conj_tac >> metis_tac[]
QED

(* Widen a nested String[1] into String[33]. No padding-cleanliness premise:
   robust representation concerns the header and the one character only. *)
Theorem tuple_string_widen_copy_probe[local]:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx (TupleT [BaseT (StringT 1)]) ea eb es
    (ArrayV (TupleV [StringV "a"])) (Var p) s /\
  ptr_val_ok cx (TupleT [BaseT (StringT 1)])
    (ArrayV (TupleV [StringV "a"])) (Var p) G tn s /\
  evaluate_type (get_tenv cx) (TupleT [BaseT (StringT 1)]) =
    SOME (TupleTV [BaseTV (StringT 1)]) /\
  lookup_var p s = SOME w /\ lookup_var src s = SOME w /\
  FLOOKUP G src = FLOOKUP G p /\ op_taint tn (Var src) = {} /\
  compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var dst s = SOME b /\ ptr_covers G tn dst s 64 ==>
  ?Gf tnf sf.
    frag_exec_ptr cx ctx PG sa sb
      (\g t v. g = G /\ t = tn /\ v = s)
      (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
    sf.vs_memory = (mcopy (w2n b) (w2n w) 64 s).vs_memory /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      val_in_memory (BaseTV (StringT 33)) (StringV "a") (w2n b) m)
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) (BaseT (StringT 1)) = SOME (BaseTV (StringT 1)) /\
   evaluate_type (get_tenv cx) (BaseT (StringT 33)) = SOME (BaseTV (StringT 33))`
    by (EVAL_TAC >> simp[wordsTheory.dimword_def]) >>
  drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)
    compile_tuple_bytestring_child_robust_frag_ptr >>
  simp[compileEnvTheory.is_word_type_def, vyperTypingTheory.value_has_type_def] >>
  simp[wordsTheory.WORD_ADD_0, wordsTheory.dimword_def] >>
  disch_then (drule_at (Pat `ptr_val_ok _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_store_bytestring _ _ _ = _`)) >>
  simp[] >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME (BaseTV (StringT 1))`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  simp[compileEnvTheory.is_bytestring_type_def, vyperTypingTheory.value_has_type_def] >>
  disch_then (qspecl_then [`PG`, `R`] strip_assume_tac) >>
  qexistsl [`Gf`, `tnf`, `sf`] >> simp[]
QED
