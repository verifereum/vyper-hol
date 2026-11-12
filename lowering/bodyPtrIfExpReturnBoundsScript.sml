Theory bodyPtrIfExpReturnBounds
Ancestors bodyPtrDefs exprSimProps valueEncoding finite_map ptrSafeRun

Theorem ifexp_ptr_mem_site_upper:
  !cx t v p G tn s tv w b n.
    ptr_mem_ok cx t v (Var p) G tn s /\
    evaluate_type (get_tenv cx) t = SOME tv /\
    eval_operand (Var p) s = SOME w /\
    FLOOKUP G p = SOME (b,n) /\ val_footprint tv v <> 0 ==>
    val_store_size tv v <= n
Proof
  rpt strip_tac >>
  qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
  simp[ptr_mem_ok_def] >>
  disch_then (qspecl_then [`tv`,`w`] mp_tac) >> simp[] >>
  strip_tac >> gvs[] >> decide_tac
QED

Theorem ifexp_tuple_annotation_exceeds_site:
  !cx p G tn s w b.
    eval_operand (Var p) s = SOME w /\ FLOOKUP G p = SOME (b,96) ==>
    ~ptr_mem_ok cx
      (TupleT [BaseT (BytesT (Dynamic 64)); BaseT (UintT 256)])
      (ArrayV (TupleV [BytesV []; IntV 42])) (Var p) G tn s
Proof
  rpt strip_tac >>
  `evaluate_type (get_tenv cx)
     (TupleT [BaseT (BytesT (Dynamic 64)); BaseT (UintT 256)]) =
   SOME (TupleTV [BaseTV (BytesT (Dynamic 64)); BaseTV (UintT 256)])`
    by (EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC) >>
  `val_footprint
     (TupleTV [BaseTV (BytesT (Dynamic 64)); BaseTV (UintT 256)])
     (ArrayV (TupleV [BytesV []; IntV 42])) <> 0` by EVAL_TAC >>
  drule_all ifexp_ptr_mem_site_upper >> EVAL_TAC
QED

Theorem ifexp_invoke_caller_prov:
  !fuel ctx PG G tn inst s p.
    inst.inst_opcode = INVOKE /\ ~MEM p inst.inst_outputs ==>
    FLOOKUP (FST (ghost_step fuel ctx PG G tn inst s)) p = FLOOKUP G p
Proof
  rpt strip_tac >> simp[Once ghost_step_def] >>
  Cases_on `decode_invoke inst` >> simp[] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 ctx.ctx_functions` >> simp[] >>
  Cases_on `eval_operands pair1 s` >> simp[] >>
  rename1 `eval_operands pair1 s = SOME args` >>
  Cases_on `setup_callee x args s` >> simp[FLOOKUP_DRESTRICT]
QED
