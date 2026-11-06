(* A literal allocation obtains its ghost and structural resources from the
   same concrete execution, without requiring an expression postcondition. *)
Theory literalAllocPathPtr
Ancestors
  normalizerAllocationFrame allocaSiteResource revertAllocationPtr fragExecPtr
  fragGasSeqPtr fragGasPathPtr allocationPtr exprLoweringProps venomMemDefs
  venomInst venomState venomExecSemantics ptrDiscipline ptrSafeRun
  finite_map words arithmetic

Theorem literal_alloca_step_resources_ptr:
  alloca_inv s /\ alloca_room ctx fn s /\ fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w cap)] [root]) (fn_insts fn) /\
  cap < dimword(:256) /\
  (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w) ==>
  ?t b.
    step_inst_base (mk_inst id ALLOCA [Lit (n2w cap)] [root]) s = OK t /\
    lookup_var root t = SOME (n2w b) /\ b+cap < dimword(:256) /\
    FLOOKUP t.vs_allocas id = SOME (b,cap) /\
    ptr_covers
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w cap)] [root]) t)
      (step_taint (mk_inst id ALLOCA [Lit (n2w cap)] [root]) s t tn)
      root t cap /\
    alloca_inv t /\ alloca_room ctx fn t /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas aid = SOME (p,sz)) /\
    (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w)
Proof
  strip_tac >>
  drule_at (Pat `alloca_room _ _ _`)
    (SRULE [] (Q.INST [`inst` |-> `mk_inst id ALLOCA [Lit (n2w cap)] [root]`,
      `n` |-> `n2w cap`, `out` |-> `root`]
      literal_alloca_structural_resources)) >>
  disch_then (drule_at (Pat `MEM (mk_inst _ _ _ _) (fn_insts _)`)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `step_inst_base (mk_inst id ALLOCA [Lit (n2w cap)] [root]) s = OK t` by
    fs[step_inst_base_def, mk_inst_def] >>
  `FLOOKUP t.vs_allocas id = SOME (b,cap)` by fs[mk_inst_def] >>
  `b+cap < dimword(:256)` by
    (drule_all alloca_site_registered_below >>
     drule alloca_room_next_lt >> simp[]) >>
  qexistsl [`t`,`b`] >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  irule (cj 1 alloca_bounds_ptr_covers) >> simp[] >>
  conj_tac >- metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
  strip_tac >>
  `id NOTIN FDOM s.vs_allocas` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  drule_at (Pat `MEM _ (fn_insts _)`) alloca_room_fresh >>
  simp[mk_inst_def, FLOOKUP_DEF] >>
  disch_then (qspecl_then [`s`,`ctx`] mp_tac) >>
  simp[FLOOKUP_DEF]
QED

Theorem literal_alloca_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ALLOCA [Lit n] [root]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  step_inst_base (mk_inst id ALLOCA [Lit n] [root]) s = OK t ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ALLOCA [Lit n] [root]) t)
    (step_taint (mk_inst id ALLOCA [Lit n] [root]) s t tn)
    (OK (t with vs_inst_idx := s.vs_inst_idx+1))
Proof
  strip_tac >>
  `inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id ALLOCA [Lit n] [root]] s
    (step_prov PG G (mk_inst id ALLOCA [Lit n] [root]) t)
    (step_taint (mk_inst id ALLOCA [Lit n] [root]) s t tn)` by
    simp[inst_seq_ptr_def, ptr_inst_ok_alloca] >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    run_inst_seq_gas_path_ptr >>
  fs[run_inst_seq_def, mk_inst_def, is_terminator_def]
QED
