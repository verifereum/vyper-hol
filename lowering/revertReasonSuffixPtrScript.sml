(* Terminal ABI encoder checks use allocation bounds, not a source-state
   relation after scratch-memory writes. *)
Theory revertReasonSuffixPtr
Ancestors
  mstoreOperandStep revertReasonLayout revertReasonCopyPtr revertAllocationPtr revertReasonPtr
  typedCopyPtr fragGasSeqPtr fragExecPtr bodyPtrDefs decoderGhostFramePtr
  venomInst venomExecSemantics venomState ptrDiscipline words arithmetic finite_map

Theorem alloca_store_literal_checks:
  (FLOOKUP s.vs_allocas id = NONE ==>
     s.vs_alloca_next+n < dimword(:256)) /\
  (!b sz. FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
     sz = n /\ b+n < dimword(:256)) /\
  32 <= n /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
  ?Gf tnf a.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ALLOCA [Lit (n2w n)] [out];
       mk_inst (id+1) MSTORE [Var out; Lit value] []] s Gf tnf /\
    lookup_var out s1 = SOME a /\
    (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >>
  `ptr_covers
     (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
     (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn)
     out s1 n` by
    (irule (cj 1 alloca_bounds_ptr_covers) >> simp[]) >>
  `ptr_covers
     (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
     (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn)
     out s1 32` by
    (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS]) >>
  simp[Once inst_seq_ptr_def, ptr_inst_ok_alloca] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ g1 t1 _ s2 _ _` >>
  `ptr_inst_ok D 0 0 ctx fn g1 t1
     (mk_inst (id+1) MSTORE [Var out; Lit value] []) s2` by
    (irule ptr_inst_ok_mstore >>
     simp[op_taint_def, Abbr `g1`, Abbr `t1`, Abbr `s2`]) >>
  `?a. lookup_var out s1 = SOME a` by fs[ptr_covers_def, eval_operand_def] >>
  `lookup_var out s2 = SOME a` by fs[Abbr `s2`, lookup_var_def] >>
  `step_inst_base (mk_inst (id+1) MSTORE [Var out; Lit value] []) s2 =
     OK (mstore (w2n a) value s2)` by
    (irule step_mstore_operands >> simp[eval_operand_def]) >>
  simp[inst_seq_ptr_def] >>
  `eval_operand (Lit value) s2 = SOME value /\ op_taint t1 (Lit value) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (cj 5 mstore_ghost_frame) >> simp[]
QED
