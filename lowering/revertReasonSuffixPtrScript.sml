(* Terminal ABI encoder checks use allocation bounds, not a source-state
   relation after scratch-memory writes. *)
Theory revertReasonSuffixPtr
Ancestors
  mstoreOperandStep revertReasonLayout revertReasonCopyPtr revertAllocationPtr revertReasonPtr
  typedCopyPtr fragGasSeqPtr fragExecPtr bodyPtrDefs decoderGhostFramePtr exprLoweringProps
  venomMemProps
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
    ptr_covers Gf tnf out
      ((mstore (w2n a) value s1) with vs_inst_idx := SUC (SUC s.vs_inst_idx)) 32 /\
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
  `ptr_covers
     (step_prov PG g1 (mk_inst (id+1) MSTORE [Var out; Lit value] [])
       (mstore (w2n a) value s2))
     (step_taint (mk_inst (id+1) MSTORE [Var out; Lit value] []) s2
       (mstore (w2n a) value s2) t1) out (mstore (w2n a) value s2) 32` by
    (irule ptr_covers_step_frame >>
     simp[mk_inst_def, mstore_def, lookup_var_def, Abbr `s2`] >>
     fs[ptr_covers_def, eval_operand_def, lookup_var_def]) >>
  simp[inst_seq_ptr_def] >> conj_tac
  >- (fs[ptr_covers_def, eval_operand_def, lookup_var_def, mstore_def, Abbr `s2`]) >>
  `eval_operand (Lit value) s2 = SOME value /\ op_taint t1 (Lit value) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (cj 5 mstore_ghost_frame) >> simp[]
QED

Theorem alloca_store_literal_path_ptr:
  (FLOOKUP s.vs_allocas id = NONE ==>
     s.vs_alloca_next+n < dimword(:256)) /\
  (!b sz. FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
     sz = n /\ b+n < dimword(:256)) /\
  32 <= n /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ALLOCA [Lit (n2w n)] [out];
            mk_inst (id+1) MSTORE [Var out; Lit value] []]
     (DROP s.vs_inst_idx bb.bb_instructions) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
  ?Gf tnf (a:bytes32).
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK ((mstore (w2n a) value s1) with vs_inst_idx := s.vs_inst_idx+2)) /\
    ptr_covers Gf tnf out
      ((mstore (w2n a) value s1) with vs_inst_idx := s.vs_inst_idx+2) 32 /\
    lookup_var out ((mstore (w2n a) value s1) with
       vs_inst_idx := s.vs_inst_idx+2) = SOME a /\
    mload (w2n a) ((mstore (w2n a) value s1) with
       vs_inst_idx := s.vs_inst_idx+2) = value /\
    (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >> drule_all alloca_store_literal_checks >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  `step_inst_base (mk_inst (id+1) MSTORE [Var out; Lit value] []) s1 =
    OK (mstore (w2n a) value s1)` by
    (irule step_mstore_operands >> simp[eval_operand_def]) >>
  `run_inst_seq [mk_inst id ALLOCA [Lit (n2w n)] [out];
       mk_inst (id+1) MSTORE [Var out; Lit value] []] s =
       OK (mstore (w2n a) value s1)` by simp[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      [mk_inst id ALLOCA [Lit (n2w n)] [out];
       mk_inst (id+1) MSTORE [Var out; Lit value] []]` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >>
  simp[mk_inst_def] >> strip_tac >>
  `mload (w2n a) ((mstore (w2n a) value s1) with
      vs_inst_idx := s.vs_inst_idx+2) = value` by
    (qsuff_tac `mload (w2n a) ((mstore (w2n a) value s1) with
        vs_inst_idx := s.vs_inst_idx+2) = mload (w2n a) (mstore (w2n a) value s1)`
     >- simp[mload_mstore_same] >>
     PURE_REWRITE_TAC[mload_def, venom_state_accfupds, combinTheory.K_THM] >>
     REFL_TAC) >>
  `lookup_var out ((mstore (w2n a) value s1) with
      vs_inst_idx := s.vs_inst_idx+2) = SOME a` by
    (qpat_x_assum `lookup_var out s1 = _` mp_tac >>
     simp[lookup_var_def, mstore_def]) >>
  qexistsl_tac [`Gf`, `tnf`, `a`] >> fs[ptr_covers_def, arithmeticTheory.ADD1]
QED
