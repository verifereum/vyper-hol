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

Theorem add_zero_ptr_covers:
  ptr_covers G tn src s n /\ lookup_var src s = SOME a ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var src; Lit 0w] [dst])
      (update_var dst a s))
    (step_taint (mk_inst id ADD [Var src; Lit 0w] [dst]) s
      (update_var dst a s) tn) dst (update_var dst a s) n
Proof
  strip_tac >>
  gvs[ptr_covers_def, eval_operand_def] >>
  simp[ptr_covers_def, eval_operand_def, step_prov_def, set_prov_def,
       out_prov_def, first_prov_def, op_prov_def, mk_inst_def,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
       step_taint_def, out_taint_def, set_var_taint_def, op_taint_def] >>
  fs[op_taint_def]
QED

Theorem add_zero_checks:
  ptr_covers G tn src s n /\ lookup_var src s = SOME a /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ADD [Var src; Lit 0w] [dst]] s Gf tnf /\
    ptr_covers Gf tnf dst (update_var dst a s) n /\
    tnf.t_mem = tn.t_mem /\
    (!x C. x <> dst /\ ptr_covers G tn x s C ==>
      ptr_covers Gf tnf x (update_var dst a s) C)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [Var src; Lit 0w] [dst]) s =
     OK (update_var dst a s)` by
    (simp[mk_inst_def] >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     PURE_REWRITE_TAC[instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
     simp[exec_pure2_def, eval_operand_def, WORD_ADD_0]) >>
  `op_taint tn (Var src) = {}` by fs[ptr_covers_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id ADD [Var src; Lit 0w] [dst]) s` by
    (irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  simp[inst_seq_ptr_def] >> conj_tac
  >- (irule add_zero_ptr_covers >> simp[]) >>
  conj_tac
  >- simp[cj 2 copy_len_binop_ghost_frame] >>
  rpt strip_tac >> irule ptr_covers_step_frame >>
  simp[mk_inst_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem mload_clean_cell_checks:
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MLOAD [Var src] [dst]] s Gf tnf /\
    op_taint tnf (Var dst) = {} /\ tnf.t_mem = tn.t_mem /\
    (!x C. x <> dst /\ ptr_covers G tn x s C ==>
      ptr_covers Gf tnf x (update_var dst (mload (w2n a) s) s) C)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MLOAD [Var src] [dst]) s =
     OK (update_var dst (mload (w2n a) s) s)` by
    (simp[mk_inst_def] >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     PURE_REWRITE_TAC[instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
     simp[exec_read1_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id MLOAD [Var src] [dst]) s` by
    (irule ptr_inst_ok_mload >> simp[]) >>
  simp[inst_seq_ptr_def] >>
  `op_taint (step_taint (mk_inst id MLOAD [Var src] [dst]) s
      (update_var dst (mload (w2n a) s) s) tn) (Var dst) = {} /\
   (step_taint (mk_inst id MLOAD [Var src] [dst]) s
      (update_var dst (mload (w2n a) s) s) tn).t_mem = tn.t_mem` by
    (conj_tac >- (irule (cj 1 mload_ghost_clean) >> simp[eval_operand_def]) >>
     irule (cj 2 mload_ghost_clean) >> simp[eval_operand_def]) >>
  simp[] >> rpt strip_tac >> irule ptr_covers_step_frame >>
  simp[mk_inst_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem alias_pair_load_checks:
  lookup_var q s = SOME Q /\ lookup_var p s = SOME P /\
  lookup_var cell s = SOME A /\
  op_taint tn (Var q) = {} /\ op_taint tn (Var p) = {} /\
  ptr_covers G tn cell s 32 /\
  (!i. w2n A <= i /\ i < w2n A+32 ==> i NOTIN tn.t_mem) /\
  p <> aq /\ cell <> aq /\ cell <> ap /\ ~ctx_has_dalloca ctx ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ADD [Var q; Lit 0w] [aq];
       mk_inst (id+1) ADD [Var p; Lit 0w] [ap];
       mk_inst (id+2) MLOAD [Var cell] [dst]] s Gf tnf /\
    op_taint tnf (Var dst) = {} /\ tnf.t_mem = tn.t_mem
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ _ _ [i;j;k] _ _ _` >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  `step_inst_base i s = OK (update_var aq Q s)` by
    (simp[Abbr `i`, mk_inst_def] >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     PURE_REWRITE_TAC[instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
     simp[exec_pure2_def, eval_operand_def, WORD_ADD_0]) >>
  simp[Once inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ g1 t1 _ s1 _ _` >>
  `t1.t_mem = tn.t_mem` by
    simp[Abbr `t1`, Abbr `i`, cj 2 copy_len_binop_ghost_frame] >>
  `ptr_covers g1 t1 cell s1 32` by
    (simp[Abbr `g1`, Abbr `t1`, Abbr `s1`] >>
     irule ptr_covers_step_frame >> simp[Abbr `i`, mk_inst_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> fs[lookup_var_def]) >>
  `lookup_var p s1 = SOME P /\ lookup_var cell s1 = SOME A` by
    fs[Abbr `s1`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `op_taint t1 (Var p) = {}` by
    (simp[Abbr `t1`, Abbr `i`, step_taint_def, set_var_taint_def,
       op_taint_def, mk_inst_def, FLOOKUP_UPDATE] >> fs[op_taint_def]) >>
  suspend "second"
QED

Resume alias_pair_load_checks[second]:
  `ptr_inst_ok D 0 0 ctx fn g1 t1 j s1` by
    (simp[Abbr `j`] >> irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  `step_inst_base j s1 = OK (update_var ap P s1)` by
    (simp[Abbr `j`, mk_inst_def] >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     PURE_REWRITE_TAC[instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
     simp[exec_pure2_def, eval_operand_def, WORD_ADD_0]) >>
  simp[Once inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ g2 t2 _ s2 _ _` >>
  `t2.t_mem = tn.t_mem` by
    simp[Abbr `t2`, Abbr `j`, cj 2 copy_len_binop_ghost_frame] >>
  `ptr_covers g2 t2 cell s2 32` by
    (simp[Abbr `g2`, Abbr `t2`, Abbr `s2`] >>
     irule ptr_covers_step_frame >> simp[Abbr `j`, mk_inst_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> fs[lookup_var_def]) >>
  `lookup_var cell s2 = SOME A` by
    fs[Abbr `s2`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `!i. w2n A <= i /\ i < w2n A+32 ==> i NOTIN t2.t_mem` by simp[] >>
  `ptr_inst_ok D 0 0 ctx fn g2 t2 k s2` by
    (simp[Abbr `k`] >> irule ptr_inst_ok_mload >> simp[]) >>
  `step_inst_base k s2 = OK (update_var dst (mload (w2n A) s2) s2)` by
    (simp[Abbr `k`, mk_inst_def] >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     PURE_REWRITE_TAC[instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
     simp[exec_read1_def, eval_operand_def]) >>
  simp[inst_seq_ptr_def, Abbr `k`] >> conj_tac
  >- (irule (cj 1 mload_ghost_clean) >> simp[eval_operand_def]) >>
  irule EQ_TRANS >> qexists_tac `t2.t_mem` >> conj_tac
  >- (irule (cj 2 mload_ghost_clean) >> simp[eval_operand_def]) >> simp[]
QED

Finalise alias_pair_load_checks
