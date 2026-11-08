(* Terminal ABI encoder checks use allocation bounds, not a source-state
   relation after scratch-memory writes. *)
Theory revertReasonSuffixPtr
Ancestors
  mstoreOperandStep revertReasonLayout revertReasonCopyPtr revertAllocationPtr revertReasonPtr
  typedCopyPtr fragGasSeqPtr fragExecPtr bodyPtrDefs decoderGhostFramePtr exprLoweringProps
  venomMemProps fragExec fragGasPathPtr gasCount ptrSafeRun typedCopyLoopHeaderPtr
  abiEncoderRounding revertReasonPrefixFramePtr list
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
    (simp[mk_inst_def] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accfupds, combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
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
    (simp[mk_inst_def] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accfupds, combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
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

Theorem alias_pair_load_run:
  lookup_var q s = SOME Q /\ lookup_var p s = SOME P /\
  lookup_var cell s = SOME A /\
  p <> aq /\ cell <> aq /\ cell <> ap ==>
  run_inst_seq
    [mk_inst id ADD [Var q; Lit 0w] [aq];
     mk_inst (id+1) ADD [Var p; Lit 0w] [ap];
     mk_inst (id+2) MLOAD [Var cell] [dst]] s =
  OK (update_var dst (mload (w2n A) s)
       (update_var ap P (update_var aq Q s)))
Proof
  strip_tac >> fs[lookup_var_def] >>
  simp[run_inst_seq_def, mk_inst_def] >>
  asm_simp_tac bool_ss [venomInstTheory.mk_inst_def, step_inst_base_opcode_eqs, instruction_accfupds,
    combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
  simp[exec_pure2_def, exec_read1_def, eval_operand_def,
    lookup_var_def, update_var_def, FLOOKUP_UPDATE, mload_def, WORD_ADD_0]
QED

Theorem alias_pair_load_checks:
  lookup_var q s = SOME Q /\ lookup_var p s = SOME P /\
  lookup_var cell s = SOME A /\
  op_taint tn (Var q) = {} /\ op_taint tn (Var p) = {} /\
  ptr_covers G tn cell s 32 /\
  (!i. w2n A <= i /\ i < w2n A+32 ==> i NOTIN tn.t_mem) /\
  p <> aq /\ cell <> aq /\ cell <> ap /\
  aq <> ap /\ aq <> dst /\ ap <> dst /\ ~ctx_has_dalloca ctx /\
  run_inst_seq
    [mk_inst id ADD [Var q; Lit 0w] [aq];
     mk_inst (id+1) ADD [Var p; Lit 0w] [ap];
     mk_inst (id+2) MLOAD [Var cell] [dst]] s = OK t ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ADD [Var q; Lit 0w] [aq];
       mk_inst (id+1) ADD [Var p; Lit 0w] [ap];
       mk_inst (id+2) MLOAD [Var cell] [dst]] s Gf tnf /\
    op_taint tnf (Var dst) = {} /\ tnf.t_mem = tn.t_mem /\
    lookup_var aq t = SOME Q /\ lookup_var ap t = SOME P /\
    lookup_var dst t = SOME (mload (w2n A) s) /\
    (!C. ptr_covers G tn q s C ==> ptr_covers Gf tnf aq t C) /\
    (!C. ptr_covers G tn p s C ==> ptr_covers Gf tnf ap t C) /\
    (!x C. x <> aq /\ x <> ap /\ x <> dst /\ ptr_covers G tn x s C ==>
       lookup_var x t = lookup_var x s /\ ptr_covers Gf tnf x t C) /\
    (!a. mload a t = mload a s)
Proof
  strip_tac >>
  `t = update_var dst (mload (w2n A) s) (update_var ap P (update_var aq Q s))` by
    (`run_inst_seq
       [mk_inst id ADD [Var q; Lit 0w] [aq];
        mk_inst (id+1) ADD [Var p; Lit 0w] [ap];
        mk_inst (id+2) MLOAD [Var cell] [dst]] s =
       OK (update_var dst (mload (w2n A) s) (update_var ap P (update_var aq Q s)))`
       by (irule alias_pair_load_run >> simp[]) >> fs[]) >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ _ _ [i;j;k] _ _ _` >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  `step_inst_base i s = OK (update_var aq Q s)` by
    (simp[Abbr `i`, mk_inst_def] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accfupds, combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
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
    (simp[Abbr `j`, mk_inst_def] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accfupds, combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
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
    (simp[Abbr `k`, mk_inst_def] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accfupds, combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
     simp[exec_read1_def, eval_operand_def]) >>
  simp[inst_seq_ptr_def, Abbr `k`] >> conj_tac
  >- (irule (cj 1 mload_ghost_clean) >> simp[eval_operand_def]) >>
  conj_tac
  >- (irule EQ_TRANS >> qexists_tac `t2.t_mem` >> conj_tac
      >- (irule (cj 2 mload_ghost_clean) >> simp[eval_operand_def]) >> simp[]) >>
  suspend "frames"
QED

Resume alias_pair_load_checks[frames]:
  qmatch_goalsub_abbrev_tac `step_prov PG g2 k sf` >>
  qabbrev_tac `gf = step_prov PG g2 k sf` >>
  qabbrev_tac `tf = step_taint k s2 sf t2` >>
  qabbrev_tac `out = update_var dst (mload (w2n A) s)
    (update_var ap P (update_var aq Q s))` >>
  `!x C. x <> dst /\ ptr_covers g2 t2 x s2 C ==>
     ptr_covers gf tf x out C` by
    (rpt gen_tac >> strip_tac >>
     `ptr_covers gf tf x (update_var dst (mload (w2n A) s2) s2) C` by
       (simp[Abbr `gf`, Abbr `tf`, Abbr `k`, Abbr `sf`] >> irule ptr_covers_step_frame >>
        simp[mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
     fs[Abbr `out`, Abbr `s2`, Abbr `s1`, ptr_covers_def,
        eval_operand_def, lookup_var_def, update_var_def, mload_def]) >>
  conj_tac >- simp[Abbr `out`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[Abbr `out`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[Abbr `out`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- suspend "alias_q" >>
  conj_tac >- suspend "alias_p" >>
  conj_tac >- suspend "live" >>
  simp[Abbr `out`, update_var_def, mload_def]
QED

Resume alias_pair_load_checks[alias_q]:
  gen_tac >> strip_tac >>
  `ptr_covers g1 t1 aq s1 C` by
    (simp[Abbr `g1`, Abbr `t1`, Abbr `i`, Abbr `s1`] >>
     irule add_zero_ptr_covers >> simp[]) >>
  `ptr_covers g2 t2 aq s2 C` by
    (simp[Abbr `g2`, Abbr `t2`, Abbr `s2`] >>
     irule ptr_covers_step_frame >>
     simp[Abbr `j`, mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  first_x_assum irule >> simp[]
QED

Resume alias_pair_load_checks[alias_p]:
  gen_tac >> strip_tac >>
  `ptr_covers g1 t1 p s1 C` by
    (simp[Abbr `g1`, Abbr `t1`, Abbr `s1`] >>
     irule ptr_covers_step_frame >>
     fs[Abbr `i`, mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `ptr_covers g2 t2 ap s2 C` by
    (simp[Abbr `g2`, Abbr `t2`, Abbr `j`, Abbr `s2`] >>
     irule add_zero_ptr_covers >> simp[]) >>
  first_x_assum irule >> simp[]
QED

Resume alias_pair_load_checks[live]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- simp[Abbr `out`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `ptr_covers g1 t1 x s1 C` by
    (simp[Abbr `g1`, Abbr `t1`, Abbr `s1`] >>
     irule ptr_covers_step_frame >>
     simp[Abbr `i`, mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `ptr_covers g2 t2 x s2 C` by
    (simp[Abbr `g2`, Abbr `t2`, Abbr `s2`] >>
     irule ptr_covers_step_frame >>
     simp[Abbr `j`, mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  first_x_assum irule >> simp[]
QED

Finalise alias_pair_load_checks

(* Both ABI offset stores and the size-cell update write clean controls. *)
Theorem mstore_clean_checks:
  ptr_covers G tn dst s 32 /\ lookup_var dst s = SOME a /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MSTORE [Var dst;value] []] s Gf tnf /\
    (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tnf.t_mem) /\
    tnf.t_mem SUBSET tn.t_mem /\
    (!x C. ptr_covers G tn x s C ==>
      ptr_covers Gf tnf x (mstore (w2n a) w s) C) /\
    (!t. run_inst_seq [mk_inst id MSTORE [Var dst;value] []] s = OK t ==>
      (!x. lookup_var x t = lookup_var x s /\
        op_taint tnf (Var x) = op_taint tn (Var x) /\
        (!C. ptr_covers G tn x s C ==> ptr_covers Gf tnf x t C)))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MSTORE [Var dst;value] []) s =
     OK (mstore (w2n a) w s)` by
    (irule step_mstore_operands >> simp[eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id MSTORE [Var dst;value] []) s` by
    (irule ptr_inst_ok_mstore >> simp[]) >>
  simp[inst_seq_ptr_def] >>
  ` (step_taint (mk_inst id MSTORE [Var dst;value] []) s
      (mstore (w2n a) w s) tn).t_mem =
      tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}` by
    (irule (cj 5 mstore_ghost_frame) >> simp[]) >>
  simp[pred_setTheory.SUBSET_DEF] >>
  conj_tac >-
    (rpt strip_tac >> irule ptr_covers_step_frame >>
     simp[mk_inst_def, mstore_def, lookup_var_def]) >>
  suspend "endpoint"
QED

Resume mstore_clean_checks[endpoint]:
  gen_tac >> strip_tac >>
  `t = mstore (w2n a) w s` by
    (qpat_x_assum `run_inst_seq _ _ = OK t` mp_tac >>
     rewrite_tac[run_inst_seq_def] >> asm_rewrite_tac[] >> simp[]) >>
  gvs[] >> gen_tac >>
  conj_tac >- simp[step_taint_other_output, mk_inst_def] >>
  rpt strip_tac >> irule ptr_covers_step_frame >>
  simp[mk_inst_def, mstore_def, lookup_var_def]
QED

Finalise mstore_clean_checks

Theorem revert_operand_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id REVERT [Var p;len] []) /\
  ptr_covers G tn p s (w2n n) /\
  eval_operand len s = SOME n /\ op_taint tn len = {} /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id REVERT [Var p;len] []) s = Abort a t ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (Abort a t)
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id REVERT [Var p;len] []) s` by
    (irule ptr_inst_ok_revert >> simp[]) >>
  irule (cj 3 gas_path_ptr_rules) >> simp[exit_result_def] >>
  rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
  qexists_tac `0` >>
  simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
       exit_result_def, ptr_safe_step_def] >>
  gvs[mk_inst_def]
QED

Theorem revert_abi_tail_checks:
  lookup_var buf s = SOME a /\ lookup_var szvar s = SOME (n2w k) /\
  ptr_covers G tn buf s capbytes /\ op_taint tn (Var szvar) = {} /\
  28 < capbytes /\ 28+(k+4) <= capbytes /\
  w2n a+28 < dimword(:256) /\ k+4 < dimword(:256) /\
  buf <> retptr /\ szvar <> retptr /\ retptr <> retlen /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ADD [Var buf;Lit 28w] [retptr];
     mk_inst (id+1) ADD [Lit 4w;Var szvar] [retlen];
     mk_inst (id+2) REVERT [Var retptr;Var retlen] []] s Gf tnf
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ _ _ [i;j;l] _ _ _` >>
  `op_taint tn (Var buf) = {}` by fs[ptr_covers_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  `step_inst_base i s = OK (update_var retptr (a+28w) s)` by
    (simp[Abbr `i`, mk_inst_def] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accfupds, combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
     simp[exec_pure2_def, eval_operand_def]) >>
  simp[Once inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ g1 t1 _ s1 _ _` >>
  `ptr_covers g1 t1 retptr s1 (k+4)` by
    (simp[Abbr `g1`, Abbr `t1`, Abbr `s1`, Abbr `i`] >>
     irule typed_copy_loop_dynamic_offset_covers >> simp[eval_operand_def] >>
     qexists_tac `capbytes` >> simp[]) >>
  `lookup_var szvar s1 = SOME (n2w k)` by
    fs[Abbr `s1`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `op_taint t1 (Var szvar) = {}` by
    (simp[Abbr `t1`, Abbr `i`, step_taint_def, set_var_taint_def,
       op_taint_def, mk_inst_def, FLOOKUP_UPDATE] >> fs[op_taint_def]) >>
  suspend "length"
QED

Resume revert_abi_tail_checks[length]:
  `ptr_inst_ok D 0 0 ctx fn g1 t1 j s1` by
    (simp[Abbr `j`] >> irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  `step_inst_base j s1 = OK (update_var retlen (n2w (k+4)) s1)` by
    (simp[Abbr `j`, mk_inst_def] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accfupds, combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
     simp[exec_pure2_def, eval_operand_def, GSYM word_add_n2w, WORD_ADD_COMM]) >>
  simp[Once inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ g2 t2 _ s2 _ _` >>
  `ptr_covers g2 t2 retptr s2 (k+4)` by
    (simp[Abbr `g2`, Abbr `t2`, Abbr `s2`] >>
     irule ptr_covers_step_frame >>
     simp[Abbr `j`, mk_inst_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `op_taint t2 (Var retlen) = {}` by
    simp[Abbr `t2`, Abbr `j`, cj 1 copy_len_binop_ghost_frame] >>
  `lookup_var retlen s2 = SOME (n2w (k+4))` by
    simp[Abbr `s2`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `ptr_inst_ok D 0 0 ctx fn g2 t2 l s2` by
    (simp[Abbr `l`] >> irule ptr_inst_ok_revert >>
     simp[eval_operand_def, w2n_n2w, LESS_MOD]) >>
  Cases_on `step_inst_base l s2` >> simp[inst_seq_ptr_def]
QED

Finalise revert_abi_tail_checks

(* The padding store precedes the unpadded payload copy.  Payload bytes need
   not be clean; only the two address/count controls do. *)
Theorem zero_pad_copy_checks:
  lookup_var dst s = SOME a /\ lookup_var lenvar s = SOME (n2w L) /\
  lookup_var rounded s = SOME (n2w R) /\
  ptr_covers G tn dst s capbytes /\ ptr_covers G tn src s (32+L) /\
  op_taint tn (Var lenvar) = {} /\ op_taint tn (Var rounded) = {} /\
  R < capbytes /\ R+32 <= capbytes /\ 32+L <= capbytes /\
  w2n a+R < dimword(:256) /\ 32+L < dimword(:256) /\
  dst <> endvar /\ src <> endvar /\ lenvar <> endvar /\
  dst <> countvar /\ src <> countvar /\ ~ctx_has_dalloca ctx ==>
  ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ADD [Var dst;Var rounded] [endvar];
     mk_inst (id+1) MSTORE [Var endvar;Lit 0w] [];
     mk_inst (id+2) ADD [Lit 32w;Var lenvar] [countvar];
     mk_inst (id+3) MCOPY [Var dst;Var src;Var countvar] []] s Gf tnf /\
    (!t. run_inst_seq
      [mk_inst id ADD [Var dst;Var rounded] [endvar];
       mk_inst (id+1) MSTORE [Var endvar;Lit 0w] [];
       mk_inst (id+2) ADD [Lit 32w;Var lenvar] [countvar];
       mk_inst (id+3) MCOPY [Var dst;Var src;Var countvar] []] s = OK t ==>
      (!x. x <> endvar /\ x <> countvar ==>
        lookup_var x t = lookup_var x s /\
        op_taint tnf (Var x) = op_taint tn (Var x) /\
        (!C. ptr_covers G tn x s C ==> ptr_covers Gf tnf x t C)))
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ _ _ code s _ _` >>
  `?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn code s Gf tnf` by
    suspend "checks" >>
  qexistsl_tac [`Gf`, `tnf`] >> simp[] >>
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
     ~MEM x i.inst_outputs) code` by
    simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  conj_tac >- (irule run_inst_seq_non_output_lookup >>
    goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (drule inst_seq_ptr_other_output_frame >>
    disch_then (qspec_then `x` mp_tac) >>
    impl_tac >- fs[EVERY_MEM] >> simp[]) >>
  rpt strip_tac >> irule (cj 2 inst_seq_ptr_live_pointer_frame) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any)
QED

Resume zero_pad_copy_checks[checks]:
  simp[Abbr `code`] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ _ _ [i;j;k;l] _ _ _` >>
  `op_taint tn (Var dst) = {}` by fs[ptr_covers_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_copy_len_binop >> simp[]) >>
  `step_inst_base i s = OK (update_var endvar (a+n2w R) s)` by
    (simp[Abbr `i`, mk_inst_def] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accfupds, combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
     simp[exec_pure2_def, eval_operand_def]) >>
  simp[Once inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ g1 t1 _ s1 _ _` >>
  `ptr_covers g1 t1 endvar s1 32` by
    (simp[Abbr `g1`, Abbr `t1`, Abbr `s1`, Abbr `i`] >>
     irule typed_copy_loop_dynamic_offset_covers >> simp[eval_operand_def] >>
     qexists_tac `capbytes` >> simp[]) >>
  `!x C. x <> endvar /\ ptr_covers G tn x s C ==>
     ptr_covers g1 t1 x s1 C` by
    (rpt strip_tac >> simp[Abbr `g1`, Abbr `t1`, Abbr `s1`] >>
     irule ptr_covers_step_frame >>
     simp[Abbr `i`, mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `ptr_covers g1 t1 dst s1 capbytes /\ ptr_covers g1 t1 src s1 (32+L)` by
    metis_tac[] >>
  `lookup_var endvar s1 = SOME (a+n2w R)` by
    simp[Abbr `s1`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  suspend "store"
QED

Resume zero_pad_copy_checks[store]:
  `ptr_inst_ok D 0 0 ctx fn g1 t1 j s1` by
    (simp[Abbr `j`] >> irule ptr_inst_ok_mstore >> simp[op_taint_def]) >>
  `step_inst_base j s1 = OK (mstore (w2n (a+n2w R)) 0w s1)` by
    (simp[Abbr `j`] >> irule step_mstore_operands >> simp[eval_operand_def]) >>
  simp[Once inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ g2 t2 _ s2 _ _` >>
  `!x C. ptr_covers g1 t1 x s1 C ==> ptr_covers g2 t2 x s2 C` by
    (rpt strip_tac >> simp[Abbr `g2`, Abbr `t2`, Abbr `s2`] >>
     irule ptr_covers_step_frame >>
     simp[Abbr `j`, mk_inst_def, mstore_def, lookup_var_def]) >>
  `ptr_covers g2 t2 dst s2 capbytes /\ ptr_covers g2 t2 src s2 (32+L)` by
    metis_tac[] >>
  `lookup_var lenvar s2 = SOME (n2w L)` by
    fs[Abbr `s2`, Abbr `s1`, mstore_def, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE] >>
  `op_taint t1 (Var lenvar) = {}` by
    (simp[Abbr `t1`, Abbr `i`, step_taint_def, set_var_taint_def,
       op_taint_def, mk_inst_def, FLOOKUP_UPDATE] >> fs[op_taint_def]) >>
  `t2.t_var = t1.t_var` by
    (simp[Abbr `t2`, Abbr `j`] >>
     irule (cj 2 mstore_ghost_frame) >> simp[eval_operand_def, op_taint_def]) >>
  `op_taint t2 (Var lenvar) = {}` by fs[op_taint_def] >>
  suspend "copy"
QED

Resume zero_pad_copy_checks[copy]:
  qpat_x_assum `!x C. _` kall_tac >>
  qpat_x_assum `!x C. _` kall_tac >>
  `ptr_inst_ok D 0 0 ctx fn g2 t2 k s2` by
    (simp[Abbr `k`] >> irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  `step_inst_base k s2 = OK (update_var countvar (n2w (32+L)) s2)` by
    (simp[Abbr `k`, mk_inst_def] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accfupds, combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
     simp[exec_pure2_def, eval_operand_def, GSYM word_add_n2w, WORD_ADD_COMM]) >>
  simp[Once inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ g3 t3 _ s3 _ _` >>
  `!x C. x <> countvar /\ ptr_covers g2 t2 x s2 C ==>
     ptr_covers g3 t3 x s3 C` by
    (rpt strip_tac >> simp[Abbr `g3`, Abbr `t3`, Abbr `s3`] >>
     irule ptr_covers_step_frame >>
     simp[Abbr `k`, mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `ptr_covers g3 t3 dst s3 capbytes /\ ptr_covers g3 t3 src s3 (32+L)` by
    metis_tac[] >>
  `ptr_covers g3 t3 dst s3 (32+L)` by
    (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `op_taint t3 (Var countvar) = {}` by
    simp[Abbr `t3`, Abbr `k`, cj 1 copy_len_binop_ghost_frame] >>
  `lookup_var countvar s3 = SOME (n2w (32+L))` by
    simp[Abbr `s3`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `ptr_inst_ok D 0 0 ctx fn g3 t3 l s3` by
    (simp[Abbr `l`] >> irule ptr_inst_ok_mcopy_operand >>
     simp[eval_operand_def, w2n_n2w, LESS_MOD] >> fs[ADD_COMM]) >>
  Cases_on `step_inst_base l s3` >> simp[inst_seq_ptr_def]
QED

Finalise zero_pad_copy_checks

Theorem round_ceil32_checks:
  lookup_var lenvar s = SOME (n2w L) /\
  op_taint tn (Var lenvar) = {} /\ L+63 < dimword(:256) /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ADD [Var lenvar;Lit 31w] [tmp];
       mk_inst (id+1) AND [Var tmp;
         Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w]
         [out]] s Gf tnf /\
    op_taint tnf (Var out) = {} /\ tnf.t_mem = tn.t_mem /\
    (!t. run_inst_seq
      [mk_inst id ADD [Var lenvar;Lit 31w] [tmp];
       mk_inst (id+1) AND [Var tmp;
         Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w]
         [out]] s = OK t ==>
      lookup_var out t = SOME (n2w (contractABI$ceil32 L)) /\
      (!a. mload a t = mload a s) /\
      (!x. x <> tmp /\ x <> out ==>
        lookup_var x t = lookup_var x s /\
        op_taint tnf (Var x) = op_taint tn (Var x) /\
        (!C. ptr_covers G tn x s C ==> ptr_covers Gf tnf x t C)))
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ _ _ [i;j] _ _ _` >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  `step_inst_base i s = OK (update_var tmp (n2w L+31w) s)` by
    (simp[Abbr `i`, mk_inst_def] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accfupds, combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
     simp[exec_pure2_def, eval_operand_def]) >>
  simp[Once inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ g1 t1 _ s1 _ _` >>
  `op_taint t1 (Var tmp) = {} /\ t1.t_mem = tn.t_mem` by
    simp[Abbr `t1`, Abbr `i`, copy_len_binop_ghost_frame] >>
  `lookup_var tmp s1 = SOME (n2w L+31w)` by
    simp[Abbr `s1`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `ptr_inst_ok D 0 0 ctx fn g1 t1 j s1` by
    (simp[Abbr `j`] >> irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  `(n2w L:bytes32)+31w &&
      0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w =
      n2w (contractABI$ceil32 L)` by
    (once_rewrite_tac[WORD_AND_COMM] >> rewrite_tac[Once WORD_ADD_COMM] >>
     irule abi_encoder_round_ceil32 >> simp[]) >>
  `step_inst_base j s1 = OK (update_var out (n2w (contractABI$ceil32 L)) s1)` by
    (simp[Abbr `j`, mk_inst_def] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accfupds, combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
     simp[exec_pure2_def, eval_operand_def]) >>
  simp[inst_seq_ptr_def, Abbr `j`, copy_len_binop_ghost_frame] >>
  suspend "endpoint"
QED

Resume round_ceil32_checks[endpoint]:
  gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq [i;j] s` >>
  `step_inst_base j (update_var tmp (n2w L+31w) s) =
     OK (update_var out (n2w (contractABI$ceil32 L))
       (update_var tmp (n2w L+31w) s))` by
    (simp[Abbr `j`, mk_inst_def] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accfupds, combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
     simp[exec_pure2_def, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE]) >>
  qpat_x_assum `run_inst_seq _ _ = OK t` mp_tac >>
  fs[Abbr `j`, run_inst_seq_def] >>
  disch_then (SUBST1_TAC o SYM) >>
  conj_tac >- simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[mload_def, update_var_def] >>
  rpt gen_tac >> strip_tac >>
  conj_tac >- simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[Abbr `t1`, Abbr `i`, copy_len_binop_ghost_frame] >>
  suspend "coverage"
QED

Resume round_ceil32_checks[coverage]:
  rpt strip_tac >>
  `ptr_covers g1 t1 x s1 C` by
    (simp[Abbr `g1`, Abbr `t1`, Abbr `s1`] >>
     irule ptr_covers_step_frame >>
     simp[Abbr `i`, mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  qmatch_goalsub_abbrev_tac `step_prov PG g1 j sf` >>
  `ptr_covers (step_prov PG g1 j sf) (step_taint j s1 sf t1) x sf C` by
    (simp[Abbr `sf`] >> irule ptr_covers_step_frame >>
     simp[Abbr `j`, mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  fs[Abbr `sf`, Abbr `s1`, ptr_covers_def, eval_operand_def,
     lookup_var_def, update_var_def]
QED

Finalise round_ceil32_checks

Theorem store_load_clean_checks:
  ptr_covers G tn cell s 32 /\ lookup_var cell s = SOME a /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MSTORE [Var cell;value] [];
       mk_inst (id+1) MLOAD [Var cell] [dst]] s Gf tnf /\
    op_taint tnf (Var dst) = {} /\
    (!t. run_inst_seq
      [mk_inst id MSTORE [Var cell;value] [];
       mk_inst (id+1) MLOAD [Var cell] [dst]] s = OK t ==>
      lookup_var dst t = SOME w /\
      (!x. x <> dst ==>
        lookup_var x t = lookup_var x s /\
        op_taint tnf (Var x) = op_taint tn (Var x) /\
        (!C. ptr_covers G tn x s C ==> ptr_covers Gf tnf x t C)))
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ _ _ [i;j] _ _ _` >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_mstore >> simp[]) >>
  `step_inst_base i s = OK (mstore (w2n a) w s)` by
    (simp[Abbr `i`] >> irule step_mstore_operands >> simp[eval_operand_def]) >>
  simp[Once inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ g1 t1 _ s1 _ _` >>
  `ptr_covers g1 t1 cell s1 32` by
    (simp[Abbr `g1`, Abbr `t1`, Abbr `s1`] >>
     irule ptr_covers_step_frame >>
     simp[Abbr `i`, mk_inst_def, mstore_def, lookup_var_def]) >>
  `lookup_var cell s1 = SOME a` by
    fs[Abbr `s1`, mstore_def, lookup_var_def] >>
  `t1.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}` by
    (simp[Abbr `t1`, Abbr `i`] >> irule (cj 5 mstore_ghost_frame) >> simp[]) >>
  `!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN t1.t_mem` by simp[] >>
  `ptr_inst_ok D 0 0 ctx fn g1 t1 j s1` by
    (simp[Abbr `j`] >> irule ptr_inst_ok_mload >> simp[]) >>
  `step_inst_base j s1 = OK (update_var dst (mload (w2n a) s1) s1)` by
    (simp[Abbr `j`, mk_inst_def] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accfupds, combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
     simp[exec_read1_def, eval_operand_def]) >>
  simp[inst_seq_ptr_def, Abbr `j`] >>
  conj_tac >- (irule (cj 1 mload_ghost_clean) >> simp[eval_operand_def]) >>
  suspend "endpoint"
QED

Resume store_load_clean_checks[endpoint]:
  gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq [i;j] s` >>
  `lookup_var cell (mstore (w2n a) w s) = SOME a` by
    simp[mstore_def, lookup_var_def] >>
  `step_inst_base j (mstore (w2n a) w s) =
     OK (update_var dst w (mstore (w2n a) w s))` by
    (simp[Abbr `j`, mk_inst_def] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accfupds, combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
     simp[exec_read1_def, eval_operand_def, mload_mstore_same]) >>
  `t = update_var dst w (mstore (w2n a) w s)` by
    (qpat_x_assum `run_inst_seq _ _ = OK t` mp_tac >>
     simp[run_inst_seq_def] >> metis_tac[]) >>
  gvs[] >> conj_tac >- simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  gen_tac >> strip_tac >>
  conj_tac >- simp[lookup_var_def, update_var_def, mstore_def, FLOOKUP_UPDATE] >>
  conj_tac >- suspend "taint" >>
  suspend "coverage"
QED

Resume store_load_clean_checks[taint]:
  `t1.t_var = tn.t_var` by
    (simp[Abbr `t1`, Abbr `i`] >>
     irule (cj 2 mstore_ghost_frame) >> simp[eval_operand_def]) >>
  simp[Abbr `j`, step_taint_def, mk_inst_def, set_var_taint_def,
     op_taint_def, FLOOKUP_UPDATE]
QED

Resume store_load_clean_checks[coverage]:
  rpt strip_tac >>
  `ptr_covers g1 t1 x s1 C` by
    (simp[Abbr `g1`, Abbr `t1`, Abbr `s1`] >>
     irule ptr_covers_step_frame >>
     simp[Abbr `i`, mk_inst_def, lookup_var_def, mstore_def]) >>
  qmatch_goalsub_abbrev_tac `step_prov PG g1 j sf` >>
  `ptr_covers (step_prov PG g1 j sf) (step_taint j s1 sf t1) x sf C` by
    (simp[Abbr `sf`] >> irule ptr_covers_step_frame >>
     simp[Abbr `j`, mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `mload (w2n a) s1 = w` by
    (qsuff_tac `mload (w2n a) s1 = mload (w2n a) (mstore (w2n a) w s)`
     >- simp[mload_mstore_same] >> simp[Abbr `s1`, mload_def]) >>
  qpat_x_assum `ptr_covers _ _ x sf C` mp_tac >>
  simp[Abbr `sf`, Abbr `s1`, ptr_covers_def, eval_operand_def,
     lookup_var_def, update_var_def]
QED

Finalise store_load_clean_checks

(* Successful-run boundary for the two numeric ADD phases of the ABI suffix. *)
Theorem clean_add_checks:
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ADD [left;right] [out]] s Gf tnf /\
    op_taint tnf (Var out) = {} /\
    (!t. run_inst_seq [mk_inst id ADD [left;right] [out]] s = OK t ==>
      lookup_var out t = SOME (a+b) /\
      (!x. x <> out ==>
        lookup_var x t = lookup_var x s /\
        op_taint tnf (Var x) = op_taint tn (Var x) /\
        (!C. ptr_covers G tn x s C ==> ptr_covers Gf tnf x t C)))
Proof
  strip_tac >>
  qabbrev_tac `i = mk_inst id ADD [left;right] [out]` >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_copy_len_binop >> simp[]) >>
  `step_inst_base i s = OK (update_var out (a+b) s)` by
    (simp[Abbr `i`, mk_inst_def] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accfupds, combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
     simp[exec_pure2_def]) >>
  simp[inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `op_taint tf (Var out)` >>
  conj_tac >- simp[Abbr `tf`, Abbr `i`, copy_len_binop_ghost_frame] >>
  gen_tac >> strip_tac >>
  `t = update_var out (a+b) s` by
    (qpat_x_assum `run_inst_seq _ _ = OK t` mp_tac >>
     rewrite_tac[run_inst_seq_def] >> asm_rewrite_tac[] >> simp[]) >>
  gvs[] >>
  conj_tac >- simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  gen_tac >> strip_tac >>
  conj_tac >- simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[Abbr `tf`, Abbr `i`, copy_len_binop_ghost_frame] >>
  rpt strip_tac >> simp[Abbr `tf`] >>
  irule ptr_covers_step_frame >>
  simp[Abbr `i`, lookup_var_def, update_var_def, FLOOKUP_UPDATE, mk_inst_def]
QED
