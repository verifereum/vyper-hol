(* Pointer checks for the straight-line Concat append arms. *)
Theory bodyPtrBytestringBuiltinsConcatChecks
Ancestors
  bodyPtrBytestringBuiltinsConcatPrefix assignTuplePtrLocalBytesCopy
  exprSimConcatStep concatMemory wordLoadStorePtr exprPtrUnwrapOffsetSegment
  bodyPtrIfExpBytesFrame bodyPtrIfExpBytesCounted bodyPtrIfExpStoragePhases
  context compileEnv emitHelper emitHelperProps exprLoweringProps venomInst venomState
  venomExecSemantics ptrDiscipline fragGasSeqPtr finite_map words pred_set list

Theorem concat_fixed_seq_ptr:
  (do offset_op <- emit_op MLOAD [Var oq];
      dst <- emit_op ADD [Var dp; offset_op];
      emit_void MSTORE [dst; x];
      new_offset <- emit_op ADD [offset_op; Lit (n2w m)];
      emit_void MSTORE [Var oq; new_offset]
   od) sx = ((), sb) /\
  lookup_var dp t = SOME (n2w (B+32)) /\ lookup_var oq t = SOME ow /\
  eval_operand x t = SOME vw /\
  not_fresh_at sx dp /\ not_fresh_at sx oq /\
  (!z. x = Var z ==> not_fresh_at sx z) /\
  ptr_covers G tn dp t (bsz-32) /\ ptr_covers G tn oq t 32 /\
  op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n ow) t = n2w k /\
  B+bsz < dimword (:256) /\ 32+k+32 <= bsz ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sx sb) t Gf tnf /\
    tnf.t_mem SUBSET tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!z. not_fresh_at sx z ==>
      FLOOKUP Gf z = FLOOKUP G z /\ op_taint tnf (Var z) = op_taint tn (Var z)) /\
    (!i. B+32+k <= i /\ i < B+32+k+32 ==> i NOTIN tnf.t_mem) /\
    (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >> drule concat_fixed_shape >> disch_then SUBST1_TAC >>
  qabbrev_tac `r0 = STRING #"%" (toString sx.cs_next_var)` >>
  qabbrev_tac `r1 = STRING #"%" (toString (sx.cs_next_var+1))` >>
  qabbrev_tac `r2 = STRING #"%" (toString (sx.cs_next_var+2))` >>
  `r0 <> r1 /\ r0 <> r2 /\ r1 <> r2` by
    simp[Abbr `r0`, Abbr `r1`, Abbr `r2`] >>
  `!z. not_fresh_at sx z ==> z <> r0 /\ z <> r1 /\ z <> r2` by
    (simp[not_fresh_at_def, Abbr `r0`, Abbr `r1`, Abbr `r2`] >>
     rpt strip_tac >> metis_tac[arithmeticTheory.LESS_EQ_REFL,
       arithmeticTheory.LESS_EQ_ADD]) >>
  drule_all assignTuplePtrLocalBytesCopyTheory.mload_clean_seq_ptr >>
  disch_then (qspecl_then [`D`,`func`,`PG`,`sx.cs_next_id`,`r0`] strip_assume_tac) >>
  suspend "offset"
QED

Resume concat_fixed_seq_ptr[offset]:
  qabbrev_tac `s0 = t' with vs_inst_idx := SUC t.vs_inst_idx` >>
  `ptr_covers G' tn' dp s0 (bsz-32)` by
    (irule annAssignPtrBytestringTheory.annassign_ptr_covers_frame_ptr >>
     qexistsl_tac [`G`,`t`,`tn`] >>
     gvs[Abbr `s0`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `lookup_var dp s0 = SOME (n2w (B+32)) /\
   eval_operand (Var r0) s0 = SOME (n2w k)` by
    (gvs[Abbr `s0`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `k < bsz-32 /\ k+32 <= bsz-32 /\
   w2n (n2w (B+32):256 word)+k < dimword (:256)` by
    (simp[wordsTheory.w2n_n2w] >>
     `B+32 < dimword (:256)` by decide_tac >>
     simp[arithmeticTheory.LESS_MOD] >> decide_tac) >>
  `dp <> r1` by metis_tac[] >>
  `allocas_from 0 s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0)` by
    simp[allocas_from_def] >>
  drule_all copy_offset_segment >>
  disch_then (qspecl_then [`sx.cs_next_id+1`,`func`,`PG`,`D`] strip_assume_tac) >>
  suspend "store"
QED

Resume concat_fixed_seq_ptr[store]:
  qabbrev_tac `s1 = t'' with vs_inst_idx := SUC s0.vs_inst_idx` >>
  `ptr_covers Gf tnf r1 s1 32` by
    gvs[Abbr `s1`, bodyPtrDefsTheory.ptr_covers_def, eval_operand_def, lookup_var_def] >>
  `eval_operand (Var r1) s1 = SOME (n2w (B+32)+n2w k) /\
   eval_operand x s1 = SOME vw` by
    (Cases_on `x` >>
     gvs[Abbr `s1`, Abbr `s0`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `op_taint tnf x = {}` by
    (Cases_on `x` >> gvs[op_taint_def] >> metis_tac[]) >>
  drule_all ifexp_copy_store_phase >>
  disch_then (qspecl_then [`sx.cs_next_id+2`,`func`,`PG`,`D`] strip_assume_tac) >>
  suspend "increment"
QED

Resume concat_fixed_seq_ptr[increment]:
  rename1 `run_inst_seq [mk_inst (sx.cs_next_id+2) MSTORE [Var r1;x] []] s1 = OK u` >>
  qabbrev_tac `s2 = u with vs_inst_idx := SUC s1.vs_inst_idx` >>
  `eval_operand (Var r0) s2 = SOME (n2w k)` by
    gvs[Abbr `s2`, Abbr `s1`, eval_operand_def, lookup_var_def,
        mstore_def, write_memory_with_expansion_def, write_memory_def,
        update_var_def, FLOOKUP_UPDATE] >>
  `op_taint tn'' (Var r0) = {} /\ op_taint tn'' (Lit (n2w m)) = {}` by
    gvs[op_taint_def] >>
  mp_tac (Q.SPECL [`D`,`ctx`,`func`,`PG`,`Gf`,`tn''`,`s2`,
    `sx.cs_next_id+3`,`ADD`,`Var r0`,`Lit (n2w m)`,`r2`,
    `word_add`,`n2w k`,`n2w m`]
    assignTuplePtrLocalBytesCopyTheory.copy_len_binop_seq_ptr) >>
  simp[eval_operand_def] >> strip_tac >>
  suspend "last_store"
QED

Resume concat_fixed_seq_ptr[last_store]:
  rename1 `inst_seq_ptr D 0 ctx func PG Gf tn''
    [mk_inst (sx.cs_next_id+3) ADD [Var r0;Lit (n2w m)] [r2]] s2 H th` >>
  qabbrev_tac `s3 = update_var r2 (n2w k+n2w m) s2 with vs_inst_idx := SUC s2.vs_inst_idx` >>
  `lookup_var oq s3 = lookup_var oq t` by
    (gvs[Abbr `s3`, Abbr `s2`, Abbr `s1`, Abbr `s0`,
      lookup_var_def, update_var_def, mstore_def,
      write_memory_with_expansion_def, write_memory_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `ptr_covers H th oq s3 32` by
    (irule annAssignPtrBytestringTheory.annassign_ptr_covers_frame_ptr >>
     qexistsl_tac [`G`,`t`,`tn`] >> simp[] >>
     gvs[op_taint_def] >> metis_tac[]) >>
  `eval_operand (Var oq) s3 = SOME ow /\
   eval_operand (Var r2) s3 = SOME (n2w k+n2w m)` by
    simp[eval_operand_def, Abbr `s3`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  drule_all ifexp_copy_store_phase >>
  disch_then (qspecl_then [`sx.cs_next_id+4`,`func`,`PG`,`D`] strip_assume_tac) >>
  suspend "assemble"
QED

Resume concat_fixed_seq_ptr[assemble]:
  rename1 `inst_seq_ptr D 0 ctx func PG H th
    [mk_inst (sx.cs_next_id+4) MSTORE [Var oq;Var r2] []] s3 H tf` >>
  qexistsl_tac [`H`,`tf`] >> conj_tac
  >- (irule (SRULE [APPEND] (Q.ISPEC `[mk_inst sx.cs_next_id MLOAD [Var oq] [r0]]`
        assignTuplePtrLocalBytesCopyTheory.inst_seq_ptr_append_run)) >>
      pure_rewrite_tac[is_terminator_def, boolTheory.NOT_CLAUSES, boolTheory.AND_CLAUSES] >>
      qexistsl_tac [`G'`,`t'`,`tn'`] >>
      `t' with vs_inst_idx := t.vs_inst_idx+1 = s0` by simp[Abbr `s0`, arithmeticTheory.ADD1] >>
      pure_asm_rewrite_tac [] >> rewrite_tac [] >>
      irule (SRULE [APPEND] (Q.ISPEC `[mk_inst (sx.cs_next_id+1) ADD [Var dp;Var r0] [r1]]`
        assignTuplePtrLocalBytesCopyTheory.inst_seq_ptr_append_run)) >>
      pure_rewrite_tac[is_terminator_def, boolTheory.NOT_CLAUSES, boolTheory.AND_CLAUSES] >>
      qexistsl_tac [`Gf`,`t''`,`tnf`] >>
      `t'' with vs_inst_idx := s0.vs_inst_idx+1 = s1` by simp[Abbr `s1`, arithmeticTheory.ADD1] >>
      pure_asm_rewrite_tac [] >> rewrite_tac [] >>
      irule (SRULE [APPEND] (Q.ISPEC `[mk_inst (sx.cs_next_id+2) MSTORE [Var r1;x] []]`
        assignTuplePtrLocalBytesCopyTheory.inst_seq_ptr_append_run)) >>
      pure_rewrite_tac[is_terminator_def, boolTheory.NOT_CLAUSES, boolTheory.AND_CLAUSES] >>
      qexistsl_tac [`Gf`,`u`,`tn''`] >>
      `u with vs_inst_idx := s1.vs_inst_idx+1 = s2` by simp[Abbr `s2`, arithmeticTheory.ADD1] >>
      pure_asm_rewrite_tac [] >> rewrite_tac [] >>
      irule (SRULE [APPEND] (Q.ISPEC `[mk_inst (sx.cs_next_id+3) ADD [Var r0;Lit (n2w m)] [r2]]`
        assignTuplePtrLocalBytesCopyTheory.inst_seq_ptr_append_run)) >>
      pure_rewrite_tac[is_terminator_def, boolTheory.NOT_CLAUSES, boolTheory.AND_CLAUSES] >>
      qexistsl_tac [`H`,`update_var r2 (n2w k+n2w m) s2`,`th`] >>
      `update_var r2 (n2w k+n2w m) s2 with vs_inst_idx := s2.vs_inst_idx+1 = s3` by
        simp[Abbr `s3`, arithmeticTheory.ADD1] >>
      pure_asm_rewrite_tac [] >> rewrite_tac []) >>
  suspend "outputs"
QED

Resume concat_fixed_seq_ptr[outputs]:
  `w2n (n2w (B+32)+n2w k :256 word) = B+32+k` by
    (pure_rewrite_tac[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w] >>
     irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  conj_tac >- (gvs[] >> ASM_SET_TAC []) >>
  conj_tac >- gvs[] >> conj_tac >- gvs[] >> conj_tac >- gvs[] >>
  conj_tac
  >- (rpt strip_tac >> gvs[op_taint_def] >> metis_tac[]) >>
  gvs[] >> conj_tac >> rpt strip_tac >> gvs[]
QED

Finalise concat_fixed_seq_ptr

(* Endpoint coverage is intentional: off may equal capacity when n is zero. *)
Theorem concat_offset_seq_ptr:
  lookup_var root s = SOME a /\ ptr_covers G tn root s capacity /\
  eval_operand delta s = SOME (n2w off) /\ op_taint tn delta = {} /\
  off+n <= capacity /\ w2n a+off < dimword (:256) /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf t.
    run_inst_seq [mk_inst id ADD [Var root;delta] [out]] s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ADD [Var root;delta] [out]] s Gf tnf /\
    t = update_var out (a+n2w off) s /\ ptr_covers Gf tnf out t n /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. p <> out ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `op_taint tn (Var root) = {}` by fs[bodyPtrDefsTheory.ptr_covers_def] >>
  mp_tac (Q.SPECL [`D`,`ctx`,`fn`,`PG`,`G`,`tn`,`s`,`id`,`ADD`,
    `Var root`,`delta`,`out`,`word_add`,`a`,`n2w off`]
    assignTuplePtrLocalBytesCopyTheory.copy_len_binop_seq_ptr) >>
  simp[eval_operand_def] >> strip_tac >>
  qexistsl_tac [`G'`,`tn'`] >> simp[] >>
  `step_inst_base (mk_inst id ADD [Var root;delta] [out]) s =
    OK (update_var out (a+n2w off) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[inst_seq_ptr_def] >> strip_tac >>
  irule (SRULE [] bodyPtrBytestringBuiltinsAllocationTheory.pointer_offset_covers) >>
  metis_tac[]
QED
