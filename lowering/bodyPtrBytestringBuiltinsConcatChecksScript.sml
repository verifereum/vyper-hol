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

Theorem concat_bytes_seq_ptr:
  (do arg_len <- emit_op MLOAD [Var src];
      arg_data <- emit_op ADD [Var src; Lit 32w];
      offset_op <- emit_op MLOAD [Var oq];
      dst <- emit_op ADD [Var dp; offset_op];
      emit_void MCOPY [dst; arg_data; arg_len];
      new_offset <- emit_op ADD [offset_op; arg_len];
      emit_void MSTORE [Var oq; new_offset]
   od) sx = ((), sb) /\
  lookup_var src t = SOME sw /\
  lookup_var dp t = SOME (n2w (B+32)) /\ lookup_var oq t = SOME ow /\
  not_fresh_at sx src /\ not_fresh_at sx dp /\ not_fresh_at sx oq /\
  ptr_covers G tn src t (32+N) /\
  ptr_covers G tn dp t (bsz-32) /\ ptr_covers G tn oq t 32 /\
  (!i. w2n sw <= i /\ i < w2n sw+32+N ==> i NOTIN tn.t_mem) /\
  mload (w2n sw) t = n2w N /\
  N < dimword (:256) /\ w2n sw+32 < dimword (:256) /\
  (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n ow) t = n2w k /\
  B+bsz < dimword (:256) /\ 32+k+N <= bsz /\ ~ctx_has_dalloca ctx ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sx sb) t Gf tnf /\
    tnf.t_mem SUBSET tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!z. not_fresh_at sx z ==>
      FLOOKUP Gf z = FLOOKUP G z /\ op_taint tnf (Var z) = op_taint tn (Var z)) /\
    (!i. B+32+k <= i /\ i < B+32+k+N ==> i NOTIN tnf.t_mem) /\
    (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >> drule concat_bytes_shape >> disch_then SUBST1_TAC >>
  qabbrev_tac `r0 = STRING #"%" (toString sx.cs_next_var)` >>
  qabbrev_tac `r1 = STRING #"%" (toString (sx.cs_next_var+1))` >>
  qabbrev_tac `r2 = STRING #"%" (toString (sx.cs_next_var+2))` >>
  qabbrev_tac `r3 = STRING #"%" (toString (sx.cs_next_var+3))` >>
  qabbrev_tac `r4 = STRING #"%" (toString (sx.cs_next_var+4))` >>
  `r0 <> r1 /\ r0 <> r2 /\ r0 <> r3 /\ r0 <> r4 /\
   r1 <> r2 /\ r1 <> r3 /\ r1 <> r4 /\ r2 <> r3 /\ r2 <> r4 /\ r3 <> r4` by
    simp[Abbr `r0`, Abbr `r1`, Abbr `r2`, Abbr `r3`, Abbr `r4`] >>
  `!z. not_fresh_at sx z ==> z <> r0 /\ z <> r1 /\ z <> r2 /\ z <> r3 /\ z <> r4` by
    (simp[not_fresh_at_def, Abbr `r0`, Abbr `r1`, Abbr `r2`, Abbr `r3`, Abbr `r4`] >>
     rpt strip_tac >> metis_tac[arithmeticTheory.LESS_EQ_REFL,
       arithmeticTheory.LESS_EQ_ADD]) >>
  `ptr_covers G tn src t 32` by
    (gvs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD, arithmeticTheory.LESS_EQ_TRANS]) >>
  `!i. w2n sw <= i /\ i < w2n sw+32 ==> i NOTIN tn.t_mem` by
    (rpt strip_tac >> qpat_x_assum `!i. w2n sw <= i /\ i < w2n sw+32+N ==> _` drule >> simp[]) >>
  drule_all assignTuplePtrLocalBytesCopyTheory.mload_clean_seq_ptr >>
  disch_then (qspecl_then [`D`,`func`,`PG`,`sx.cs_next_id`,`r0`] strip_assume_tac) >>
  suspend "source_offset"
QED

Resume concat_bytes_seq_ptr[source_offset]:
  qabbrev_tac `s0 = t' with vs_inst_idx := SUC t.vs_inst_idx` >>
  `ptr_covers G' tn' src s0 (32+N)` by
    (irule annAssignPtrBytestringTheory.annassign_ptr_covers_frame_ptr >>
     qexistsl_tac [`G`,`t`,`tn`] >>
     gvs[Abbr `s0`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `lookup_var src s0 = SOME sw` by
    (gvs[Abbr `s0`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `eval_operand (Lit 32w) s0 = SOME (n2w 32) /\ op_taint tn' (Lit 32w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  `32+N <= 32+N` by simp[] >>
  drule_all concat_offset_seq_ptr >>
  disch_then (qspecl_then [`r1`,`sx.cs_next_id+1`,`func`,`PG`,`D`] strip_assume_tac) >>
  suspend "offset_load"
QED

Resume concat_bytes_seq_ptr[offset_load]:
  qabbrev_tac `s1 = t'' with vs_inst_idx := SUC s0.vs_inst_idx` >>
  `ptr_covers Gf tnf oq s1 32` by
    (irule annAssignPtrBytestringTheory.annassign_ptr_covers_frame_ptr >>
     qexistsl_tac [`G`,`t`,`tn`] >>
     gvs[Abbr `s1`, Abbr `s0`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `lookup_var oq s1 = SOME ow` by
    (gvs[Abbr `s1`, Abbr `s0`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tnf.t_mem` by gvs[] >>
  drule_all assignTuplePtrLocalBytesCopyTheory.mload_clean_seq_ptr >>
  disch_then (qspecl_then [`D`,`func`,`PG`,`sx.cs_next_id+2`,`r2`] strip_assume_tac) >>
  suspend "dest_offset"
QED

Resume concat_bytes_seq_ptr[dest_offset]:
  qabbrev_tac `s2 = t''' with vs_inst_idx := SUC s1.vs_inst_idx` >>
  `ptr_covers G'' tn'' dp s2 (bsz-32)` by
    (irule annAssignPtrBytestringTheory.annassign_ptr_covers_frame_ptr >>
     qexistsl_tac [`G`,`t`,`tn`] >>
     gvs[Abbr `s2`, Abbr `s1`, Abbr `s0`, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `lookup_var dp s2 = SOME (n2w (B+32)) /\
   eval_operand (Var r2) s2 = SOME (n2w k)` by
    (gvs[Abbr `s2`, Abbr `s1`, Abbr `s0`, eval_operand_def,
         lookup_var_def, update_var_def, FLOOKUP_UPDATE, mload_def] >> metis_tac[]) >>
  `k+N <= bsz-32 /\ w2n (n2w (B+32):256 word)+k < dimword (:256)` by
    (`B+32 < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac) >>
  drule_all concat_offset_seq_ptr >>
  disch_then (qspecl_then [`r3`,`sx.cs_next_id+3`,`func`,`PG`,`D`] strip_assume_tac) >>
  suspend "copy"
QED

Resume concat_bytes_seq_ptr[copy]:
  qabbrev_tac `s3 = t'''' with vs_inst_idx := SUC s2.vs_inst_idx` >>
  `ptr_covers Gf' tnf' r3 s3 N` by simp[Abbr `s3`] >>
  `ptr_covers Gf' tnf' r1 s3 N` by
    (irule annAssignPtrBytestringTheory.annassign_ptr_covers_frame_ptr >>
     qexistsl_tac [`Gf`,`t''`,`tnf`] >>
     gvs[Abbr `s3`, Abbr `s2`, Abbr `s1`, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `lookup_var r1 s3 = SOME (sw+32w) /\
   lookup_var r3 s3 = SOME (n2w (B+32)+n2w k) /\
   eval_operand (Var r0) s3 = SOME (n2w N) /\
   op_taint tnf' (Var r0) = {}` by
    (gvs[Abbr `s3`, Abbr `s2`, Abbr `s1`, Abbr `s0`, eval_operand_def,
         lookup_var_def, update_var_def, FLOOKUP_UPDATE, mload_def] >> metis_tac[]) >>
  `ptr_covers Gf' tnf' r3 s3 (w2n (n2w N:256 word)) /\
   ptr_covers Gf' tnf' r1 s3 (w2n (n2w N:256 word))` by
    simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  suspend "copy_certificate"
QED


Resume concat_bytes_seq_ptr[copy_certificate]:
  subgoal `inst_seq_ptr D 0 ctx func PG Gf' tnf'
    [mk_inst (sx.cs_next_id+4) MCOPY [Var r3;Var r1;Var r0] []] s3 Gf'
    (step_taint (mk_inst (sx.cs_next_id+4) MCOPY [Var r3;Var r1;Var r0] []) s3
      (mcopy (w2n (n2w (B+32)+n2w k:256 word)) (w2n (sw+32w:256 word))
        (w2n (n2w N:256 word)) s3) tnf')`
  >- (match_mp_tac bodyPtrIfExpBytesCountedTheory.mcopy_operand_seq_ptr >> simp[]) >>
  suspend "copy_frame"
QED

Resume concat_bytes_seq_ptr[copy_frame]:
  qabbrev_tac `u = mcopy (w2n (n2w (B+32)+n2w k:256 word))
    (w2n (sw+32w:256 word)) (w2n (n2w N:256 word)) s3` >>
  qabbrev_tac `tc = step_taint (mk_inst (sx.cs_next_id+4) MCOPY [Var r3;Var r1;Var r0] []) s3 u tnf'` >>
  subgoal `tc.t_var = tnf'.t_var`
  >- (unabbrev_all_tac >> match_mp_tac (cj 2 typedCopyPtrTheory.mcopy_operand_ghost_frame) >>
      simp[eval_operand_def]) >>
  subgoal `tc.t_stor = tnf'.t_stor`
  >- (qunabbrev_tac `tc` >> qunabbrev_tac `u` >>
      match_mp_tac (cj 3 typedCopyPtrTheory.mcopy_operand_ghost_frame) >> simp[eval_operand_def]) >>
  subgoal `tc.t_trans = tnf'.t_trans`
  >- (qunabbrev_tac `tc` >> qunabbrev_tac `u` >>
      match_mp_tac (cj 4 typedCopyPtrTheory.mcopy_operand_ghost_frame) >> simp[eval_operand_def]) >>
  suspend "copy_memory"
QED

Resume concat_bytes_seq_ptr[copy_memory]:
  `tc.t_imm = tnf'.t_imm` by
    simp[Abbr `tc`, exprPtrUnwrapCopyEdgesTheory.copy_mk_immutable_taint] >>
  subgoal `tc.t_mem =
    (tnf'.t_mem DIFF {i | w2n (n2w (B+32)+n2w k:256 word) <= i /\
      i < w2n (n2w (B+32)+n2w k:256 word)+w2n (n2w N:256 word)}) UNION
    {w2n (n2w (B+32)+n2w k:256 word)+i |
      i < w2n (n2w N:256 word) /\ w2n (sw+32w:256 word)+i IN tnf'.t_mem}`
  >- (qunabbrev_tac `tc` >> qunabbrev_tac `u` >>
      match_mp_tac (cj 5 typedCopyPtrTheory.mcopy_operand_ghost_frame) >> simp[eval_operand_def]) >>
  `run_inst_seq [mk_inst (sx.cs_next_id+4) MCOPY [Var r3;Var r1;Var r0] []] s3 = OK u` by
    simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def, Abbr `u`] >>
  `w2n (sw+32w) = w2n sw+32 /\
   w2n (n2w (B+32)+n2w k:256 word) = B+32+k` by
    (conj_tac
     >- (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> simp[]) >>
     pure_rewrite_tac[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w] >>
     irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  `!i. i < N ==> w2n sw+32+i NOTIN tn.t_mem` by
    (rpt strip_tac >> qpat_x_assum `!i. w2n sw <= i /\ i < w2n sw+32+N ==> _`
       (qspec_then `w2n sw+32+i` mp_tac) >> simp[]) >>
  suspend "memory_outputs"
QED

Resume concat_bytes_seq_ptr[memory_outputs]:
  `w2n (n2w N:256 word) = N` by simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `{B+32+k+i | i < N /\ w2n sw+32+i IN tn.t_mem} = {}` by
    (qpat_x_assum `!i. i < N ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] >>
     rpt strip_tac >> gvs[]) >>
  `tc.t_mem = tn.t_mem DIFF {i | B+32+k <= i /\ i < B+32+k+N}` by
    (qpat_x_assum `tc.t_mem = _` mp_tac >> simp[] >> gvs[]) >>
  `tc.t_mem SUBSET tn.t_mem` by simp[] >>
  `!i. B+32+k <= i /\ i < B+32+k+N ==> i NOTIN tc.t_mem` by simp[] >>
  suspend "increment"
QED

Resume concat_bytes_seq_ptr[increment]:
  qabbrev_tac `s4 = u with vs_inst_idx := SUC s3.vs_inst_idx` >>
  `eval_operand (Var r2) s4 = SOME (n2w k) /\
   eval_operand (Var r0) s4 = SOME (n2w N)` by
    gvs[Abbr `s4`, Abbr `u`, Abbr `s3`, Abbr `s2`, Abbr `s1`, Abbr `s0`,
      eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
      mcopy_def, mload_def, write_memory_with_expansion_def] >>
  `op_taint tc (Var r2) = {} /\ op_taint tc (Var r0) = {}` by
    (gvs[op_taint_def] >> metis_tac[]) >>
  mp_tac (Q.SPECL [`D`,`ctx`,`func`,`PG`,`Gf'`,`tc`,`s4`,
    `sx.cs_next_id+5`,`ADD`,`Var r2`,`Var r0`,`r4`,
    `word_add`,`n2w k`,`n2w N`]
    assignTuplePtrLocalBytesCopyTheory.copy_len_binop_seq_ptr) >>
  simp[] >> strip_tac >>
  suspend "last_store"
QED

Resume concat_bytes_seq_ptr[last_store]:
  rename1 `inst_seq_ptr D 0 ctx func PG Gf' tc
    [mk_inst (sx.cs_next_id+5) ADD [Var r2;Var r0] [r4]] s4 H th` >>
  qabbrev_tac `s5 = update_var r4 (n2w k+n2w N) s4 with vs_inst_idx := SUC s4.vs_inst_idx` >>
  `lookup_var oq s5 = lookup_var oq t` by
    (gvs[Abbr `s5`, Abbr `s4`, Abbr `u`, Abbr `s3`, Abbr `s2`, Abbr `s1`, Abbr `s0`,
      lookup_var_def, update_var_def, mcopy_def,
      write_memory_with_expansion_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `ptr_covers H th oq s5 32` by
    (irule annAssignPtrBytestringTheory.annassign_ptr_covers_frame_ptr >>
     qexistsl_tac [`G`,`t`,`tn`] >> simp[] >>
     gvs[op_taint_def] >> metis_tac[]) >>
  `eval_operand (Var oq) s5 = SOME ow /\
   eval_operand (Var r4) s5 = SOME (n2w k+n2w N)` by
    simp[eval_operand_def, Abbr `s5`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  drule_all ifexp_copy_store_phase >>
  disch_then (qspecl_then [`sx.cs_next_id+6`,`func`,`PG`,`D`] strip_assume_tac) >>
  suspend "assemble"
QED

Resume concat_bytes_seq_ptr[assemble]:
  rename1 `inst_seq_ptr D 0 ctx func PG H th
    [mk_inst (sx.cs_next_id+6) MSTORE [Var oq;Var r4] []] s5 H tf` >>
  qexistsl_tac [`H`,`tf`] >> conj_tac
  >- (irule (SRULE [APPEND] (Q.ISPEC `[mk_inst sx.cs_next_id MLOAD [Var src] [r0]]`
        assignTuplePtrLocalBytesCopyTheory.inst_seq_ptr_append_run)) >>
      pure_rewrite_tac[is_terminator_def, boolTheory.NOT_CLAUSES, boolTheory.AND_CLAUSES] >>
      qexistsl_tac [`G'`,`t'`,`tn'`] >>
      `t' with vs_inst_idx := t.vs_inst_idx+1 = s0` by simp[Abbr `s0`, arithmeticTheory.ADD1] >>
      pure_asm_rewrite_tac [] >> rewrite_tac [] >>
      irule (SRULE [APPEND] (Q.ISPEC `[mk_inst (sx.cs_next_id+1) ADD [Var src;Lit 32w] [r1]]`
        assignTuplePtrLocalBytesCopyTheory.inst_seq_ptr_append_run)) >>
      pure_rewrite_tac[is_terminator_def, boolTheory.NOT_CLAUSES, boolTheory.AND_CLAUSES] >>
      qexistsl_tac [`Gf`,`t''`,`tnf`] >>
      `t'' with vs_inst_idx := s0.vs_inst_idx+1 = s1` by simp[Abbr `s1`, arithmeticTheory.ADD1] >>
      pure_asm_rewrite_tac [] >> rewrite_tac [] >>
      irule (SRULE [APPEND] (Q.ISPEC `[mk_inst (sx.cs_next_id+2) MLOAD [Var oq] [r2]]`
        assignTuplePtrLocalBytesCopyTheory.inst_seq_ptr_append_run)) >>
      pure_rewrite_tac[is_terminator_def, boolTheory.NOT_CLAUSES, boolTheory.AND_CLAUSES] >>
      qexistsl_tac [`G''`,`t'''`,`tn''`] >>
      `t''' with vs_inst_idx := s1.vs_inst_idx+1 = s2` by simp[Abbr `s2`, arithmeticTheory.ADD1] >>
      pure_asm_rewrite_tac [] >> rewrite_tac [] >>
      suspend "assemble_tail") >>
  suspend "outputs"
QED

Resume concat_bytes_seq_ptr[assemble_tail]:
  irule (SRULE [APPEND] (Q.ISPEC `[mk_inst (sx.cs_next_id+3) ADD [Var dp;Var r2] [r3]]`
    assignTuplePtrLocalBytesCopyTheory.inst_seq_ptr_append_run)) >>
  pure_rewrite_tac[is_terminator_def, boolTheory.NOT_CLAUSES, boolTheory.AND_CLAUSES] >>
  qexistsl_tac [`Gf'`,`t''''`,`tnf'`] >>
  `t'''' with vs_inst_idx := s2.vs_inst_idx+1 = s3` by simp[Abbr `s3`, arithmeticTheory.ADD1] >>
  pure_asm_rewrite_tac [] >> rewrite_tac [] >>
  irule (SRULE [APPEND] (Q.ISPEC `[mk_inst (sx.cs_next_id+4) MCOPY [Var r3;Var r1;Var r0] []]`
    assignTuplePtrLocalBytesCopyTheory.inst_seq_ptr_append_run)) >>
  pure_rewrite_tac[is_terminator_def, boolTheory.NOT_CLAUSES, boolTheory.AND_CLAUSES] >>
  qexistsl_tac [`Gf'`,`u`,`tc`] >>
  `u with vs_inst_idx := s3.vs_inst_idx+1 = s4` by simp[Abbr `s4`, arithmeticTheory.ADD1] >>
  pure_asm_rewrite_tac [] >> rewrite_tac [] >>
  irule (SRULE [APPEND] (Q.ISPEC `[mk_inst (sx.cs_next_id+5) ADD [Var r2;Var r0] [r4]]`
    assignTuplePtrLocalBytesCopyTheory.inst_seq_ptr_append_run)) >>
  pure_rewrite_tac[is_terminator_def, boolTheory.NOT_CLAUSES, boolTheory.AND_CLAUSES] >>
  qexistsl_tac [`H`,`update_var r4 (n2w k+n2w N) s4`,`th`] >>
  `update_var r4 (n2w k+n2w N) s4 with vs_inst_idx := s4.vs_inst_idx+1 = s5` by
    simp[Abbr `s5`, arithmeticTheory.ADD1] >>
  pure_asm_rewrite_tac [] >> rewrite_tac []
QED

Resume concat_bytes_seq_ptr[outputs]:
  conj_tac >- (gvs[] >> ASM_SET_TAC []) >>
  conj_tac >- gvs[] >> conj_tac >- gvs[] >> conj_tac >- gvs[] >>
  conj_tac
  >- (rpt strip_tac >> gvs[op_taint_def] >> metis_tac[]) >>
  conj_tac >> rpt strip_tac >> gvs[]
QED

Finalise concat_bytes_seq_ptr
