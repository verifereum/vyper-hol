(* Counted dynamic copy after the clean bytestring length prefix. *)
Theory annAssignPtrBytestring
Ancestors
 annAssignPtrLength annAssignPtrCopy annAssignPtrSetup typedCopyPtr
 fragGasPathPtr bodyPtrDefs ptrDiscipline venomInst venomInstProofs
 venomExecSemantics venomState venomMemDefs venomMemProofs
 context emitHelper emitHelperProps finite_map pred_set compileEnv fragExec
 valueCopy vfmConstants arithmetic annAssignPtrScratch robustCopyTransportPtr valueEncoding valueEncodingProps

Theorem annassign_emit_mcopy_path_ptr:
 !D ctx func PG G tn s dst src count_op a b n k sa sb.
 emit_inst MCOPY [Var dst;Var src;count_op] [] sa = ((),sb) /\
 fn_has_code sa sb func /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\ w2n n = k /\
 ptr_covers G tn src s k /\ ptr_covers G tn dst s k ==>
 ?sf tnf. gas_path_ptr D 0 ctx func PG G tn s 0 G tnf (OK sf) /\
 sf.vs_current_bb = sb.cs_current_bb /\ sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
 ~sf.vs_halted /\
 (sf with <|vs_memory := s.vs_memory;vs_inst_idx := s.vs_inst_idx|>) = s /\
 (tnf with t_mem := tn.t_mem) = tn /\
 (!x. lookup_var x sf = lookup_var x s) /\
 sf.vs_memory = (mcopy (w2n b) (w2n a) k s).vs_memory /\
 tnf.t_var = tn.t_var /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
 tnf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + k}) UNION
              {w2n b + i | i < k /\ w2n a + i IN tn.t_mem}
Proof
 rpt gen_tac >> strip_tac >>
 drule_all annassign_emit_instruction_ptr >> strip_tac >>
 `sb.cs_current_bb = sa.cs_current_bb /\
  LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
  gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
 qexistsl [`mcopy (w2n b) (w2n a) k s with vs_inst_idx := SUC s.vs_inst_idx`,
  `step_taint (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []) s
    (mcopy (w2n b) (w2n a) k s) tn`] >>
 conj_tac >- (irule annassign_mcopy_path_ptr >> simp[] >> metis_tac[]) >>
 qpat_x_assum `w2n n = k` (SUBST_ALL_TAC o SYM) >>
 simp[annassign_mcopy_cursor_ptr, annassign_mcopy_restore_ptr,
      annassign_mcopy_taint_restore_ptr, mcopy_operand_ghost_frame, eval_operand_def]
QED

Theorem annassign_ptr_covers_frame_ptr:
 !G tn p s n G' tn' s'.
 ptr_covers G tn p s n /\
 lookup_var p s' = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
 op_taint tn' (Var p) = op_taint tn (Var p) ==>
 ptr_covers G' tn' p s' n
Proof
 simp[ptr_covers_def]
QED

Theorem annassign_store_bytestring_layout_ptr:
 !src dst sa sb func.
 compile_store_bytestring src dst sa = ((),sb) /\ fn_has_code sa sb func ==>
 ?count_op sc.
 compile_bytestring_copy_len src sa = (count_op,sc) /\
 emit_inst MCOPY [dst;src;count_op] [] sc = ((),sb) /\
 fn_has_code sa sc func /\ fn_has_code sc sb func
Proof
 rpt gen_tac >> strip_tac >>
 qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
 simp[compile_store_bytestring_def, comp_bind_def] >>
 pairarg_tac >> simp[emit_void_def, GSYM emit_inst_def] >> strip_tac >>
 rename1 `compile_bytestring_copy_len src sa = (count_op,sc)` >>
 `cs_extends sa sc` by
  (drule annassign_copy_len_decompose_ptr >> strip_tac >>
   metis_tac[cs_extends_trans]) >>
 `cs_extends sc sb` by
  gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def, cs_extends_def] >>
 drule_all fn_has_code_split >> strip_tac >>
 goal_assum (drule_at Any) >> simp[]
QED

Theorem annassign_bytestring_prefix_path_ptr:
 !D ctx func PG G tn s sa sb src dst a b len n.
 compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\ fn_has_code sa sb func /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 not_fresh_at sa src /\ not_fresh_at sa dst /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 n = 32 + 32 * ((len + 31) DIV 32) /\ n < dimword (:256) /\
 mload (w2n a) s = n2w len /\ ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
 (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
 ?count_op sc Gf tnf sf.
 emit_inst MCOPY [Var dst;Var src;count_op] [] sc = ((),sb) /\ fn_has_code sc sb func /\
 gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sc.cs_current_bb /\ sf.vs_inst_idx = LENGTH sc.cs_current_insts /\
 ~sf.vs_halted /\ eval_operand count_op sf = SOME (n2w n) /\ op_taint tnf count_op = {} /\
 lookup_var src sf = SOME a /\ lookup_var dst sf = SOME b /\
 ptr_covers Gf tnf src sf n /\ ptr_covers Gf tnf dst sf n /\
 (sf with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
 sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
 tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s /\
   FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
 rpt gen_tac >> strip_tac >>
 drule_all annassign_store_bytestring_layout_ptr >> strip_tac >>
 `32 <= n` by simp[] >>
 `ptr_covers G tn src s 32` by
  (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_MONO_ADD_EQ]) >>
 drule_all annassign_bytestring_copy_len_path_ptr >>
 disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
 `((n2w len + 31w && i2w (-32)) + 32w : bytes32) = n2w n` by
  (once_rewrite_tac[GSYM wordsTheory.w2n_11] >>
   qspec_then `len` mp_tac bytestring_copy_len_word_exact >>
   simp[word_size_def, wordsTheory.w2n_n2w] >>
   metis_tac[wordsTheory.n2w_w2n]) >>
 qexistsl [`count_op`,`sc`,`Gf`,`tnf`,`sf`] >> simp[] >>
 rpt conj_tac >> irule annassign_ptr_covers_frame_ptr >>
 qexistsl [`G`,`s`,`tn`] >> gvs[]
QED

Theorem annassign_store_bytestring_path_ptr:
 !D ctx func PG G tn s sa sb src dst a b len n.
 compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\ fn_has_code sa sb func /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 not_fresh_at sa src /\ not_fresh_at sa dst /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 n = 32 + 32 * ((len + 31) DIV 32) /\ n < dimword (:256) /\
 mload (w2n a) s = n2w len /\ ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
 (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sb.cs_current_bb /\ sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
 ~sf.vs_halted /\
 (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_inst_idx := s.vs_inst_idx|>) = s /\
 sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 tnf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + n}) UNION
              {w2n b + i | i < n /\ w2n a + i IN tn.t_mem} /\
 (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s /\
   FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
 rpt gen_tac >> strip_tac >>
 drule_all annassign_bytestring_prefix_path_ptr >>
 disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
 rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1 (OK s1)` >>
 `w2n (n2w n : bytes32) = n` by simp[wordsTheory.w2n_n2w] >>
 drule_all annassign_emit_mcopy_path_ptr >>
 disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
 qexistsl [`G1`,`tnf`,`sf`] >>
 conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
 `(mcopy (w2n b) (w2n a) n s1).vs_memory =
  (mcopy (w2n b) (w2n a) n s).vs_memory` by
  simp[mcopy_def, write_memory_with_expansion_def] >>
 gvs[taint_component_equality, op_taint_def]
QED

(* Robust destination representation and the exterior byte frame depend only
   on the copy window, not on the arithmetic variables of the length prefix. *)
Theorem annassign_bytestring_copy_robust_ptr:
 !D ctx func PG G tn s sa sb src dst a b len n tv v.
 compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\ fn_has_code sa sb func /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 not_fresh_at sa src /\ not_fresh_at sa dst /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 n = 32 + 32 * ((len + 31) DIV 32) /\ n < dimword (:256) /\
 mload (w2n a) s = n2w len /\ ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
 (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
 val_wf tv v /\ val_footprint tv v <= n /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n a) m) ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sb.cs_current_bb /\ sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
 ~sf.vs_halted /\
 (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_inst_idx := s.vs_inst_idx|>) = s /\
 sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s /\
   FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
 (!i. ~(w2n b <= i /\ i < w2n b+n) ==>
   mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
   (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
 (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==> val_in_memory tv v (w2n b) m)
Proof
 rpt gen_tac >> strip_tac >>
 drule_all annassign_store_bytestring_path_ptr >>
 disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
 drule annassign_copy_taint_window_ptr >> strip_tac >>
 `mem_bytes_at (w2n b) n sf.vs_memory = mem_bytes_at (w2n a) n s.vs_memory` by
   simp[mcopy_mem_bytes_at_same] >>
 `!i. ~(w2n b <= i /\ i < w2n b+n) ==>
   mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory` by
   (rpt strip_tac >> simp[] >> irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
 `!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n b) m` by
   (rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
    conj_tac >- simp[] >>
    qexistsl [`s.vs_memory`,`sf.vs_memory`,`n`,`w2n a`,`tn.t_mem`,`tnf.t_mem`] >>
    asm_rewrite_tac[]) >>
 qexistsl [`Gf`,`tnf`,`sf`] >> simp[]
QED
