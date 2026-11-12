(* Counted runtime payload copy for equal-element dynamic arrays. *)
Theory bodyPtrTypedCopyDynamicFast
Ancestors bodyPtrTypedCopyArrayControl annAssignPtrCopy
  assignTuplePtrLocalFixedCopy annAssignPtrScratch venomMemProofs
  venomExecSemantics venomInst venomState ptrDiscipline words
  finite_map arithmetic bodyPtrDefs fragGasPathPtr fragGasSeqPtr

Theorem typed_copy_dynamic_payload_counted:
  !s ctx fn bb id len cnt src dst a b n stride G tn PG D.
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id MUL [Var len;Lit (n2w stride)] [cnt]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst (id+1) MCOPY [Var dst;Var src;Var cnt] []) /\
  lookup_var len s = SOME (n2w n) /\ op_taint tn (Var len) = {} /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s (n*stride) /\ ptr_covers G tn dst s (n*stride) /\
  cnt <> src /\ cnt <> dst /\ cnt <> len /\
  n*stride < dimword(:256) /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?H tf u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx+2 /\
    ~u.vs_halted /\
    u.vs_memory = (mcopy (w2n b) (w2n a) (n*stride) s).vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_inst_idx := s.vs_inst_idx|>) = s /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. i < n*stride ==> (w2n b+i IN tf.t_mem <=> w2n a+i IN tn.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b+n*stride) ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    mem_bytes_at (w2n b) (n*stride) u.vs_memory =
      mem_bytes_at (w2n a) (n*stride) s.vs_memory /\
    (!p. p <> cnt ==> lookup_var p u = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `s1 = update_var cnt (n2w (n*stride)) s with
    vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g1 = DRESTRICT G (COMPL {cnt})` >>
  qabbrev_tac `t1 = tn with t_var := tn.t_var |+ (cnt,{})` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 t1 (OK s1)` by
    (simp[Abbr `s1`, Abbr `g1`, Abbr `t1`] >>
     irule typed_copy_arith_counted >> simp[update_var_def] >>
     qexistsl_tac [`id`, `MUL`, `[Var len; Lit (n2w stride)]`] >>
     simp[] >> conj_tac
     >- (rpt strip_tac >> gvs[op_taint_def]) >>
     simp[update_var_def,
       step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, wordsTheory.word_mul_n2w]) >>
  qabbrev_tac `u = (mcopy (w2n b) (w2n a) (n*stride) s1) with
    vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `tf = step_taint (mk_inst (id+1) MCOPY
    [Var dst; Var src; Var cnt] []) s1
    (mcopy (w2n b) (w2n a) (n*stride) s1) t1` >>
  `gas_path_ptr D 0 ctx fn PG g1 t1 s1 0 g1 tf (OK u)` by
    (simp[Abbr `u`, Abbr `tf`] >>
     irule annassign_mcopy_path_ptr >>
     simp[Abbr `s1`, Abbr `g1`, Abbr `t1`, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE, eval_operand_def, op_taint_def,
       ptr_covers_def, FLOOKUP_DRESTRICT, LESS_MOD] >>
     gvs[ptr_covers_def, lookup_var_def, op_taint_def]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 tf (OK u)` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  `tf.t_var = t1.t_var /\ tf.t_stor = t1.t_stor /\
   tf.t_trans = t1.t_trans /\ tf.t_imm = t1.t_imm /\
   (!i. i < n*stride ==> (w2n b+i IN tf.t_mem <=> w2n a+i IN t1.t_mem)) /\
   (!i. ~(w2n b <= i /\ i < w2n b+n*stride) ==>
     (i IN tf.t_mem <=> i IN t1.t_mem))` by
    (irule mcopy_operand_taint_frames_ptr >>
     qexistsl_tac [`Var cnt`, `Var dst`, `id+1`,
       `n2w (n*stride)`, `s1`, `Var src`] >>
     simp[Abbr `tf`, Abbr `s1`, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, LESS_MOD] >>
     gvs[lookup_var_def]) >>
  `!p. p <> cnt ==> lookup_var p u = lookup_var p s /\
    FLOOKUP g1 p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)` by
    (rpt strip_tac >>
     simp[Abbr `u`, Abbr `s1`, Abbr `g1`, lookup_var_def,
       mcopy_def, write_memory_with_expansion_def,
       update_var_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
       op_taint_def, Abbr `t1`]) >>
  qexistsl_tac [`g1`, `tf`, `u`] >>
  simp[Abbr `t1`] >>
  `u.vs_memory = (mcopy (w2n b) (w2n a) (n*stride) s).vs_memory` by
    simp[Abbr `u`, Abbr `s1`, mcopy_def, write_memory_with_expansion_def,
      update_var_def] >>
  simp[valueEncodingProofsTheory.mcopy_mem_bytes_at_same] >>
  `!i. ~(w2n b <= i) \/ ~(i < w2n b+n*stride) ==>
     mem_bytes_at i 1 (mcopy (w2n b) (w2n a) (n*stride) s).vs_memory =
     mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >>
     irule valueEncodingProofsTheory.mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  simp[] >>
  gvs[Abbr `u`, Abbr `s1`, mcopy_def, write_memory_with_expansion_def,
    update_var_def] >> gvs[]
QED
