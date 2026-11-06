Theory bodyPtrMakeArrayCountedLength
Ancestors
  bodyPtrMakeArrayCountStep bodyPtrMakeArrayPrimitiveInstall
  fragGasPathPtr valueCopy ptrDiscipline venomExecSemantics venomState
  venomInst finite_map

(* A literal arithmetic instruction leaves all non-variable runtime fields
   relevant to the next installed instruction unchanged. *)
Theorem copy_len_literal_endpoint:
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id opc [Var input; Lit k] [tmp]) ==>
  (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
  eval_operand (Var input) s = SOME v /\ op_taint tn (Var input) = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_inst_idx = SUC s.vs_inst_idx /\
    sf.vs_current_bb = s.vs_current_bb /\ sf.vs_halted = s.vs_halted /\
    eval_operand (Var tmp) sf = SOME (f v k) /\
    op_taint tnf (Var tmp) = {} /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!x. x <> tmp ==>
      lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`left` |-> `Var input`, `right` |-> `Lit k`,
                 `a` |-> `v:bytes32`, `b` |-> `k:bytes32`]
    copy_len_binop_endpoint) >>
  simp[eval_operand_def, op_taint_def] >>
  strip_tac >>
  qexistsl_tac [`Gf`, `tnf`,
    `update_var tmp (f v k) s with vs_inst_idx := SUC s.vs_inst_idx`] >>
  gvs[update_var_def]
QED

Theorem copy_len_round_endpoint:
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id1 ADD [Var a; Lit 31w] [b]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst id2 AND [Var b; Lit (i2w (-32))] [c]) /\
  get_instruction bb (s.vs_inst_idx + 2) =
    SOME (mk_inst id3 ADD [Var c; Lit 32w] [d]) /\
  eval_operand (Var a) s = SOME v /\ op_taint tn (Var a) = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_inst_idx = s.vs_inst_idx + 3 /\
    sf.vs_current_bb = s.vs_current_bb /\ sf.vs_halted = s.vs_halted /\
    eval_operand (Var d) sf = SOME (((v + 31w) && i2w (-32)) + 32w) /\
    op_taint tnf (Var d) = {} /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!x. x <> b /\ x <> c /\ x <> d ==>
      lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule (SRULE [] (Q.INST [`f` |-> `word_add`] copy_len_literal_endpoint)) >>
  disch_then (drule_all o SRULE []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] mp_tac) >>
  disch_then (qx_choose_then `G1` (qx_choose_then `tn1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `get_instruction bb s1.vs_inst_idx =
    SOME (mk_inst id2 AND [Var b; Lit (i2w (-32))] [c])` by simp[] >>
  pop_assum (mp_then Any mp_tac
    (Q.INST [`f` |-> `word_and`] copy_len_literal_endpoint)) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  disch_then (drule_all o SRULE []) >>
  disch_then (qspecl_then [`PG`, `G1`, `D`] mp_tac) >>
  disch_then (qx_choose_then `G2` (qx_choose_then `tn2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  `get_instruction bb s2.vs_inst_idx =
    SOME (mk_inst id3 ADD [Var c; Lit 32w] [d])` by
      simp[arithmeticTheory.ADD1] >>
  pop_assum (mp_then Any mp_tac
    (Q.INST [`f` |-> `word_add`] copy_len_literal_endpoint)) >>
  `lookup_block s2.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  disch_then (drule_all o SRULE []) >>
  disch_then (qspecl_then [`PG`, `G2`, `D`] mp_tac) >>
  disch_then (qx_choose_then `G3` (qx_choose_then `tn3`
    (qx_choose_then `s3` strip_assume_tac))) >>
  qexistsl_tac [`G3`, `tn3`, `s3`] >>
  conj_tac >- (metis_tac[SRULE []
    (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)]) >>
  simp[arithmeticTheory.ADD1] >> metis_tac[]
QED

Theorem bytestring_copy_len_counted:
  compile_bytestring_copy_len (Var src) sa = (out,sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME p /\
  (!i. w2n p <= i /\ i < w2n p + 32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    sf.vs_current_bb = sb.cs_current_bb /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (((mload (w2n p) s + 31w) && i2w (-32)) + 32w) /\
    op_taint tnf out = {} /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all bytestring_copy_len_fetch >> strip_tac >>
  map_every (fn i => qpat_assum `!i. i < 4 ==> _`
    (qspec_then i assume_tac)) [`0`, `1`, `2`, `3`] >> fs[] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id MLOAD [Var src] [a])` by simp[] >>
  drule_all copy_len_header_endpoint >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choose_then `G1` (qx_choose_then `tn1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `s1.vs_inst_idx = SUC s.vs_inst_idx /\
   s1.vs_current_bb = s.vs_current_bb /\ ~s1.vs_halted` by
    simp[update_var_def] >>
  `get_instruction bb s1.vs_inst_idx =
    SOME (mk_inst (sa.cs_next_id + 1) ADD [Var a; Lit 31w] [b]) /\
   get_instruction bb (SUC s1.vs_inst_idx) =
    SOME (mk_inst (sa.cs_next_id + 2) AND [Var b; Lit (i2w (-32))] [c]) /\
   get_instruction bb (s1.vs_inst_idx + 2) =
    SOME (mk_inst (sa.cs_next_id + 3) ADD [Var c; Lit 32w] [d]) /\
   lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb` by
     simp[arithmeticTheory.ADD1] >>
  drule_all copy_len_round_endpoint >>
  disch_then (qspecl_then [`PG`, `G1`, `D`] mp_tac) >>
  disch_then (qx_choose_then `G2` (qx_choose_then `tn2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >>
  conj_tac >- (metis_tac[SRULE []
    (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)]) >>
  simp[arithmeticTheory.ADD1] >> metis_tac[]
QED

Theorem bytestring_copy_len_counted_exact:
  compile_bytestring_copy_len (Var src) sa = (out,sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME p /\
  (!i. w2n p <= i /\ i < w2n p + 32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  mload (w2n p) s = n2w len /\
  n = 32 + 32 * ((len + 31) DIV 32) /\
  len + 31 < dimword (:256) /\ n < dimword (:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    sf.vs_current_bb = sb.cs_current_bb /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (n2w n) /\ op_taint tnf out = {} /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all bytestring_copy_len_counted >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> strip_tac >>
  `w2n (((n2w len + 31w) && i2w (-32)) + 32w : bytes32) = n` by
    (qspec_then `len` mp_tac bytestring_copy_len_word_exact >>
     gvs[vfmConstantsTheory.word_size_def]) >>
  `(((n2w len + 31w) && i2w (-32)) + 32w : bytes32) = n2w n` by
    metis_tac[wordsTheory.n2w_w2n] >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> gvs[]
QED
