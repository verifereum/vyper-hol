(* Counted fixed-copy boundary retaining byte and taint exterior frames. *)
Theory assignTuplePtrLocalCopyPath
Ancestors
  assignTuplePtrLocalFixedCopy assignTuplePtrLocalCopyRun assignTuplePtrBytesCopy
  fragGasPathPtr
  venomState venomExecSemantics fragExec exprLoweringProps context

Theorem compile_fixed_copy_path_frames_ptr:
  compile_store_memory cenv (Var src) (Var dst) ty ty sa = ((),sb) /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  n = type_memory_bytes cenv ty /\ n < dimword (:256) /\
  ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?tn'.
    gas_path_ptr D 0 ctx func PG G tn s 0 G tn'
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    (!p. lookup_var p u = lookup_var p s /\
         op_taint tn' (Var p) = op_taint tn (Var p)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!off k. off + k <= n ==> mem_bytes_at (w2n b + off) k u.vs_memory =
      mem_bytes_at (w2n a + off) k s.vs_memory) /\
    (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. i < n ==> (w2n b + i IN tn'.t_mem <=> w2n a + i IN tn.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >> drule_all compile_fixed_copy_frames_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  drule_all tuple_local_copy_code_shape_ptr >> strip_tac >>
  drule_all emitted_sequence_path_ptr >> strip_tac >>
  qexists_tac `tn'` >> simp[]
QED

Theorem compile_bytes_copy_path_frames_ptr:
  compile_store_memory cenv (Var src) (Var dst) ty ty sa = ((),sb) /\
  ~is_word_type ty /\ is_bytestring_type ty /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  n = 32 + 32 * ((len + 31) DIV 32) /\
  len + 31 < dimword (:256) /\ n < dimword (:256) /\
  mload (w2n a) s = n2w len /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb ==>
  ?Gf tnf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    u.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
    (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!i. i < n ==> (w2n b + i IN tnf.t_mem <=> w2n a + i IN tn.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `compile_store_bytestring (Var src) (Var dst) sa = ((),sb)` by
    fs[compile_store_memory_def] >>
  drule_all compile_store_bytestring_run_frames_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  drule_all tuple_local_copy_code_shape_ptr >> strip_tac >>
  drule_all emitted_sequence_path_ptr >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`] >> simp[]
QED
