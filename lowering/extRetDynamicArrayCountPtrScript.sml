Theory extRetDynamicArrayCountPtr
Ancestors
  extRetBytesCopyCountedPtr extRetBulkCopyCountedPtr extRetFramedChildPtr
  fragGasPathPtr emitHelperProps exprLoweringProps emitHelper compileEnv
  bodyPtrDefs ptrDiscipline venomState venomMemDefs words finite_map
  pred_set arithmetic

(* The actual array prefix reads the count before overwriting the output
   header. Keep its provenance and exact allocation frame for initialization. *)
Theorem encoder_dynamic_count_header_counted_ptr:
  emit_op MLOAD [Var src] sa = (Var cv,sb) /\
  emit_void MSTORE [Var dst;Var cv] sb = ((),sc) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa dst /\
  lookup_var src s = SOME (n2w a) /\ a < dimword(:256) /\
  ptr_covers G tn src s 32 /\
  (!i. a <= i /\ i < a+32 ==> i NOTIN tn.t_mem) /\
  mload a s = n2w N /\ lookup_var dst s = SOME (n2w b) /\
  ptr_covers G tn dst s 32 /\ b < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sc.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var cv sf = SOME (n2w N) /\ op_taint tnf (Var cv) = {} /\
    op_prov Gf (Var cv) = NONE /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_memory = (mstore b (n2w N) s).vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32} /\
    (!i. i < b \/ b+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!i. b <= i /\ i < b+32 ==> i NOTIN tnf.t_mem) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    encoder_ambient_frame tn s tnf sf
Proof
  strip_tac >>
  `!i. w2n (n2w a : bytes32) <= i /\
    i < w2n (n2w a : bytes32)+32 ==> i NOTIN tn.t_mem` by
    simp[w2n_n2w, LESS_MOD] >>
  drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `lookup_var dst sf = SOME (n2w b) /\ ptr_covers Gf tnf dst sf 32 /\
   eval_operand (Var cv) sf = SOME (n2w N)` by
    (gvs[ptr_covers_def, eval_operand_def, w2n_n2w, LESS_MOD] >> metis_tac[]) >>
  drule_all emit_mstore_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`,`tnf'`,`sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`,`sf`,`tnf`] >> simp[]) >>
  simp[encoder_ambient_frame_def, w2n_n2w, LESS_MOD] >>
  fs[w2n_n2w, LESS_MOD, mstore_def, write_memory_with_expansion_def] >>
  metis_tac[]
QED
