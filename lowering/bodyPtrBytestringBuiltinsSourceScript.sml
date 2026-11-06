(* Source preparation for memory-backed slices. Fixed bytes use a raw
   scratch word, not a dynamic bytestring's length-prefixed representation. *)
Theory bodyPtrBytestringBuiltinsSource
Ancestors
  bodyPtrBytestringBuiltinsBuffer exprSimPtrProps builtinBytes
  emitHelper compileEnv exprLoweringProps bodyPtrDefs venomState venomInstProofs
  finite_map

Theorem compile_bytestring_src_parts:
  compile_bytestring_src src sa = ((len,data),sb) ==>
  ?sm. emit_op MLOAD [src] sa = (len,sm) /\
       emit_op ADD [src; Lit 32w] sm = (data,sb)
Proof
  simp[compile_bytestring_src_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

(* A clean length word is scalar, while the source root remains a pointer.
   The explicit loaded value premise is supplied by source representation. *)
Theorem emit_bytestring_length_counted:
  emit_op MLOAD [Var src] sa = (op,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ not_fresh_at sa src /\
  ptr_covers G tn src s (32+L) /\ lookup_var src s = SOME a /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  mload (w2n a) s = n2w L /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  !D PG. ?out G' tn'.
    op = Var out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK ((update_var out (n2w L) s) with vs_inst_idx := SUC s.vs_inst_idx)) /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\
    ptr_covers G' tn' src (update_var out (n2w L) s) (32+L) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> rpt gen_tac >>
  `ptr_covers G tn src s 32` by
    (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LE_ADD]) >>
  drule_all emit_mload_ptr_path >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`out`,`G'`,`tn'`] >> gvs[] >>
  conj_tac
  >- (`src <> STRING #"%" (toString sa.cs_next_var)` by metis_tac[] >>
      gvs[ptr_covers_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  metis_tac[]
QED
