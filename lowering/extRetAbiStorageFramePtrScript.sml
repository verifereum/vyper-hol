(* Storage safety transport for finite memory-only ABI encoder stages. *)
Theory extRetAbiStorageFramePtr
Ancestors bodyPtrDefs ptrDiscipline venomState extRetAbiSingletonWrapperPtr
  abiBuiltinAllocation valueEncodingProofs words finite_map pred_set arithmetic

Theorem stor_taint_ok_ambient_transport:
  stor_taint_ok cx tn s /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
  sf.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address ==>
  stor_taint_ok cx tnf sf
Proof
  simp[stor_taint_ok_def]
QED

Theorem compile_abi_encode_singleton_bytes_stor_counted_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src)
    (AbiComplex [(AbiBytestring maxlen,32,cap,T)]) sa = (out,sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME (n2w a) /\ lookup_var dst s = SOME (n2w b) /\
  ptr_covers G tn src s cap /\ ptr_covers G tn dst s (64+ceil32 (LENGTH bs)) /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas sa.cs_next_id =
    SOME (cursor,32) /\ cursor+32 < dimword(:256) /\
  (cursor+32 <= a \/ a+cap <= cursor) /\
  (cursor+32 <= b \/ b+64+ceil32 (LENGTH bs) <= cursor) /\
  32+LENGTH bs <= cap /\ LENGTH bs <= dimword(:256)-32 /\
  32+ceil32 (LENGTH bs) < dimword(:256) /\
  a+cap < dimword(:256) /\ b+64+ceil32 (LENGTH bs) < dimword(:256) /\
  (a+cap <= b \/ b+64+ceil32 (LENGTH bs) <= a) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) a cap mem') /\
  stor_taint_ok cx tn s ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (n2w (64+ceil32 (LENGTH bs))) /\ op_taint tnf out = {} /\
    ptr_covers Gf tnf dst sf (64+ceil32 (LENGTH bs)) /\
    (!i. b <= i /\ i < b+64+ceil32 (LENGTH bs) ==> i NOTIN tnf.t_mem) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    stor_taint_ok cx tnf sf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_abi_encode_singleton_bytes_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
  irule stor_taint_ok_ambient_transport >>
  qexistsl_tac [`s`, `tn`] >> simp[]
QED
