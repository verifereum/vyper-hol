(* Actual singleton dynamic bytes encoder: finite compiler cuts. *)
Theory extRetAbiSingletonWrapperPtr
Ancestors
  extRetAbiSingletonCountedPtr abiEncoderComplexCode abiEncoderComplexPrefix
  abiEncoderMemberCode abiEncoderChildCode abiEncoderAddressReach
  extRetBulkCopyCountedPtr extRetCountedPtr fragExec fragGasPathPtr fragGasSeqPtr
  emitHelperProps exprLoweringProps compileEnv emitHelper exprLowering
  abiEncoder abiBuiltinAllocation bodyPtrDefs ptrDiscipline venomState
  robustCopyTransportPtr abiEncoderInputFrame valueEncodingProofs extRetBytesCopyCountedPtr
  words finite_map pred_set arithmetic list rich_list

Theorem abi_singleton_wrapper_context:
  compile_abi_encode_to_buf (Var dst) (Var src)
    (AbiComplex [(AbiBytestring maxlen,32,cap,T)]) sa = (out,sb) /\
  fn_has_code sa sb fn ==>
  ?ip elem sc sd se ignored.
    abi_encode_complex_prefix [(AbiBytestring maxlen,32,cap,T)] sa = (Var ip,sc) /\
    emit_op ADD [Var src;Lit 0w] sc = (Var elem,sd) /\
    compile_abi_encode_child (Var dst) (Var elem) (AbiBytestring maxlen) T 0
      (Var ip) sd = (ignored,se) /\
    emit_op MLOAD [Var ip] se = (out,sb) /\
    fn_has_code sa sc fn /\ fn_has_code sc sd fn /\
    fn_has_code sd se fn /\ fn_has_code se sb fn /\
    not_fresh_at sc ip /\ not_fresh_at sd ip /\ not_fresh_at sd elem /\
    not_fresh_at se ip /\
    (!v. not_fresh_at sa v ==> not_fresh_at sc v) /\
    (!v. not_fresh_at sc v ==> not_fresh_at sd v) /\
    (!v. not_fresh_at sd v ==> not_fresh_at se v)
Proof
  strip_tac >>
  `EXISTS (\(_,_,_,dyn). dyn) [(AbiBytestring maxlen,32,cap,T)]` by simp[] >>
  drule_all abi_encoder_complex_dynamic_trace >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  drule abi_encoder_members_bounds >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  `cs_extends sa prepared` by
    (irule cs_extends_same_block >> fs[inst_extends_def, IS_PREFIX_APPEND]) >>
  `cs_extends prepared sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa prepared fn /\ fn_has_code prepared middle fn /\
   fn_has_code middle sb fn` by metis_tac[fn_has_code_split] >>
  drule_all abi_encoder_member_cons_context >> strip_tac >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ [] _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_encode_child_def, comp_return_def] >> strip_tac >> gvs[] >>
  `?elem. elem_src = Var elem /\ not_fresh_at prepared' elem` by
    (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[not_fresh_at_def]) >>
  gvs[] >>
  simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac
QED

Theorem compile_abi_encode_singleton_bytes_ambient_counted_ptr:
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
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) a cap mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (n2w (64+ceil32 (LENGTH bs))) /\ op_taint tnf out = {} /\
    ptr_covers Gf tnf dst sf (64+ceil32 (LENGTH bs)) /\
    (!i. b <= i /\ i < b+64+ceil32 (LENGTH bs) ==> i NOTIN tnf.t_mem) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_singleton_wrapper_context >> strip_tac >>
  drule_all abi_encode_singleton_prefix_ambient_counted_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `lookup_var src sf = SOME (n2w a) /\ lookup_var dst sf = SOME (n2w b) /\
   ptr_covers Gf tnf src sf cap /\
   ptr_covers Gf tnf dst sf (64+ceil32 (LENGTH bs)) /\
   not_fresh_at sc src /\ not_fresh_at sc dst` by
    (`lookup_var src sf = lookup_var src s /\ FLOOKUP Gf src = FLOOKUP G src /\
      op_taint tnf (Var src) = op_taint tn (Var src) /\
      lookup_var dst sf = lookup_var dst s /\ FLOOKUP Gf dst = FLOOKUP G dst /\
      op_taint tnf (Var dst) = op_taint tn (Var dst)` by metis_tac[] >>
     fs[ptr_covers_def] >> gvs[]) >>
  `mem_bytes_at a cap sf.vs_memory = mem_bytes_at a cap s.vs_memory /\
   (!i. i < cap ==> (a+i IN tnf.t_mem <=> a+i IN tn.t_mem))` by
    suspend "source_window" >>
  `!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) a cap mem'` by
    (rpt strip_tac >> drule_all copied_window_agree_witness >> strip_tac >>
     `abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) a cap mix` by
       metis_tac[] >>
     drule_all abi_encoder_input_mem_agree >> simp[]) >>
  `a < dimword(:256)` by decide_tac >>
  `w2n (n2w a : 256 word) < dimword(:256) /\ cap <= cap` by simp[] >>
  drule_all (SRULE [] (Q.INST [`off` |-> `0`, `n` |-> `cap`, `extent` |-> `cap`]
    (SPEC_ALL emit_bulk_offset_ambient_counted_ptr))) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var dst sf' = SOME (n2w b) /\ lookup_var ip sf' = SOME (n2w cursor) /\
   ptr_covers Gf' tnf' dst sf' (64+ceil32 (LENGTH bs)) /\
   ptr_covers Gf' tnf' ip sf' 32 /\ not_fresh_at sd dst /\
   mload cursor sf' = 32w /\
   (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tnf'.t_mem) /\
   (!mem'. mem_agree_outside tnf'.t_mem sf'.vs_memory mem' ==>
      abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) a cap mem')` by
    suspend "child_resources" >>
  Q.SUBGOAL_THEN `(a+cap <= b+32 \/ b+64+ceil32 (LENGTH bs) <= a)` assume_tac
  >- decide_tac >>
  drule_all abi_singleton_bytes_child_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var ip sf'' = SOME (n2w cursor) /\ ptr_covers Gf'' tnf'' ip sf'' 32` by
    suspend "load_resources" >>
  `cursor < dimword(:256)` by decide_tac >>
  `!i. w2n (n2w cursor : 256 word) <= i /\
       i < w2n (n2w cursor : 256 word)+32 ==> i NOTIN tnf''.t_mem` by
    simp[] >>
  `?v. out = Var v` by metis_tac[emitted_insts_emit_op] >>
  qpat_x_assum `out = Var _` SUBST_ALL_TAC >>
  drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf'''`, `tnf'''`, `sf'''`] >>
  conj_tac >- suspend "path" >>
  suspend "endpoint"
QED

Resume compile_abi_encode_singleton_bytes_ambient_counted_ptr[source_window]:
  conj_tac
  >- (irule LIST_EQ >> simp[] >> rpt strip_tac >>
      rename1 `j < cap` >>
      `mem_bytes_at (a+j) 1 sf.vs_memory = mem_bytes_at (a+j) 1 s.vs_memory` by
        (qpat_x_assum `mem_agree_outside _ sf.vs_memory _` mp_tac >>
         simp[mem_agree_outside_def] >> disch_then irule >> simp[] >> decide_tac) >>
      pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]) >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Resume compile_abi_encode_singleton_bytes_ambient_counted_ptr[child_resources]:
  `lookup_var dst sf' = lookup_var dst sf /\ FLOOKUP Gf' dst = FLOOKUP Gf dst /\
   op_taint tnf' (Var dst) = op_taint tnf (Var dst) /\
   lookup_var ip sf' = lookup_var ip sf /\ FLOOKUP Gf' ip = FLOOKUP Gf ip /\
   op_taint tnf' (Var ip) = op_taint tnf (Var ip)` by metis_tac[] >>
  fs[ptr_covers_def, mload_def] >> gvs[]
QED

Resume compile_abi_encode_singleton_bytes_ambient_counted_ptr[load_resources]:
  `lookup_var ip sf'' = lookup_var ip sf' /\ FLOOKUP Gf'' ip = FLOOKUP Gf' ip /\
   op_taint tnf'' (Var ip) = op_taint tnf' (Var ip)` by metis_tac[] >>
  simp[ptr_covers_def] >>
  qpat_x_assum `ptr_covers Gf' tnf' ip sf' 32` mp_tac >>
  simp[ptr_covers_def]
QED

Resume compile_abi_encode_singleton_bytes_ambient_counted_ptr[path]:
  irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
  qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[] >>
  irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
  qexistsl_tac [`Gf'`, `sf'`, `tnf'`] >> simp[] >>
  irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
  qexistsl_tac [`Gf''`, `sf''`, `tnf''`] >> simp[]
QED

Resume compile_abi_encode_singleton_bytes_ambient_counted_ptr[endpoint]:
  `not_fresh_at se dst` by metis_tac[] >>
  `lookup_var dst sf''' = lookup_var dst sf' /\ FLOOKUP Gf''' dst = FLOOKUP Gf' dst /\
   op_taint tnf''' (Var dst) = op_taint tnf' (Var dst)` by metis_tac[] >>
  `ptr_covers Gf''' tnf''' dst sf''' (64+ceil32 (LENGTH bs))` by
    (simp[ptr_covers_def] >>
     qpat_x_assum `ptr_covers Gf' tnf' dst sf' _` mp_tac >> simp[ptr_covers_def]) >>
  simp[eval_operand_def] >> rpt strip_tac >> metis_tac[]
QED

Finalise compile_abi_encode_singleton_bytes_ambient_counted_ptr

Theorem compile_abi_encode_singleton_bytes_counted_ptr:
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
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) a cap mem') ==>
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
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_abi_encode_singleton_bytes_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[]
QED
