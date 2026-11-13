Theory extRetSemanticDynamicLoopPtr
Ancestors
  extRetDynamicLoopPtr extRetDynamicBodyPtr extRetRecursiveLayoutPtr
  extRetSemanticResultPtr extRetFramedChildPtr extRetRecursiveResourcePtr
  abiEncoderArrayHeader abiEncoderArrayBodyCode abiEncoderArrayTail
  abiEncoderChildCode abiDecoderLoopEmit abiEncoder compileEnv fragExec
  fragGasPathPtr bodyPtrDefs ptrDiscipline venomState valueEncoding
  vyperABI vyperTypeABI vyperTyping vyperValue words finite_map pred_set
  arithmetic list rich_list

(* The recursive premise is a semantic endpoint for the actual evaluated
   element, with an existential output length.  In particular it assumes
   neither an indexed target length nor execution of the loop body. *)
Theorem encoder_semantic_dynamic_inner_loop_counted_ptr:
  abi_encode_array_header (Var ip) (Var cv) sh = ((hdr,body_lbl,exit_lbl),sa) /\
  abi_encode_array_addresses (Var ip) (Var src) (Var dst) 32 msz sa =
    (((Var idx,Var child_src),(Var data,Var head)),sx) /\
  abi_encode_array_tail (Var data) (Var cursor) sx = ((Var off,Var child_dst),sb) /\
  compile_abi_encode_to_buf (Var child_dst) (Var child_src) ei sb = (len,se) /\
  abi_encode_child_suffix (Var head) (Var cursor) (Var off) len se = (len,ss) /\
  abi_decode_loop_suffix (Var ip) (Var idx) hdr exit_lbl ss = ((),sc) /\
  fn_has_code sh sa fn /\ fn_has_code sa sx fn /\ fn_has_code sx sb fn /\
  fn_has_code sb se fn /\ fn_has_code se ss fn /\ fn_has_code ss sc fn /\
  sa.cs_current_bb = body_lbl /\ sa.cs_current_insts = [] /\
  ~ctx_has_dalloca ctx /\
  not_fresh_at sh ip /\ not_fresh_at sh cursor /\ not_fresh_at sh src /\
  not_fresh_at sh dst /\ not_fresh_at sh cv /\
  not_fresh_at sa ip /\ not_fresh_at sa cursor /\ not_fresh_at sa src /\
  not_fresh_at sa dst /\ not_fresh_at sa cv /\
  not_fresh_at sb head /\ not_fresh_at sb off /\ not_fresh_at sb idx /\
  (!x. not_fresh_at sh x ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
  (!x. not_fresh_at sb x ==> not_fresh_at se x) /\
  (!x. not_fresh_at se x ==> not_fresh_at ss x) /\
  encoder_dynamic_loop_inv ctx fn sites protected
    ip cursor src dst cv p c a b scap dcap
    (ArrayTV tv (Dynamic limit)) (ArrayV (DynArrayV vs)) N ns 0 G tn s /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
  N = LENGTH vs /\ LENGTH ns = N /\ LENGTH avs = N /\ LENGTH costs = N /\
  evaluate_type env ty = SOME tv /\ msz = type_memory_size tv /\
  value_has_type (ArrayTV tv (Dynamic limit)) (ArrayV (DynArrayV vs)) /\
  (!i. i<N ==> vyper_to_abi env ty (EL i vs) = SOME (EL i avs) /\
    EL i ns = LENGTH (enc (vyper_to_abi_type env ty) (EL i avs))) /\
  N < dimword(:256) /\ 32+32*N+SUM ns <= dcap /\
  val_wf (ArrayTV tv (Dynamic limit)) (ArrayV (DynArrayV vs)) /\
  val_footprint (ArrayTV tv (Dynamic limit)) (ArrayV (DynArrayV vs)) <= scap /\
  regions_disjoint (p,32) (c,32) /\
  regions_disjoint (p,32) (b,dcap) /\ regions_disjoint (c,32) (b,dcap) /\
  regions_disjoint (a,scap) (p,32) /\ regions_disjoint (a,scap) (c,32) /\
  regions_disjoint (a,scap) (b,dcap) /\
  FLOOKUP s.vs_allocas pid = SOME (p,32) /\ pid IN sites /\ pid NOTIN children /\
  FLOOKUP s.vs_allocas cid = SOME (c,32) /\ cid IN sites /\ cid NOTIN children /\
  MEM (did,dbase,dsize) protected /\ dbase <= b /\ b+dcap <= dbase+dsize /\
  children SUBSET sites /\
  p+32 < dimword(:256) /\ c+32 < dimword(:256) /\
  a+scap < dimword(:256) /\ b+dcap < dimword(:256) /\
  (!i. i<N ==> EL i ns <= cap i /\
    32+(32*N+SUM (TAKE i ns))+cap i <= dcap /\ 32+i*msz+msz <= scap) /\
  (!i Gp tnp sp. i<N /\
    sp.vs_current_bb = sb.cs_current_bb /\
    sp.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sp.vs_halted /\
    lookup_var child_src sp = SOME (n2w (a+32+i*msz)) /\
    ptr_covers Gp tnp child_src sp msz /\
    lookup_var child_dst sp = SOME (n2w (b+32+(32*N+SUM (TAKE i ns)))) /\
    ptr_covers Gp tnp child_dst sp (cap i) /\
    (!mem. mem_agree_outside tnp.t_mem sp.vs_memory mem ==>
      val_in_memory tv (EL i vs) (a+32+i*msz) mem) /\
    encoder_resource ctx fn children a scap
      ((pid,p,32)::(cid,c,32)::protected) sp ==>
    ?n Gm tnm sm. encoder_semantic_framed_result env ty (EL i vs)
      D ctx fn PG sb se children a scap
      ((pid,p,32)::(cid,c,32)::protected) (b+32+(32*N+SUM (TAKE i ns)))
      (cap i) len n (EL i costs) Gp tnp sp Gm tnm sm) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s (SUM costs) Gf tnf (OK sf) /\
    sf.vs_current_bb = exit_lbl /\ sf.vs_inst_idx = 0 /\
    encoder_dynamic_loop_inv ctx fn sites protected
      ip cursor src dst cv p c a b scap dcap
      (ArrayTV tv (Dynamic limit)) (ArrayV (DynArrayV vs)) N ns N Gf tnf sf /\
    mload c sf = n2w (32*N+SUM ns) /\
    encoder_dynamic_effect sh sites b dcap G tn s Gf tnf sf /\
    (!i. b <= i /\ i < b+32 ==> (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  `!i Gp tnp sp. i<N /\
    sp.vs_current_bb = sb.cs_current_bb /\
    sp.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sp.vs_halted /\
    lookup_var child_src sp = SOME (n2w (a+32+i*msz)) /\
    ptr_covers Gp tnp child_src sp msz /\
    lookup_var child_dst sp = SOME (n2w (b+32+(32*N+SUM (TAKE i ns)))) /\
    ptr_covers Gp tnp child_dst sp (cap i) /\
    (!mem. mem_agree_outside tnp.t_mem sp.vs_memory mem ==>
      val_in_memory (ArrayTV tv (Dynamic limit)) (ArrayV (DynArrayV vs)) a mem) /\
    encoder_resource ctx fn children a scap
      ((pid,p,32)::(cid,c,32)::protected) sp ==>
    ?Gm tnm sm. encoder_framed_child_result D ctx fn PG sb se children a scap
      ((pid,p,32)::(cid,c,32)::protected) (b+32+(32*N+SUM (TAKE i ns)))
      (cap i) len (EL i ns) (EL i costs) Gp tnp sp Gm tnm sm` by
    (rpt gen_tac >> strip_tac >>
     `!mem. mem_agree_outside tnp.t_mem sp.vs_memory mem ==>
        val_in_memory tv (EL i vs) (a+32+i*msz) mem` by
       (metis_tac[encoder_dynamic_source_window]) >>
     qpat_x_assum `!i Gp tnp sp. _` (qspecl_then [`i`,`Gp`,`tnp`,`sp`] mp_tac) >>
     (impl_tac >- simp[]) >>
     strip_tac >>
     gvs[encoder_semantic_framed_result_def] >>
     metis_tac[]) >>
  mp_tac (encoder_dynamic_inner_loop_counted_ptr |>
    Q.INST [`tv` |-> `ArrayTV tv (Dynamic limit)`,
            `v` |-> `ArrayV (DynArrayV vs)`] |>
    Q.SPECL [`N`,`0`,`G`,`tn`,`s`]) >>
  (impl_tac >- asm_simp_tac bool_ss [ADD_CLAUSES]) >>
  pure_rewrite_tac[DROP_0] >> strip_tac >>
  qexistsl [`Gf`,`tnf`,`sf`] >> simp[] >>
  drule_all encoder_dynamic_loop_completed_prefixes >> simp[]
QED
