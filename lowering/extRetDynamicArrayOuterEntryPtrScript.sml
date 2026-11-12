Theory extRetDynamicArrayOuterEntryPtr
Ancestors
  extRetSemanticDynamicArrayPtr extRetDynamicArrayInitFramePtr
  extRetDynamicArrayPhasePtr extRetDynamicArrayCountPtr extRetDynamicBodyPtr
  extRetDynamicArrayEntryPtr extRetRecursiveFramePtr
  extRetRecursiveResourcePtr extRetFramedChildPtr extRetScratchResourcePtr
  abiEncoderArrayPhases abiEncoderArrayContext abiDecoderIndexInit
  abiEncoderArrayCode abiEncoderArrayHeader abiEncoder
  emitHelperProps exprLoweringProps compileEnv emitHelper fragExec
  bodyPtrDefs ptrDiscipline venomState venomMemDefs venomMemProps
  robustCopyTransportPtr valueEncoding words finite_map pred_set arithmetic list

Theorem encoder_dynamic_outer_prefix_trace[local]:
  abi_encode_array_prefix src dst si = (ops,sl) ==>
  ?buf s0 s1 s2 cv.
    compile_alloc_buffer 32 si = (buf,s0) /\
    emit_void MSTORE [buf.buf_operand;Lit 0w] s0 = ((),s1) /\
    emit_op MLOAD [src] s1 = (cv,s2) /\
    emit_void MSTORE [dst;cv] s2 = ((),sl) /\
    ops = (buf.buf_operand,cv)
Proof
  simp_tac bool_ss [abi_encode_array_prefix_def, abi_decode_index_init_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

(* Allocate the outer cursor using the original sites, then remove it from
   the loop's writable sites and register it as an ancestor cell. *)
Theorem encoder_dynamic_parent_init_counted_ptr:
  compile_alloc_buffer 32 si = (buf,s0) /\
  emit_void MSTORE [buf.buf_operand;Lit 0w] s0 = ((),s1) /\
  fn_has_code si s1 fn /\ s.vs_current_bb = si.cs_current_bb /\
  s.vs_inst_idx = LENGTH si.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ encoder_resource ctx fn sites a scap protected s /\
  si.cs_next_id IN sites ==>
  ?parent r Gf tnf sf.
    buf.buf_operand = Var parent /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = s1.cs_current_bb /\
    sf.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var parent sf = SOME (n2w r) /\ ptr_covers Gf tnf parent sf 32 /\
    r+32 < dimword(:256) /\ mload r sf = 0w /\
    (!i. r <= i /\ i < r+32 ==> i NOTIN tnf.t_mem) /\
    FLOOKUP sf.vs_allocas si.cs_next_id = SOME (r,32) /\
    encoder_resource ctx fn (sites DELETE si.cs_next_id) a scap
      ((si.cs_next_id,r,32)::protected) sf /\
    encoder_dynamic_effect si sites b dcap G tn s Gf tnf sf /\
    sf.vs_memory = (mstore r 0w s).vs_memory /\
    mem_agree_outside {i | r <= i /\ i < r+32} sf.vs_memory s.vs_memory /\
    (!i. i < r \/ r+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!v. not_fresh_at si v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    encoder_ambient_frame tn s tnf sf /\
    (!aid. aid <> si.cs_next_id ==>
      FLOOKUP sf.vs_allocas aid = FLOOKUP s.vs_allocas aid)
Proof
  strip_tac >>
  `scratch_resource ctx fn sites a scap s` by
    metis_tac[encoder_resource_def] >>
  `eval_operand (Lit 0w) s = SOME 0w /\ op_taint tn (Lit 0w) = {} /\
   (!v. Lit 0w = Var v ==> not_fresh_at si v)` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all encoder_scratch_word_exact_counted_ptr >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  `encoder_resource ctx fn sites a scap protected sf` by
    (irule encoder_resource_registered_intro >> simp[] >>
     rpt strip_tac >>
     qpat_assum `encoder_resource ctx fn sites a scap protected s` mp_tac >>
     pure_rewrite_tac [encoder_resource_def] >> strip_tac >>
     first_x_assum drule >> strip_tac >> simp[] >> metis_tac[]) >>
  `encoder_resource ctx fn (sites DELETE si.cs_next_id) a scap
     ((si.cs_next_id,addr,32)::protected) sf` by
    (irule encoder_resource_push >> simp[] >> qexists_tac `sites` >> simp[]) >>
  `encoder_dynamic_effect si sites b dcap G tn s Gf tnf sf` by
    (irule encoder_dynamic_effect_from_footprint >> simp[] >>
     conj_tac >- (rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
     qexists_tac `{i | addr <= i /\ i < addr+32}` >>
     simp[SUBSET_DEF, encoder_write_envelope_def, encoder_scratch_span_def] >>
     conj_tac >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
     reverse conj_tac >- metis_tac[] >>
     rpt strip_tac >> disj2_tac >>
     qexistsl [`si.cs_next_id`,`addr`,`32`] >> simp[]) >>
  qexistsl [`ip`,`addr`,`Gf`,`tnf`,`sf`] >> simp[] >>
  gvs[]
QED
