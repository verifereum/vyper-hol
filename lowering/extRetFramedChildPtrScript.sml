Theory extRetFramedChildPtr
Ancestors
  extRetRecursiveChildPtr extRetRecursiveResourcePtr extRetRecursiveFramePtr
  fragGasPathPtr fragExec compileEnv bodyPtrDefs ptrDiscipline venomState
  venomMemDefs words finite_map pred_set arithmetic list
  abiEncoderChildContext extRetBulkCopyCountedPtr extRetScratchResourcePtr
  emitHelper abiEncoderChildCode fragGasSeqPtr extRetAbiChildComposePtr

Definition encoder_ambient_frame_def:
  encoder_ambient_frame tn s tnf sf <=>
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans
End

Definition encoder_framed_child_result_def:
  encoder_framed_child_result D ctx fn PG sa sb sites q source_len protected
    b cap out n cost G tn s Gf tnf sf <=>
    gas_path_ptr D 0 ctx fn PG G tn s cost Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (n2w n) /\ op_taint tnf out = {} /\
    (!i. b <= i /\ i < b+n ==> i NOTIN tnf.t_mem) /\
    encoder_resource ctx fn sites q source_len protected sf /\
    mem_agree_outside (encoder_write_envelope sites sf b cap)
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN encoder_write_envelope sites sf b cap ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    s.vs_alloca_next <= sf.vs_alloca_next /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP sf.vs_allocas aid = SOME (p,sz)) /\
    (!aid. aid NOTIN sites ==> FLOOKUP sf.vs_allocas aid = FLOOKUP s.vs_allocas aid) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    encoder_ambient_frame tn s tnf sf
End

Theorem encoder_ambient_frame_refl:
  encoder_ambient_frame tn s tn s
Proof
  simp[encoder_ambient_frame_def]
QED

Theorem encoder_ambient_frame_trans:
  encoder_ambient_frame tn s tnm sm /\ encoder_ambient_frame tnm sm tnf sf ==>
  encoder_ambient_frame tn s tnf sf
Proof
  simp[encoder_ambient_frame_def]
QED

Theorem encoder_framed_child_result_path:
  encoder_framed_child_result D ctx fn PG sa sb sites q source_len protected
    b cap out n cost G tn s Gf tnf sf ==>
  gas_path_ptr D 0 ctx fn PG G tn s cost Gf tnf (OK sf)
Proof
  simp[encoder_framed_child_result_def]
QED

Theorem encoder_framed_child_result_ambient:
  encoder_framed_child_result D ctx fn PG sa sb sites q source_len protected
    b cap out n cost G tn s Gf tnf sf ==>
  encoder_ambient_frame tn s tnf sf
Proof
  simp[encoder_framed_child_result_def]
QED

Theorem encoder_framed_child_result_identity:
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand out s = SOME (n2w n) /\ op_taint tn out = {} /\
  (!i. b <= i /\ i < b+n ==> i NOTIN tn.t_mem) /\
  encoder_resource ctx fn sites q source_len protected s ==>
  encoder_framed_child_result D ctx fn PG sa sa sites q source_len protected
    b cap out n 0 G tn s G tn s
Proof
  simp[encoder_framed_child_result_def, encoder_ambient_frame_def,
    mem_agree_outside_def, gas_path_ptr_rules]
QED

Theorem encoder_static_child_framed_counted_ptr:
  compile_abi_encode_child (Var dst) src ei F h dp sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ lookup_var dst s = SOME (n2w b) /\
  ptr_covers G tn dst s cap /\ b+cap < dimword(:256) /\
  h+child_cap <= cap /\ children SUBSET sites /\
  encoder_resource ctx fn sites q source_len protected s /\
  (!head sc Gp tnp sp.
    emit_op ADD [Var dst; Lit (n2w h)] sa = (Var head,sc) /\
    compile_abi_encode_to_buf (Var head) src ei sc = (out,sb) /\
    sp.vs_current_bb = sc.cs_current_bb /\
    sp.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~sp.vs_halted /\
    lookup_var head sp = SOME (n2w (b+h)) /\ ptr_covers Gp tnp head sp child_cap /\
    encoder_resource ctx fn children q source_len protected sp /\
    sp.vs_memory = s.vs_memory /\ tnp.t_mem = tn.t_mem ==>
    ?Gm tnm sm. encoder_framed_child_result D ctx fn PG sc sb children q
      source_len protected (b+h) child_cap out n cost Gp tnp sp Gm tnm sm) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s cost Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (n2w n) /\ op_taint tnf out = {} /\
    (!i. b+h <= i /\ i < b+h+n ==> i NOTIN tnf.t_mem) /\
    encoder_resource ctx fn sites q source_len protected sf /\
    mem_agree_outside (encoder_write_envelope sites sf b cap) sf.vs_memory s.vs_memory /\
    (!i. i NOTIN encoder_write_envelope sites sf b cap ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    s.vs_alloca_next <= sf.vs_alloca_next /\
    (!id b sz. FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
      FLOOKUP sf.vs_allocas id = SOME (b,sz)) /\
    (!id. id NOTIN children ==> FLOOKUP sf.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    encoder_ambient_frame tn s tnf sf
Proof
  strip_tac >> drule_all abi_encoder_static_child_structural_context >> strip_tac >>
  `?hv. head = Var hv` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, emit_def, comp_return_def] >> gvs[] >>
  `w2n (n2w b : bytes32)+h < dimword(:256)` by
    (simp[w2n_n2w, LESS_MOD] >> decide_tac) >>
  `h+child_cap <= cap` by decide_tac >>
  drule_all (emit_bulk_offset_ambient_counted_ptr |> SPEC_ALL |>
    Q.INST [`n` |-> `child_cap`, `extent` |-> `cap`]) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `encoder_resource ctx fn sites q source_len protected sf` by
    (irule encoder_resource_fields >> qexists_tac `s` >> simp[]) >>
  `encoder_resource ctx fn children q source_len protected sf` by
    (irule encoder_resource_restrict >> qexists_tac `sites` >> simp[]) >>
  qpat_x_assum `!Gp tnp sp. _`
    (qspecl_then [`Gf`, `tnf`, `sf`] mp_tac) >>
  impl_tac >- (simp[w2n_n2w, LESS_MOD] >> metis_tac[]) >> strip_tac >>
  fs[encoder_framed_child_result_def, encoder_ambient_frame_def] >>
  `scratch_resource ctx fn sites q source_len sm` by
    (irule encoder_child_scratch_restore >>
     qexistsl_tac [`children`, `sf`] >> fs[encoder_resource_def]) >>
  `encoder_resource ctx fn sites q source_len protected sm` by
    (irule encoder_child_resource_restore >> simp[] >> qexists_tac `sf` >> simp[]) >>
  `encoder_write_envelope children sm (b+h) child_cap SUBSET
    encoder_write_envelope sites sm b cap` by
    (irule encoder_child_envelope_subset >> simp[]) >>
  `!v. not_fresh_at sa v ==> not_fresh_at prepared v` by
    (gvs[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  qexistsl_tac [`Gm`, `tnm`, `sm`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[]) >>
  simp[encoder_ambient_frame_def] >> conj_tac >-
    (irule encoder_memory_frame_mono >> metis_tac[]) >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem encoder_dynamic_child_framed_counted_ptr:
  compile_abi_encode_child (Var dst) src ei T h (Var ip) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa ip /\ not_fresh_at sa dst /\
  lookup_var dst s = SOME (n2w b) /\ b+cap < dimword(:256) /\
  ptr_covers G tn dst s cap /\ h+32 <= k /\ k+child_cap <= cap /\ n <= child_cap /\
  lookup_var ip s = SOME (n2w cursor) /\ cursor < dimword(:256) /\
  ptr_covers G tn ip s 32 /\ mload cursor s = n2w k /\
  (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tn.t_mem) /\
  venomMemDefs$regions_disjoint (cursor,32) (b+k,child_cap) /\
  encoder_resource ctx fn sites q source_len protected s /\
  children SUBSET sites /\ id IN sites /\ id NOTIN children /\
  FLOOKUP s.vs_allocas id = SOME (cursor,32) /\
  (!head off child sc len sd Gp tnp sp.
    abi_encode_child_prefix (Var dst) h (Var ip) sa =
      ((Var head,Var off,Var child),sc) /\
    compile_abi_encode_to_buf (Var child) src ei sc = (len,sd) /\
    sp.vs_current_bb = sc.cs_current_bb /\
    sp.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~sp.vs_halted /\
    lookup_var head sp = SOME (n2w (b+h)) /\ ptr_covers Gp tnp head sp 32 /\
    lookup_var off sp = SOME (n2w k) /\ op_taint tnp (Var off) = {} /\
    lookup_var child sp = SOME (n2w (b+k)) /\ ptr_covers Gp tnp child sp (cap-k) /\
    encoder_resource ctx fn children q source_len ((id,cursor,32)::protected) sp /\
    sp.vs_memory = s.vs_memory /\ tnp.t_mem = tn.t_mem ==>
    ?Gm tnm sm. encoder_framed_child_result D ctx fn PG sc sd children q
      source_len ((id,cursor,32)::protected) (b+k) child_cap len n cost
      Gp tnp sp Gm tnm sm) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s cost Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    mload cursor sf = n2w (k+n) /\
    (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tnf.t_mem) /\
    (!i. b+k <= i /\ i < b+k+n ==> i NOTIN tnf.t_mem) /\
    (!i. b+h <= i /\ i < b+h+32 ==> i NOTIN tnf.t_mem) /\
    encoder_resource ctx fn sites q source_len protected sf /\
    mem_agree_outside (encoder_write_envelope sites sf b cap) sf.vs_memory s.vs_memory /\
    (!i. i NOTIN encoder_write_envelope sites sf b cap ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    s.vs_alloca_next <= sf.vs_alloca_next /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP sf.vs_allocas aid = SOME (p,sz)) /\
    (!aid. aid NOTIN children ==> FLOOKUP sf.vs_allocas aid = FLOOKUP s.vs_allocas aid) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    encoder_ambient_frame tn s tnf sf
Proof
  strip_tac >> drule_all abi_encoder_dynamic_child_context >> strip_tac >>
  `?head off child. ops = (Var head,Var off,Var child) /\
    not_fresh_at prepared head /\ not_fresh_at prepared off /\
    not_fresh_at prepared child` by
    (qpat_x_assum `abi_encode_child_prefix _ _ _ _ = _` mp_tac >>
     simp[abi_encode_child_prefix_def, comp_bind_def, comp_return_def,
       emit_op_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     simp[not_fresh_at_def]) >> gnvs[] >>
  `h+32 <= cap /\ k <= cap` by decide_tac >>
  drule_all encoder_child_prefix_resource_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qpat_x_assum `!Gp tnp sp. _`
    (qspecl_then [`Gp`, `tnp`, `sp`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  fs[encoder_framed_child_result_def, encoder_ambient_frame_def] >>
  `scratch_resource ctx fn sites q source_len sm` by
    (irule encoder_child_scratch_restore >>
     qexistsl_tac [`children`, `sp`] >> fs[encoder_resource_def]) >>
  `encoder_resource ctx fn sites q source_len protected sm` by
    (irule encoder_child_resource_restore >> simp[] >> qexists_tac `sp` >> simp[]) >>
  `!v. not_fresh_at sa v ==> not_fresh_at prepared v` by
    (gvs[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `not_fresh_at child_end head /\ not_fresh_at child_end ip` by
    (gvs[not_fresh_at_def] >> decide_tac) >>
  `lookup_var head sm = SOME (n2w (b+h)) /\ ptr_covers Gm tnm head sm 32 /\
   lookup_var ip sm = SOME (n2w cursor) /\ ptr_covers Gm tnm ip sm 32 /\
   lookup_var off sm = SOME (n2w k) /\ op_taint tnm (Var off) = {}` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `k+n < dimword(:256) /\ k+n <= cap /\ b+h < dimword(:256)` by decide_tac >>
  Q.SUBGOAL_THEN `n = 0 \/ cursor+32 <= b+k \/ b+k+n <= cursor` assume_tac >-
    (fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  drule abi_encode_child_suffix_shape >> strip_tac >>
  qpat_x_assum `out = child_len` SUBST_ALL_TAC >>
  `FLOOKUP sm.vs_allocas id = SOME (cursor,32)` by metis_tac[] >>
  `!i. b+k <= i /\ i < b+k+n ==> i NOTIN tnm.t_mem` by
    (pure_rewrite_tac[GSYM ADD_ASSOC] >> first_assum ACCEPT_TAC) >>
  drule_all encoder_child_suffix_resource_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gp`, `sp`, `tnp`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gm`, `sm`, `tnm`] >> simp[]) >>
  `encoder_write_envelope children sm (b+k) child_cap SUBSET
    encoder_write_envelope sites sf b cap` by
    (`encoder_write_envelope sites sf b cap =
      encoder_write_envelope sites sm b cap` by
       simp[encoder_write_envelope_def, encoder_scratch_span_def] >>
     asm_rewrite_tac[] >> irule encoder_child_envelope_subset >> simp[]) >>
  `!v. not_fresh_at sa v ==> not_fresh_at child_end v` by
    (gvs[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  simp[encoder_ambient_frame_def] >> conj_tac >-
    (fs[mem_agree_outside_def, SUBSET_DEF] >> metis_tac[]) >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem encoder_envelope_registered_mono:
  (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
    FLOOKUP sf.vs_allocas aid = SOME (p,sz)) ==>
  encoder_write_envelope sites s b cap SUBSET encoder_write_envelope sites sf b cap
Proof
  simp[encoder_write_envelope_def, encoder_scratch_span_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem encoder_framed_child_result_then:
  encoder_framed_child_result D ctx fn PG sa sb sites q source_len protected
    b cap out1 n1 cost1 G tn s Gm tnm sm /\
  encoder_framed_child_result D ctx fn PG sb sc sites q source_len protected
    b cap out2 n2 cost2 Gm tnm sm Gf tnf sf /\
  (!v. not_fresh_at sa v ==> not_fresh_at sb v) ==>
  encoder_framed_child_result D ctx fn PG sa sc sites q source_len protected
    b cap out2 n2 (cost1+cost2) G tn s Gf tnf sf
Proof
  simp[encoder_framed_child_result_def] >> strip_tac >>
  `encoder_write_envelope sites sm b cap SUBSET
    encoder_write_envelope sites sf b cap` by
    (irule encoder_envelope_registered_mono >> simp[]) >>
  conj_tac >- (irule gas_path_ptr_then >> metis_tac[]) >>
  simp[] >> conj_tac >-
    (fs[mem_agree_outside_def, SUBSET_DEF] >> metis_tac[]) >>
  fs[SUBSET_DEF, encoder_ambient_frame_def] >> metis_tac[]
QED
