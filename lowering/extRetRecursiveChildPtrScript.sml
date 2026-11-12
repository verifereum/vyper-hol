Theory extRetRecursiveChildPtr
Ancestors
  extRetRecursiveResourcePtr extRetRecursiveFramePtr extRetScratchResourcePtr
  extRetAbiChildBoundaryPtr extRetAbiChildComposePtr
  abiEncoderChildCode fragGasPathPtr fragExec compileEnv emitHelper
  bodyPtrDefs ptrDiscipline venomState venomMemDefs words finite_map pred_set
  arithmetic list wordLoadStorePtr abiEncoderChildContext extRetBulkCopyCountedPtr
  fragGasSeqPtr

(* The envelope is taken at the child endpoint, where new scratch spans
   have been registered.  No fixed entry-state scratch footprint is used. *)
Theorem encoder_child_protected_cursor:
  encoder_resource ctx fn children q len protected sf /\
  MEM (id,cursor,32) protected /\
  venomMemDefs$regions_disjoint (cursor,32) (dst,cap) /\
  mem_agree_outside (encoder_write_envelope children sf dst cap)
    sf.vs_memory s.vs_memory /\
  (!i. i NOTIN encoder_write_envelope children sf dst cap ==>
    (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
  (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tn.t_mem) ==>
  mload cursor sf = mload cursor s /\
  (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >>
  `!i. cursor <= i /\ i < cursor+32 ==>
    i NOTIN encoder_write_envelope children sf dst cap` by
    (metis_tac[encoder_envelope_protected]) >>
  irule encoder_frame_clean_word >>
  qexistsl_tac [`tn`, `encoder_write_envelope children sf dst cap`] >> simp[]
QED

(* Restoring the parent resource needs the parent's source scratch fact,
   not merely restriction of a child resource. *)
Theorem encoder_child_resource_restore:
  encoder_resource ctx fn sites q len protected s /\
  scratch_resource ctx fn sites q len sf /\
  (!id b n. FLOOKUP s.vs_allocas id = SOME (b,n) ==>
    FLOOKUP sf.vs_allocas id = SOME (b,n)) ==>
  encoder_resource ctx fn sites q len protected sf
Proof
  strip_tac >> irule encoder_resource_registered_intro >> simp[] >>
  fs[encoder_resource_def] >> metis_tac[]
QED

Theorem encoder_child_envelope_subset:
  children SUBSET sites /\ k+child_cap <= cap ==>
  encoder_write_envelope children sf (b+k) child_cap SUBSET
    encoder_write_envelope sites sf b cap
Proof
  simp[encoder_write_envelope_def, encoder_scratch_span_def, SUBSET_DEF] >>
  rpt strip_tac >- (disj1_tac >> decide_tac) >>
  disj2_tac >> metis_tac[]
QED

(* The child may allocate only at its own sites.  This is the missing
   direction of resource restriction: old parent-only records remain exact. *)
Theorem encoder_child_scratch_restore:
  scratch_resource ctx fn sites q len s /\
  scratch_resource ctx fn children q len sf /\
  s.vs_alloca_next <= sf.vs_alloca_next /\
  (!id. id NOTIN children ==>
    FLOOKUP sf.vs_allocas id = FLOOKUP s.vs_allocas id) ==>
  scratch_resource ctx fn sites q len sf
Proof
  metis_tac[scratch_resource_def]
QED

Theorem encoder_child_prefix_resource_counted_ptr:
  abi_encode_child_prefix (Var dst) h (Var ip) sa =
    ((Var head,Var off,Var child),sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa ip /\ not_fresh_at sa dst /\
  lookup_var dst s = SOME (n2w b) /\ b+cap < dimword(:256) /\
  ptr_covers G tn dst s cap /\ h+32 <= cap /\ k <= cap /\
  lookup_var ip s = SOME (n2w cursor) /\ cursor < dimword(:256) /\
  ptr_covers G tn ip s 32 /\ mload cursor s = n2w k /\
  (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tn.t_mem) /\
  encoder_resource ctx fn sites q source_len protected s /\
  children SUBSET sites /\ id NOTIN children /\
  FLOOKUP s.vs_allocas id = SOME (cursor,32) ==>
  ?Gp tnp sp.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gp tnp (OK sp) /\
    sp.vs_current_bb = sb.cs_current_bb /\
    sp.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sp.vs_halted /\
    lookup_var head sp = SOME (n2w (b+h)) /\ ptr_covers Gp tnp head sp 32 /\
    lookup_var off sp = SOME (n2w k) /\ op_taint tnp (Var off) = {} /\
    lookup_var child sp = SOME (n2w (b+k)) /\ ptr_covers Gp tnp child sp (cap-k) /\
    encoder_resource ctx fn sites q source_len protected sp /\
    encoder_resource ctx fn children q source_len ((id,cursor,32)::protected) sp /\
    sp.vs_allocas = s.vs_allocas /\ sp.vs_alloca_next = s.vs_alloca_next /\
    sp.vs_memory = s.vs_memory /\ tnp.t_mem = tn.t_mem /\
    tnp.t_imm = tn.t_imm /\ sp.vs_accounts = s.vs_accounts /\
    sp.vs_transient = s.vs_transient /\ sp.vs_call_ctx = s.vs_call_ctx /\
    tnp.t_stor = tn.t_stor /\ tnp.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sp = lookup_var v s /\ FLOOKUP Gp v = FLOOKUP G v /\
      op_taint tnp (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule_all abi_child_prefix_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `encoder_resource ctx fn sites q source_len protected sf` by
    (irule encoder_resource_fields >> qexists_tac `s` >> simp[]) >>
  `encoder_resource ctx fn children q source_len ((id,cursor,32)::protected) sf` by
    (irule encoder_resource_push >> simp[] >> qexists_tac `sites` >> simp[]) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[]
QED

Theorem encoder_child_suffix_resource_counted_ptr:
  abi_encode_child_suffix (Var head) (Var ip) (Var off) len sa = (len,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa head /\ not_fresh_at sa ip /\
  lookup_var head s = SOME (n2w (b+h)) /\ b+h < dimword(:256) /\
  ptr_covers G tn head s 32 /\
  lookup_var ip s = SOME (n2w cursor) /\ cursor < dimword(:256) /\
  ptr_covers G tn ip s 32 /\
  lookup_var off s = SOME (n2w k) /\ op_taint tn (Var off) = {} /\
  eval_operand len s = SOME (n2w n) /\ op_taint tn len = {} /\
  k+n < dimword(:256) /\ h+32 <= k /\ k+n <= cap /\
  (n = 0 \/ cursor+32 <= b+k \/ b+k+n <= cursor) /\
  (!i. b+k <= i /\ i < b+k+n ==> i NOTIN tn.t_mem) /\
  encoder_resource ctx fn sites q source_len protected s /\
  id IN sites /\ FLOOKUP s.vs_allocas id = SOME (cursor,32) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    mload cursor sf = n2w (k+n) /\
    (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tnf.t_mem) /\
    (!i. b+k <= i /\ i < b+k+n ==> i NOTIN tnf.t_mem) /\
    (!i. b+h <= i /\ i < b+h+32 ==> i NOTIN tnf.t_mem) /\
    encoder_resource ctx fn sites q source_len protected sf /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    mem_agree_outside (encoder_write_envelope sites sf b cap)
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN encoder_write_envelope sites sf b cap ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule_all abi_child_suffix_operand_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `encoder_resource ctx fn sites q source_len protected sf` by
    (irule encoder_resource_fields >> qexists_tac `s` >> simp[]) >>
  `mload cursor sf = n2w (k+n) /\
   (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tnf.t_mem)` by
    (irule abi_child_suffix_cursor_clean >> simp[] >>
     qexistsl_tac [`b+h`, `s`, `tn`] >> simp[]) >>
  `!i. cursor <= i /\ i < cursor+32 ==>
    i IN encoder_write_envelope sites sf b cap` by
    (simp[encoder_write_envelope_def, encoder_scratch_span_def] >>
     metis_tac[]) >>
  `mem_agree_outside (encoder_write_envelope sites sf b cap)
    sf.vs_memory s.vs_memory` by
    (qspecl_then [`s`, `b+h`, `n2w k`] mp_tac mstore_memory_frame >>
     qspecl_then [`mstore (b+h) (n2w k) s`, `cursor`, `n2w (k+n)`]
       mp_tac mstore_memory_frame >>
     strip_tac >> strip_tac >>
     irule encoder_memory_frame_mono >>
     qexists_tac `{i | b+h <= i /\ i < b+h+32} UNION
       {i | cursor <= i /\ i < cursor+32}` >>
     conj_tac >-
       (simp[SUBSET_DEF] >> rpt strip_tac >-
         (simp[encoder_write_envelope_def] >> disj1_tac >> decide_tac) >>
        metis_tac[]) >>
     irule encoder_memory_frame_union >> metis_tac[]) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
  rpt conj_tac >> rpt strip_tac >> gvs[] >>
  fs[encoder_write_envelope_def] >> metis_tac[]
QED

Theorem encoder_static_child_resource_counted_ptr:
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
    ?Gm tnm sm.
      gas_path_ptr D 0 ctx fn PG Gp tnp sp cost Gm tnm (OK sm) /\
      sm.vs_current_bb = sb.cs_current_bb /\
      sm.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sm.vs_halted /\
      eval_operand out sm = SOME (n2w n) /\ op_taint tnm out = {} /\
      (!i. b+h <= i /\ i < b+h+n ==> i NOTIN tnm.t_mem) /\
      encoder_resource ctx fn children q source_len protected sm /\
      mem_agree_outside (encoder_write_envelope children sm (b+h) child_cap)
        sm.vs_memory sp.vs_memory /\
      (!i. i NOTIN encoder_write_envelope children sm (b+h) child_cap ==>
        (i IN tnm.t_mem <=> i IN tnp.t_mem)) /\
      sp.vs_alloca_next <= sm.vs_alloca_next /\
      (!id b sz. FLOOKUP sp.vs_allocas id = SOME (b,sz) ==>
        FLOOKUP sm.vs_allocas id = SOME (b,sz)) /\
      (!id. id NOTIN children ==> FLOOKUP sm.vs_allocas id = FLOOKUP sp.vs_allocas id) /\
      (!v. not_fresh_at sc v ==>
        lookup_var v sm = lookup_var v sp /\ FLOOKUP Gm v = FLOOKUP Gp v /\
        op_taint tnm (Var v) = op_taint tnp (Var v))) ==>
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
      op_taint tnf (Var v) = op_taint tn (Var v))
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
  simp[] >> conj_tac >-
    (irule encoder_memory_frame_mono >> metis_tac[]) >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem encoder_child_resource_counted_ptr:
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
    ?Gm tnm sm.
      gas_path_ptr D 0 ctx fn PG Gp tnp sp cost Gm tnm (OK sm) /\
      sm.vs_current_bb = sd.cs_current_bb /\
      sm.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~sm.vs_halted /\
      eval_operand len sm = SOME (n2w n) /\ op_taint tnm len = {} /\
      (!i. b+k <= i /\ i < b+k+n ==> i NOTIN tnm.t_mem) /\
      encoder_resource ctx fn children q source_len ((id,cursor,32)::protected) sm /\
      mem_agree_outside (encoder_write_envelope children sm (b+k) child_cap)
        sm.vs_memory sp.vs_memory /\
      (!i. i NOTIN encoder_write_envelope children sm (b+k) child_cap ==>
        (i IN tnm.t_mem <=> i IN tnp.t_mem)) /\
      sp.vs_alloca_next <= sm.vs_alloca_next /\
      (!aid p sz. FLOOKUP sp.vs_allocas aid = SOME (p,sz) ==>
        FLOOKUP sm.vs_allocas aid = SOME (p,sz)) /\
      (!aid. aid NOTIN children ==> FLOOKUP sm.vs_allocas aid = FLOOKUP sp.vs_allocas aid) /\
      (!v. not_fresh_at sc v ==>
        lookup_var v sm = lookup_var v sp /\ FLOOKUP Gm v = FLOOKUP Gp v /\
        op_taint tnm (Var v) = op_taint tnp (Var v))) ==>
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
      op_taint tnf (Var v) = op_taint tn (Var v))
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
  simp[] >> conj_tac >-
    (fs[mem_agree_outside_def, SUBSET_DEF] >> metis_tac[]) >>
  fs[SUBSET_DEF] >> metis_tac[]
QED
