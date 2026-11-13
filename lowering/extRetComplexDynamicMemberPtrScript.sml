Theory extRetComplexDynamicMemberPtr
Ancestors
  extRetComplexMemberStatePtr extRetSemanticResultPtr
  extRetChildNarrowFramePtr extRetDynamicBodyPtr extRetRecursiveResourcePtr
  extRetRecursiveFramePtr extRetFramedChildPtr extRetRecursiveChildPtr
  extRetScratchResourcePtr abiEncoderChildContext abiEncoderChildCode
  abiEncoderMemberCode emitHelper fragGasSeqPtr fragGasPathPtr
  abiEncoderInput bodyPtrDefs compileEnv loweringStateRelDefs fragExec
  vyperABI vyperTypeABI vyperTyping vyperValue venomState venomMemDefs
  ptrDiscipline valueEncoding words finite_map pred_set list rich_list
  arithmetic

Theorem encoder_complex_dynamic_member_coordinates:
  encoder_complex_layout so ho ms hs tails dyn ns caps children
    sites a scap b dcap protected active cid cursor /\
  j < LENGTH ms /\ EL j dyn ==>
  active /\ EL j hs = 32 /\ EL j tails = EL j ns /\
  EL j ns <= caps j /\ children j SUBSET sites /\
  encoder_member_offset ho hs (j+1) = encoder_member_offset ho hs j + 32 /\
  encoder_member_offset (ho+SUM hs) tails (j+1) =
    encoder_member_offset (ho+SUM hs) tails j + EL j ns /\
  encoder_member_offset ho hs j + 32 <= ho+SUM hs /\
  ho+SUM hs <= encoder_member_offset (ho+SUM hs) tails j /\
  encoder_member_offset (ho+SUM hs) tails j + caps j <= dcap
Proof
  strip_tac >>
  `LENGTH hs = LENGTH ms /\ LENGTH tails = LENGTH ms /\
   LENGTH dyn = LENGTH ms /\ active = EXISTS I dyn /\
   EL j hs = 32 /\ EL j tails = EL j ns /\ EL j ns <= caps j /\
   children j SUBSET sites /\
   encoder_member_offset (ho+SUM hs) tails j + caps j <= dcap` by
    metis_tac[encoder_complex_layout_def] >>
  `active` by
    (fs[EXISTS_MEM] >> irule (iffRL MEM_EL) >> qexists_tac `j` >> simp[]) >>
  `SUM (TAKE j hs) + EL j hs <= SUM hs` by
    (mp_tac (Q.ISPECL [`\n:num. n`, `hs:num list`, `j:num`] abi_encoder_prefix_sum_bound) >> simp[]) >>
  `encoder_member_offset ho hs (j+1) = encoder_member_offset ho hs j + EL j hs /\
   encoder_member_offset (ho+SUM hs) tails (j+1) =
     encoder_member_offset (ho+SUM hs) tails j + EL j tails` by
    metis_tac[encoder_member_offset_step] >>
  fs[encoder_member_offset_def] >> decide_tac
QED

(* The actual three-instruction prefix also preserves the existing source
   operand. This strengthens the callback, not the recursive result. *)
Theorem encoder_dynamic_child_source_narrow_framed_counted_ptr[local]:
  compile_abi_encode_child (Var dst) src ei T h (Var ip) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa ip /\ not_fresh_at sa dst /\
  lookup_var dst s = SOME (n2w b) /\ b+cap < dimword(:256) /\
  ptr_covers G tn dst s cap /\ h+32 <= k /\ k+child_cap <= cap /\ n <= child_cap /\
  lookup_var ip s = SOME (n2w cursor) /\ cursor < dimword(:256) /\
  ptr_covers G tn ip s 32 /\ mload cursor s = n2w k /\
  (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tn.t_mem) /\
  regions_disjoint (cursor,32) (b+k,child_cap) /\
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
    sp.vs_memory = s.vs_memory /\ tnp.t_mem = tn.t_mem /\
    sp.vs_allocas = s.vs_allocas /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sp = lookup_var x s /\ FLOOKUP Gp x = FLOOKUP G x /\
      op_taint tnp (Var x) = op_taint tn (Var x)) ==>
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
    encoder_ambient_frame tn s tnf sf /\
    mem_agree_outside (encoder_write_envelope children sf (b+k) child_cap UNION
      {i | b+h <= i /\ i < b+h+32} UNION {i | cursor <= i /\ i < cursor+32})
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN (encoder_write_envelope children sf (b+k) child_cap UNION
      {i | b+h <= i /\ i < b+h+32} UNION {i | cursor <= i /\ i < cursor+32}) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem))
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
  (impl_tac >- simp[]) >> strip_tac >>
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
    (fs[regions_disjoint_def] >> decide_tac) >>
  drule abi_encode_child_suffix_shape >> strip_tac >>
  qpat_x_assum `out = child_len` SUBST_ALL_TAC >>
  `FLOOKUP sm.vs_allocas id = SOME (cursor,32)` by metis_tac[] >>
  `!i. b+k <= i /\ i < b+k+n ==> i NOTIN tnm.t_mem` by
    (pure_rewrite_tac[GSYM ADD_ASSOC] >> first_assum ACCEPT_TAC) >>
  drule_all encoder_child_suffix_narrow_resource_counted_ptr >>
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
  `encoder_write_envelope children sf (b+k) child_cap =
    encoder_write_envelope children sm (b+k) child_cap` by
    simp[encoder_write_envelope_def, encoder_scratch_span_def] >>
  `!v. not_fresh_at sa v ==> not_fresh_at child_end v` by
    (gvs[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  simp[encoder_ambient_frame_def] >> conj_tac >-
    (fs[mem_agree_outside_def, SUBSET_DEF] >> metis_tac[]) >>
  fs[mem_agree_outside_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem encoder_complex_dynamic_clean_prefixes:
  encoder_complex_layout so ho ms hs tails dyn ns caps children
    sites a scap b dcap protected active cid cursor /\
  j < LENGTH ms /\ EL j dyn /\
  encoder_resource ctx fn (children j) a scap protected sf /\
  (!i. i NOTIN (encoder_write_envelope (children j) sf
      (b+encoder_member_offset (ho+SUM hs) tails j) (caps j) UNION
      {x | b+encoder_member_offset ho hs j <= x /\ x < b+encoder_member_offset ho hs j+32} UNION
      {x | cursor <= x /\ x < cursor+32}) ==>
    (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
  (!i. b <= i /\ i < b+encoder_member_offset ho hs j ==> i NOTIN tn.t_mem) /\
  (!i. b+(ho+SUM hs) <= i /\
    i < b+encoder_member_offset (ho+SUM hs) tails j ==> i NOTIN tn.t_mem) /\
  (!i. b+encoder_member_offset ho hs j <= i /\
    i < b+encoder_member_offset ho hs j+32 ==> i NOTIN tnf.t_mem) /\
  (!i. b+encoder_member_offset (ho+SUM hs) tails j <= i /\
    i < b+encoder_member_offset (ho+SUM hs) tails j+EL j ns ==> i NOTIN tnf.t_mem) ==>
  (!i. b <= i /\ i < b+encoder_member_offset ho hs (j+1) ==> i NOTIN tnf.t_mem) /\
  (!i. b+(ho+SUM hs) <= i /\
    i < b+encoder_member_offset (ho+SUM hs) tails (j+1) ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >> drule_all encoder_complex_dynamic_member_coordinates >> strip_tac >>
  `?id p sz. MEM (id,p,sz) protected /\ p <= b /\ b+dcap <= p+sz` by
    metis_tac[encoder_complex_layout_def] >>
  `regions_disjoint (cursor,32) (b,dcap)` by
    metis_tac[encoder_complex_layout_def] >>
  `!i. b <= i /\ i < b+dcap ==>
    i NOTIN encoder_scratch_span (children j) sf /\
    ~(cursor <= i /\ i < cursor+32)` by
    (gen_tac >> strip_tac >> conj_tac
     >- (`p <= i /\ i < p+sz` by decide_tac >>
         metis_tac[encoder_complex_scratch_excludes_protected]) >>
     fs[regions_disjoint_def] >> decide_tac) >>
  `!i. (b <= i /\ i < b+encoder_member_offset ho hs j) \/
      (b+(ho+SUM hs) <= i /\ i < b+encoder_member_offset (ho+SUM hs) tails j) ==>
    i NOTIN (encoder_write_envelope (children j) sf
      (b+encoder_member_offset (ho+SUM hs) tails j) (caps j) UNION
      {x | b+encoder_member_offset ho hs j <= x /\ x < b+encoder_member_offset ho hs j+32} UNION
      {x | cursor <= x /\ x < cursor+32})` by
    (gen_tac >> strip_tac >>
     `b <= i /\ i < b+dcap` by decide_tac >>
     `i NOTIN encoder_scratch_span (children j) sf /\
      ~(cursor <= i /\ i < cursor+32)` by metis_tac[] >>
     simp[encoder_write_envelope_def] >> decide_tac) >>
  conj_tac
  >- (gen_tac >> strip_tac >> Cases_on `i < b+encoder_member_offset ho hs j`
      >- metis_tac[] >>
      `b+encoder_member_offset ho hs j <= i /\
       i < b+encoder_member_offset ho hs j+32` by decide_tac >> metis_tac[]) >>
  gen_tac >> strip_tac >> Cases_on `i < b+encoder_member_offset (ho+SUM hs) tails j`
  >- metis_tac[] >>
  `b+encoder_member_offset (ho+SUM hs) tails j <= i /\
   i < b+encoder_member_offset (ho+SUM hs) tails j+EL j ns` by decide_tac >> metis_tac[]
QED

Theorem encoder_complex_dynamic_invariant_advance:
  encoder_complex_layout so ho ms hs tails dyn ns caps children
    sites a scap b dcap protected active cid cursor /\
  j < LENGTH ms /\ EL j dyn /\
  encoder_complex_member_inv ctx fn sites protected src dst ip a b scap dcap
    active cid cursor so ho ms hs tails tv v j sa G tn s /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
  ~sf.vs_halted /\ encoder_resource ctx fn sites a scap protected sf /\
  encoder_dynamic_effect sa sites b dcap G tn s Gf tnf sf /\
  mload cursor sf = n2w (encoder_member_offset (ho+SUM hs) tails j+EL j ns) /\
  (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tnf.t_mem) /\
  (!i. i NOTIN (encoder_write_envelope (children j) sf
      (b+encoder_member_offset (ho+SUM hs) tails j) (caps j) UNION
      {x | b+encoder_member_offset ho hs j <= x /\ x < b+encoder_member_offset ho hs j+32} UNION
      {x | cursor <= x /\ x < cursor+32}) ==>
    (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
  (!i. b+encoder_member_offset ho hs j <= i /\
    i < b+encoder_member_offset ho hs j+32 ==> i NOTIN tnf.t_mem) /\
  (!i. b+encoder_member_offset (ho+SUM hs) tails j <= i /\
    i < b+encoder_member_offset (ho+SUM hs) tails j+EL j ns ==> i NOTIN tnf.t_mem) /\
  (!i. j+1 <= i /\ i < LENGTH ms ==>
    val_wf (tv i) (v i) /\
    encoder_member_offset so ms i + val_footprint (tv i) (v i) <= scap) ==>
  encoder_complex_member_inv ctx fn sites protected src dst ip a b scap dcap
    active cid cursor so ho ms hs tails tv v (j+1) sb Gf tnf sf
Proof
  strip_tac >> drule_all encoder_complex_dynamic_member_coordinates >> strip_tac >>
  `encoder_resource ctx fn (children j) a scap protected sf` by
    (irule encoder_resource_restrict >> metis_tac[]) >>
  `!i mem. j+1 <= i /\ i < LENGTH ms /\
    mem_agree_outside tnf.t_mem sf.vs_memory mem ==>
    val_in_memory (tv i) (v i) (a+encoder_member_offset so ms i) mem` by
    (rpt gen_tac >> strip_tac >>
     `val_wf (tv i) (v i) /\
      a <= a+encoder_member_offset so ms i /\
      (a+encoder_member_offset so ms i)+val_footprint (tv i) (v i) <= a+scap` by
       (qpat_x_assum `!i. j+1 <= i /\ i < LENGTH ms ==> _`
          (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
     `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory (tv i) (v i) (a+encoder_member_offset so ms i) m` by
       (fs[encoder_complex_member_inv_def] >> `j <= i` by decide_tac >> metis_tac[]) >>
     `regions_disjoint (a,scap) (b,dcap)` by
       metis_tac[encoder_complex_layout_def] >>
     qpat_x_assum `encoder_dynamic_effect _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [encoder_dynamic_effect_def]) >>
     drule_all encoder_complex_unread_frame >> simp[]) >>
  `(!i. b <= i /\ i < b+encoder_member_offset ho hs (j+1) ==> i NOTIN tnf.t_mem) /\
   (!i. b+(ho+SUM hs) <= i /\
    i < b+encoder_member_offset (ho+SUM hs) tails (j+1) ==> i NOTIN tnf.t_mem)` by
    (irule encoder_complex_dynamic_clean_prefixes >>
     metis_tac[encoder_complex_member_inv_def]) >>
  gvs[encoder_complex_member_inv_def, encoder_dynamic_effect_def] >>
  rpt conj_tac >> rpt strip_tac >>
  gvs[ptr_covers_def, op_prov_def] >> metis_tac[]
QED

Theorem encoder_complex_dynamic_member_counted_ptr:
  encoder_complex_layout so ho ms hs tails dyn ns caps children
    sites a scap b dcap protected active cid cursor /\
  j < LENGTH ms /\ EL j dyn /\
  encoder_complex_member_inv ctx fn sites protected src dst ip a b scap dcap
    active cid cursor so ho ms hs tails tv v j sa G tn s /\
  not_fresh_at sa es /\
  lookup_var es s = SOME (n2w (a+encoder_member_offset so ms j)) /\
  ptr_covers G tn es s (EL j ms) /\
  (!i. j+1 <= i /\ i < LENGTH ms ==>
    val_wf (tv i) (v i) /\
    encoder_member_offset so ms i + val_footprint (tv i) (v i) <= scap) /\
  vyper_to_abi env ty (v j) = SOME av /\
  EL j ns = LENGTH (enc (vyper_to_abi_type env ty) av) /\
  compile_abi_encode_child (Var dst) (Var es) ei T
    (encoder_member_offset ho hs j) (Var ip) sa = (out,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!head off child sc len sd Gp tnp sp.
    abi_encode_child_prefix (Var dst) (encoder_member_offset ho hs j) (Var ip) sa =
      ((Var head,Var off,Var child),sc) /\
    compile_abi_encode_to_buf (Var child) (Var es) ei sc = (len,sd) /\
    sp.vs_current_bb = sc.cs_current_bb /\
    sp.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~sp.vs_halted /\
    lookup_var head sp = SOME (n2w (b+encoder_member_offset ho hs j)) /\
    ptr_covers Gp tnp head sp 32 /\
    lookup_var off sp = SOME (n2w (encoder_member_offset (ho+SUM hs) tails j)) /\
    op_taint tnp (Var off) = {} /\
    lookup_var child sp = SOME (n2w (b+encoder_member_offset (ho+SUM hs) tails j)) /\
    ptr_covers Gp tnp child sp (dcap-encoder_member_offset (ho+SUM hs) tails j) /\
    lookup_var es sp = SOME (n2w (a+encoder_member_offset so ms j)) /\
    ptr_covers Gp tnp es sp (EL j ms) /\
    (!mem. mem_agree_outside tnp.t_mem sp.vs_memory mem ==>
      val_in_memory (tv j) (v j) (a+encoder_member_offset so ms j) mem) /\
    encoder_resource ctx fn (children j) a scap ((cid,cursor,32)::protected) sp ==>
    ?n Gm tnm sm. encoder_semantic_framed_result env ty (v j)
      D ctx fn PG sc sd (children j) a scap ((cid,cursor,32)::protected)
      (b+encoder_member_offset (ho+SUM hs) tails j) (caps j) len n cost
      Gp tnp sp Gm tnm sm) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s cost Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    encoder_complex_member_inv ctx fn sites protected src dst ip a b scap dcap
      active cid cursor so ho ms hs tails tv v (j+1) sb Gf tnf sf /\
    encoder_dynamic_effect sa sites b dcap G tn s Gf tnf sf
Proof
  strip_tac >>
  `!head off child sc len sd Gp tnp sp.
    abi_encode_child_prefix (Var dst) (encoder_member_offset ho hs j) (Var ip) sa =
      ((Var head,Var off,Var child),sc) /\
    compile_abi_encode_to_buf (Var child) (Var es) ei sc = (len,sd) /\
    sp.vs_current_bb = sc.cs_current_bb /\
    sp.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~sp.vs_halted /\
    lookup_var head sp = SOME (n2w (b+encoder_member_offset ho hs j)) /\
    ptr_covers Gp tnp head sp 32 /\
    lookup_var off sp = SOME (n2w (encoder_member_offset (ho+SUM hs) tails j)) /\
    op_taint tnp (Var off) = {} /\
    lookup_var child sp = SOME (n2w (b+encoder_member_offset (ho+SUM hs) tails j)) /\
    ptr_covers Gp tnp child sp (dcap-encoder_member_offset (ho+SUM hs) tails j) /\
    encoder_resource ctx fn (children j) a scap ((cid,cursor,32)::protected) sp /\
    sp.vs_memory = s.vs_memory /\ tnp.t_mem = tn.t_mem /\ sp.vs_allocas = s.vs_allocas /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sp = lookup_var x s /\ FLOOKUP Gp x = FLOOKUP G x /\
      op_taint tnp (Var x) = op_taint tn (Var x)) ==>
    ?Gm tnm sm. encoder_framed_child_result D ctx fn PG sc sd (children j)
      a scap ((cid,cursor,32)::protected)
      (b+encoder_member_offset (ho+SUM hs) tails j) (caps j) len
      (EL j ns) cost Gp tnp sp Gm tnm sm` by
    (rpt gen_tac >> strip_tac >>
     `lookup_var es sp = SOME (n2w (a+encoder_member_offset so ms j)) /\
      ptr_covers Gp tnp es sp (EL j ms)` by
       (gvs[ptr_covers_def, op_prov_def] >> metis_tac[]) >>
     `!mem. mem_agree_outside tnp.t_mem sp.vs_memory mem ==>
        val_in_memory (tv j) (v j) (a+encoder_member_offset so ms j) mem` by
       (fs[encoder_complex_member_inv_def] >> metis_tac[LESS_OR_EQ]) >>
     qpat_x_assum `!head off child sc len sd Gp tnp sp. _` drule_all >> strip_tac >>
     gvs[encoder_semantic_framed_result_def] >> metis_tac[]) >>
  drule_all encoder_complex_dynamic_member_coordinates >> strip_tac >>
  `~s.vs_halted /\ not_fresh_at sa ip /\ not_fresh_at sa dst /\
   lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s dcap /\
   lookup_var ip s = SOME (n2w cursor) /\ ptr_covers G tn ip s 32 /\
   mload cursor s = n2w (encoder_member_offset (ho+SUM hs) tails j) /\
   (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tn.t_mem) /\
   FLOOKUP s.vs_allocas cid = SOME (cursor,32) /\
   encoder_resource ctx fn sites a scap protected s` by
    fs[encoder_complex_member_inv_def] >>
  `b+dcap < dimword(:256) /\ cursor < dimword(:256) /\
   cid IN sites /\ cid NOTIN children j /\
   regions_disjoint (cursor,32)
     (b+encoder_member_offset (ho+SUM hs) tails j,caps j)` by
    (fs[encoder_complex_layout_def, regions_disjoint_def] >> decide_tac) >>
  `encoder_member_offset ho hs j+32 <= encoder_member_offset (ho+SUM hs) tails j` by
    decide_tac >>
  drule_all encoder_dynamic_child_source_narrow_framed_counted_ptr >> strip_tac >>
  `encoder_dynamic_effect sa sites b dcap G tn s Gf tnf sf` by
    (simp[encoder_dynamic_effect_def] >> fs[SUBSET_DEF] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    (drule abi_encoder_child_bounds >> simp[not_fresh_at_def] >>
     rpt strip_tac >> decide_tac) >>
  drule_all encoder_complex_dynamic_invariant_advance >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[]
QED
