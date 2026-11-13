Theory extRetSemanticDynamicConstructorPtr
Ancestors
  extRetDynamicArrayOuterEntryPtr extRetDynamicArrayOuterFinishPtr
  extRetDynamicArrayPhasePtr extRetDynamicBodyPtr extRetRecursiveFramePtr
  extRetFramedChildPtr extRetSemanticResultPtr extRetRecursiveResourcePtr
  extRetScratchResourcePtr fragGasPathPtr fragExec compileEnv
  loweringStateRelDefs emitHelper abiEncoderArrayContext
  abiEncoderArrayHeader abiEncoderArrayLoopLayout abiEncoderArrayBodyCode
  abiEncoderArrayTail abiEncoderChildCode abiDecoderLoopEmit
  abiEncoderArrayCode abiEncoderChildContext abiEncoder bodyPtrDefs
  ptrDiscipline venomState venomMemDefs valueEncoding vyperABI vyperTypeABI
  vyperTyping vyperValue words finite_map pred_set arithmetic list rich_list

(* A zero-cost outer entry may stop at a header, not at the compiler
   endpoint.  Its effect is precisely what is needed to rebase the result. *)
Theorem encoder_semantic_result_prefix[local]:
  gas_path_ptr D 0 ctx fn PG G tn s 0 Gm tnm (OK smstate) /\
  encoder_dynamic_effect si sites b cap G tn s Gm tnm smstate /\
  encoder_semantic_framed_result env ty v D ctx fn PG sh sfcomp sites a scap
    protected b cap out n cost Gm tnm smstate Gf tnf sf /\
  (!x. not_fresh_at si x ==> not_fresh_at sh x) ==>
  encoder_semantic_framed_result env ty v D ctx fn PG si sfcomp sites a scap
    protected b cap out n cost G tn s Gf tnf sf
Proof
  simp_tac bool_ss [encoder_semantic_framed_result_def] >> strip_tac >>
  `encoder_dynamic_effect sh sites b cap Gm tnm smstate Gf tnf sf` by
    fs[encoder_dynamic_effect_def, encoder_framed_child_result_def] >>
  `encoder_dynamic_effect si sites b cap Gm tnm smstate Gf tnf sf` by
    (fs[encoder_dynamic_effect_def] >> metis_tac[]) >>
  `encoder_dynamic_effect si sites b cap G tn s Gf tnf sf` by
    (irule encoder_dynamic_effect_then >> metis_tac[]) >>
  fs[encoder_framed_child_result_def, encoder_dynamic_effect_def] >>
  irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`] |> SRULE []) >>
  metis_tac[]
QED

(* The recursive premise concerns only a child compilation and its entry;
   no runtime state for the parent is supplied by the caller. *)
Theorem encoder_semantic_dynamic_array_counted_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiDynArray ei 32 msz T) si = (out,sfcomp) /\
  fn_has_code si sfcomp fn /\
  s.vs_current_bb = si.cs_current_bb /\
  s.vs_inst_idx = LENGTH si.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ encoder_resource ctx fn sites a scap protected s /\
  si.cs_next_id IN sites /\ si.cs_next_id+4 IN sites /\ si.cs_next_id+6 IN sites /\
  children SUBSET sites DELETE si.cs_next_id /\
  si.cs_next_id+4 NOTIN children /\ si.cs_next_id+6 NOTIN children /\
  not_fresh_at si src /\ not_fresh_at si dst /\
  lookup_var src s = SOME (n2w a) /\ lookup_var dst s = SOME (n2w b) /\
  ptr_covers G tn src s scap /\ ptr_covers G tn dst s dcap /\
  a+scap < dimword(:256) /\ b+dcap < dimword(:256) /\
  32 <= scap /\ 32 <= dcap /\ N < dimword(:256) /\
  (!i. a <= i /\ i < a+32 ==> i NOTIN tn.t_mem) /\ mload a s = n2w N /\
  val_wf (ArrayTV tv (Dynamic limit)) (ArrayV (DynArrayV vs)) /\
  val_footprint (ArrayTV tv (Dynamic limit)) (ArrayV (DynArrayV vs)) <= scap /\
  (a+scap <= b \/ b+dcap <= a) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic limit)) (ArrayV (DynArrayV vs)) a mem) /\
  MEM (did,dbase,dsize) protected /\ dbase <= b /\ b+dcap <= dbase+dsize /\
  N = LENGTH vs /\ LENGTH ns = N /\ LENGTH avs = N /\ LENGTH costs = N /\
  evaluate_type env ty = SOME tv /\ msz = type_memory_size tv /\
  value_has_type (ArrayTV tv (Dynamic limit)) (ArrayV (DynArrayV vs)) /\
  (!i. i<N ==> vyper_to_abi env ty (EL i vs) = SOME (EL i avs) /\
    EL i ns = LENGTH (enc (vyper_to_abi_type env ty) (EL i avs))) /\
  vyper_to_abi env (ArrayT ty (Dynamic limit)) (ArrayV (DynArrayV vs)) = SOME av /\
  LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic limit))) av) =
    32+32*N+SUM ns /\ 32+32*N+SUM ns <= dcap /\
  (!i. i<N ==> EL i ns <= cap i /\
    32+(32*N+SUM (TAKE i ns))+cap i <= dcap /\ 32+i*msz+msz <= scap) /\
  (!sb se child_src child_dst len r p c i Gp tnp sp.
    compile_abi_encode_to_buf (Var child_dst) (Var child_src) ei sb = (len,se) /\
    fn_has_code sb se fn /\ i<N /\
    sp.vs_current_bb = sb.cs_current_bb /\
    sp.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sp.vs_halted /\
    lookup_var child_src sp = SOME (n2w (a+32+i*msz)) /\
    ptr_covers Gp tnp child_src sp msz /\
    lookup_var child_dst sp = SOME (n2w (b+32+(32*N+SUM (TAKE i ns)))) /\
    ptr_covers Gp tnp child_dst sp (cap i) /\
    (!mem. mem_agree_outside tnp.t_mem sp.vs_memory mem ==>
      val_in_memory tv (EL i vs) (a+32+i*msz) mem) /\
    encoder_resource ctx fn children a scap
      ((si.cs_next_id+4,p,32)::(si.cs_next_id+6,c,32)::(si.cs_next_id,r,32)::protected) sp ==>
    ?n Gm tnm sm. encoder_semantic_framed_result env ty (EL i vs)
      D ctx fn PG sb se children a scap
      ((si.cs_next_id+4,p,32)::(si.cs_next_id+6,c,32)::(si.cs_next_id,r,32)::protected)
      (b+32+(32*N+SUM (TAKE i ns))) (cap i) len n (EL i costs) Gp tnp sp Gm tnm sm) ==>
  ?Gf tnf sf.
    encoder_semantic_framed_result env (ArrayT ty (Dynamic limit))
      (ArrayV (DynArrayV vs)) D ctx fn PG si sfcomp sites a scap protected
      b dcap out (32+32*N+SUM ns) (SUM costs) G tn s Gf tnf sf /\
    32+32*N+SUM ns <= dcap
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all encoder_dynamic_array_phase_context >> strip_tac >>
  drule abi_encode_array_prefix_shape >> strip_tac >>
  drule abi_encode_array_dynamic_init_shape >> strip_tac >>
  qpat_x_assum `ops = _` SUBST_ALL_TAC >>
  qpat_x_assum `cells = _` SUBST_ALL_TAC >>
  rule_assum_tac (PURE_REWRITE_RULE [pairTheory.FST,pairTheory.SND]) >>
  `?idx child_src data head. coords = ((Var idx,Var child_src),(Var data,Var head)) /\
     not_fresh_at sx idx /\ not_fresh_at sx child_src /\
     not_fresh_at sx data /\ not_fresh_at sx head` by
    (qpat_x_assum `abi_encode_array_addresses _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[abi_encode_array_addresses_def,
       abiDecoderDynamicLoopSetupTheory.abi_decode_array_head_setup_def,
       abiDecoderDynamicLoopSetupTheory.abi_decode_indexed_coordinates_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  qpat_x_assum `coords = _` SUBST_ALL_TAC >>
  rule_assum_tac (PURE_REWRITE_RULE [pairTheory.FST,pairTheory.SND]) >>
  `?off child_dst. tail = (Var off,Var child_dst) /\
     not_fresh_at sb off /\ not_fresh_at sb child_dst` by
    (qpat_x_assum `abi_encode_array_tail _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abi_encode_array_tail_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  qpat_x_assum `tail = _` SUBST_ALL_TAC >>
  rule_assum_tac (PURE_REWRITE_RULE [pairTheory.FST,pairTheory.SND]) >>
  drule (cj 2 abi_encode_array_exit_shape) >> strip_tac >>
  qpat_x_assum `encoded = _` SUBST_ALL_TAC >>
  drule abi_encode_array_finish_shape >> strip_tac >>
  qpat_x_assum `out = _` SUBST_ALL_TAC >>
  drule abiEncoderArrayParentTheory.abi_encode_array_finish_trace >> strip_tac >>
  imp_res_tac emitHelperPropsTheory.emitted_insts_emit_op >>
  qpat_x_assum `old = _` SUBST_ALL_TAC >>
  qpat_x_assum `next = _` SUBST_ALL_TAC >>
  `?hdr body_lbl exit_lbl. labels = (hdr,body_lbl,exit_lbl) /\
     sa.cs_current_bb = body_lbl /\ sa.cs_current_insts = [] /\
     sa.cs_next_var = sh.cs_next_var+3` by
    (qpat_x_assum `abi_encode_array_header _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[abi_encode_array_header_shape] >>
     strip_tac >> gvs[]) >>
  qpat_x_assum `labels = _` SUBST_ALL_TAC >>
  qpat_x_assum `idx = Var _` SUBST_ALL_TAC >>
  rule_assum_tac (PURE_REWRITE_RULE [pairTheory.FST,pairTheory.SND]) >>
  `sc.cs_current_bb = exit_lbl /\ sc.cs_current_insts = [] /\
   sc.cs_next_var = send.cs_next_var+1` by
    (qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abi_decode_loop_suffix_shape,abi_decode_loop_suffix_state_def] >>
     strip_tac >> gvs[]) >>
  `cs_extends slend c1 /\ cs_extends c1 c2 /\
   cs_extends c2 c3 /\ cs_extends c3 sfcomp` by
    (imp_res_tac emitHelperPropsTheory.inst_extends_emit_op >>
     imp_res_tac emitHelperPropsTheory.inst_extends_emit_void >>
     imp_res_tac exprLoweringPropsTheory.emit_op_same_blocks >>
     imp_res_tac exprLoweringPropsTheory.emit_void_same_blocks >>
     fs[exprLoweringPropsTheory.same_blocks_def] >> metis_tac[abi_encoder_straight_extends]) >>
  `fn_has_code slend c1 fn /\ fn_has_code c1 c2 fn /\
   fn_has_code c2 c3 fn /\ fn_has_code c3 sfcomp fn` by
    metis_tac[fn_has_code_split,cs_extends_trans] >>
  `si.cs_next_var <= sh.cs_next_var /\
   sh.cs_next_var <= sa.cs_next_var /\
   sa.cs_next_var <= sb.cs_next_var /\
   se.cs_next_var <= send.cs_next_var /\
   sh.cs_next_var <= sc.cs_next_var /\
   sc.cs_next_var <= slend.cs_next_var /\
   sx.cs_next_var <= sb.cs_next_var` by decide_tac >>
  `!x. not_fresh_at si x ==> not_fresh_at sh x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. not_fresh_at sh x ==> not_fresh_at sa x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. not_fresh_at sb x ==> not_fresh_at se x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. not_fresh_at se x ==> not_fresh_at send x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. not_fresh_at sh x ==> not_fresh_at sc x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. not_fresh_at sh x ==> not_fresh_at slend x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sh` >> simp[] >> decide_tac) >>
  `not_fresh_at sh (STRING #"%" (toString sl.cs_next_var)) /\
   not_fresh_at sh (STRING #"%" (toString (sl.cs_next_var+1))) /\
   not_fresh_at sh (STRING #"%" (toString si.cs_next_var)) /\
   not_fresh_at sh (STRING #"%" (toString (si.cs_next_var+1))) /\
   not_fresh_at slend (STRING #"%" (toString (sc.cs_next_var+2)))` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `not_fresh_at sh src /\ not_fresh_at sh dst` by metis_tac[] >>
  `not_fresh_at sa (STRING #"%" (toString sl.cs_next_var)) /\
   not_fresh_at sa (STRING #"%" (toString (sl.cs_next_var+1))) /\
   not_fresh_at sa (STRING #"%" (toString (si.cs_next_var+1))) /\
   not_fresh_at sa src /\ not_fresh_at sa dst` by metis_tac[] >>
  `not_fresh_at sb head /\ not_fresh_at sb idx'` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `not_fresh_at sc (STRING #"%" (toString (sl.cs_next_var+1))) /\
   not_fresh_at sc (STRING #"%" (toString si.cs_next_var)) /\
   not_fresh_at slend (STRING #"%" (toString si.cs_next_var))` by metis_tac[] >>
  qabbrev_tac `parent = STRING #"%" (toString si.cs_next_var)` >>
  qabbrev_tac `cv = STRING #"%" (toString (si.cs_next_var+1))` >>
  qabbrev_tac `ip = STRING #"%" (toString sl.cs_next_var)` >>
  qabbrev_tac `cursor = STRING #"%" (toString (sl.cs_next_var+1))` >>
  qabbrev_tac `encodedv = STRING #"%" (toString (sc.cs_next_var+2))` >>
  qabbrev_tac `oldv = STRING #"%" (toString slend.cs_next_var)` >>
  qabbrev_tac `sumv = STRING #"%" (toString c1.cs_next_var)` >>
  qabbrev_tac `outv = STRING #"%" (toString c3.cs_next_var)` >>
  `a < dimword(:256) /\ b < dimword(:256)` by decide_tac >>
  drule_all (encoder_dynamic_outer_entry_counted_ptr |>
    Q.INST [`ops` |-> `(Var parent,Var cv)`, `cells` |-> `(Var ip,Var cursor)`,
            `labels` |-> `(hdr,body_lbl,exit_lbl)`] |> SRULE []) >>
  disch_then (qspecl_then [`ns`,`PG`,`D`] strip_assume_tac) >>
  `alloca_inv sf` by metis_tac[encoder_resource_def, scratch_resource_def] >>
  `regions_disjoint (p,32) (c,32)` by
    (match_mp_tac (allocaSiteResourceTheory.alloca_site_registered_disjoint |>
       Q.INST [`s` |-> `sf`, `id` |-> `si.cs_next_id+4`, `other` |-> `si.cs_next_id+6`]) >>
     simp[]) >>
  `regions_disjoint (a,scap) (p,32) /\
   regions_disjoint (a,scap) (c,32)` by
    (qpat_assum `encoder_resource ctx fn sites a scap protected sf` mp_tac >>
     pure_rewrite_tac [encoder_resource_def, scratch_resource_def] >>
     strip_tac >> `scap <> 0` by decide_tac >> metis_tac[]) >>
  `regions_disjoint (r,32) (b,dcap) /\
   regions_disjoint (p,32) (b,dcap) /\
   regions_disjoint (c,32) (b,dcap)` by
    (drule_all (encoder_resource_protected |> Q.INST [`s` |-> `sf`]) >>
     strip_tac >>
     `dsize <> 0` by decide_tac >>
     `regions_disjoint (dbase,dsize) (r,32) /\
      regions_disjoint (dbase,dsize) (p,32) /\
      regions_disjoint (dbase,dsize) (c,32)` by
       (qpat_assum `scratch_resource ctx fn sites dbase dsize sf` mp_tac >>
        pure_rewrite_tac [scratch_resource_def] >> strip_tac >> metis_tac[]) >>
     qpat_assum `regions_disjoint (dbase,dsize) (r,32)` mp_tac >>
     qpat_assum `regions_disjoint (dbase,dsize) (p,32)` mp_tac >>
     qpat_assum `regions_disjoint (dbase,dsize) (c,32)` mp_tac >>
     qpat_assum `dbase <= b` mp_tac >>
     qpat_assum `b+dcap <= dbase+dsize` mp_tac >>
     rpt (pop_assum kall_tac) >> pure_rewrite_tac [regions_disjoint_def] >> decide_tac) >>
  `regions_disjoint (a,scap) (b,dcap)` by simp[regions_disjoint_def] >>
  mp_tac (encoder_dynamic_outer_finish_counted_ptr |>
    Q.INST [`oid` |-> `si.cs_next_id`, `pid` |-> `si.cs_next_id+4`,
            `cid` |-> `si.cs_next_id+6`, `s` |-> `sf`, `G` |-> `Gf`, `tn` |-> `tnf`,
            `ss` |-> `send`, `sd` |-> `slend`, `s0` |-> `c1`, `s1` |-> `c2`,
            `s2` |-> `c3`, `idx` |-> `idx'`, `encoded` |-> `encodedv`,
            `old` |-> `oldv`, `sumv` |-> `sumv`, `out` |-> `outv`]) >>
  (impl_tac >- (
    asm_rewrite_tac [] >>
    (conj_tac >- simp[]) >> (conj_tac >- simp[]) >>
    rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
    metis_tac[])) >>
  strip_tac >>
  qexistsl [`Gf'`,`tnf'`,`sf'`] >> conj_tac >-
    (irule encoder_semantic_result_prefix >> metis_tac[]) >>
  first_assum ACCEPT_TAC
QED
