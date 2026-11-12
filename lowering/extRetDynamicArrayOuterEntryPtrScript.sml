Theory extRetDynamicArrayOuterEntryPtr
Ancestors
  extRetSemanticDynamicArrayPtr extRetDynamicArrayInitFramePtr
  extRetDynamicArrayPhasePtr extRetDynamicArrayCountPtr extRetDynamicBodyPtr
  extRetDynamicArrayEntryPtr extRetRecursiveFramePtr
  extRetRecursiveResourcePtr extRetFramedChildPtr extRetScratchResourcePtr
  abiEncoderArrayPhases abiEncoderArrayContext abiDecoderIndexInit
  abiEncoderArrayCode abiEncoderArrayHeader abiEncoder
  emitHelperProps exprLoweringProps compileEnv emitHelper fragExec context ASCIInumbers
  bodyPtrDefs ptrDiscipline venomState venomMemDefs venomMemProps
  robustCopyTransportPtr augAssignPtrStore wordLoadStorePtr valueEncoding words finite_map pred_set arithmetic list loweringStateRelDefs

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
    encoder_resource ctx fn sites a scap protected sf /\
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

(* Count load/store, at the resource boundary used by the outer join. *)
Theorem encoder_dynamic_count_resource_counted_ptr:
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
  ptr_covers G tn dst s 32 /\ b < dimword(:256) /\ 32 <= dcap /\
  encoder_resource ctx fn sites a scap protected s /\
  val_wf tv v /\ (a+val_footprint tv v <= b \/ b+32 <= a) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v a mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sc.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var cv sf = SOME (n2w N) /\ op_taint tnf (Var cv) = {} /\
    op_prov Gf (Var cv) = NONE /\
    encoder_resource ctx fn sites a scap protected sf /\
    encoder_dynamic_effect sa sites b dcap G tn s Gf tnf sf /\
    (!mem. mem_agree_outside tnf.t_mem sf.vs_memory mem ==> val_in_memory tv v a mem) /\
    sf.vs_allocas = s.vs_allocas /\
    (!i. b <= i /\ i < b+32 ==> i NOTIN tnf.t_mem) /\
    sf.vs_memory = (mstore b (n2w N) s).vs_memory /\
    (!i. i < b \/ b+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule_all encoder_dynamic_count_header_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `encoder_resource ctx fn sites a scap protected sf` by
    (irule encoder_resource_fields >> qexists_tac `s` >> simp[]) >>
  `encoder_dynamic_effect sa sites b dcap G tn s Gf tnf sf` by
    (irule encoder_dynamic_effect_from_footprint >> simp[] >>
     qexists_tac `{i | b <= i /\ i < b+32}` >>
     simp[SUBSET_DEF, encoder_write_envelope_def] >>
     irule mstore_memory_frame) >>
  `!mem. mem_agree_outside tnf.t_mem sf.vs_memory mem ==> val_in_memory tv v a mem` by
    (gvs[] >> match_mp_tac mstore_robust_exterior >> simp[] >>
     rpt strip_tac >> decide_tac) >>
  qexistsl [`Gf`,`tnf`,`sf`] >> simp[]
QED

(* Resolve the four straight-line compiler steps once, before the runtime join. *)
Theorem encoder_dynamic_outer_prefix_context[local]:
  abi_encode_array_prefix src dst si = (ops,sl) /\ fn_has_code si sl fn ==>
  ?buf s0 s1 s2 cv.
    compile_alloc_buffer 32 si = (buf,s0) /\
    emit_void MSTORE [buf.buf_operand;Lit 0w] s0 = ((),s1) /\
    emit_op MLOAD [src] s1 = (Var cv,s2) /\
    emit_void MSTORE [dst;Var cv] s2 = ((),sl) /\
    ops = (buf.buf_operand,Var cv) /\
    fn_has_code si s1 fn /\ fn_has_code s1 s2 fn /\ fn_has_code s2 sl fn /\
    s1.cs_next_var = si.cs_next_var+1 /\
    sl.cs_next_var = si.cs_next_var+2 /\ sl.cs_next_id = si.cs_next_id+4 /\
    not_fresh_at sl cv /\
    (!x. not_fresh_at si x ==> not_fresh_at s1 x /\ not_fresh_at sl x)
Proof
  strip_tac >> drule encoder_dynamic_outer_prefix_trace >> strip_tac >>
  `cs_extends si s0 /\ cs_extends s0 s1 /\ cs_extends s1 s2 /\ cs_extends s2 sl` by
    (gvs[compile_alloc_buffer_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
     simp[cs_extends_def, emitted_blocks_def]) >>
  `fn_has_code si s1 fn /\ fn_has_code s1 s2 fn /\ fn_has_code s2 sl fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def, compile_alloc_buffer_def] >>
  simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem encoder_dynamic_outer_effect_mono[local]:
  encoder_dynamic_effect sa sites b cap G tn s Gf tnf sf /\
  sites SUBSET larger /\
  (!x. not_fresh_at earlier x ==> not_fresh_at sa x) ==>
  encoder_dynamic_effect earlier larger b cap G tn s Gf tnf sf
Proof
  strip_tac >>
  `encoder_write_envelope sites sf b cap SUBSET
   encoder_write_envelope larger sf b cap` by
    (fs[encoder_write_envelope_def, encoder_scratch_span_def, SUBSET_DEF] >>
     metis_tac[]) >>
  fs[encoder_dynamic_effect_def, mem_agree_outside_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem encoder_dynamic_outer_entry_counted_ptr:
  abi_encode_array_prefix (Var src) (Var dst) si = (ops,sl) /\
  abi_encode_array_dynamic_init (SND ops) 32 sl = (cells,sh) /\
  abi_encode_array_header (FST cells) (SND ops) sh = (labels,sa) /\
  fn_has_code si sl fn /\ fn_has_code sl sh fn /\ fn_has_code sh sa fn /\
  s.vs_current_bb = si.cs_current_bb /\
  s.vs_inst_idx = LENGTH si.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ encoder_resource ctx fn sites a scap protected s /\
  si.cs_next_id IN sites /\ si.cs_next_id+4 IN sites /\ si.cs_next_id+6 IN sites /\
  not_fresh_at si src /\ not_fresh_at si dst /\
  lookup_var src s = SOME (n2w a) /\ lookup_var dst s = SOME (n2w b) /\
  ptr_covers G tn src s scap /\ ptr_covers G tn dst s dcap /\
  a < dimword(:256) /\ b < dimword(:256) /\
  32 <= scap /\ 32 <= dcap /\
  (!i. a <= i /\ i < a+32 ==> i NOTIN tn.t_mem) /\ mload a s = n2w N /\
  val_wf tv v /\ val_footprint tv v <= scap /\
  (a+scap <= b \/ b+dcap <= a) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v a mem) /\
  MEM (did,dbase,dsize) protected /\ dbase <= b /\ b+dcap <= dbase+dsize ==>
  ?parent cv ip cursor r p c Gf tnf sf.
    ops = (Var parent,Var cv) /\ cells = (Var ip,Var cursor) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = FST labels /\ sf.vs_inst_idx = 0 /\
    encoder_dynamic_loop_inv ctx fn (sites DELETE si.cs_next_id)
      ((si.cs_next_id,r,32)::protected)
      ip cursor src dst cv p c a b scap dcap tv v N ns 0 Gf tnf sf /\
    encoder_dynamic_effect si sites b dcap G tn s Gf tnf sf /\
    encoder_resource ctx fn sites a scap protected sf /\
    lookup_var parent sf = SOME (n2w r) /\ ptr_covers Gf tnf parent sf 32 /\
    mload r sf = 0w /\ (!i. r <= i /\ i < r+32 ==> i NOTIN tnf.t_mem) /\
    FLOOKUP sf.vs_allocas si.cs_next_id = SOME (r,32) /\
    FLOOKUP sf.vs_allocas (si.cs_next_id+4) = SOME (p,32) /\
    FLOOKUP sf.vs_allocas (si.cs_next_id+6) = SOME (c,32) /\
    r+32 < dimword(:256) /\ p+32 < dimword(:256) /\ c+32 < dimword(:256) /\
    (!i. b <= i /\ i < b+32 ==> i NOTIN tnf.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all encoder_dynamic_outer_prefix_context >> strip_tac >>
  drule_all encoder_dynamic_parent_init_counted_ptr >>
  disch_then (qspecl_then [`tn`,`dcap`,`b`,`PG`,`G`,`D`] strip_assume_tac) >>
  `not_fresh_at s1 parent` by
    (qpat_x_assum `compile_alloc_buffer 32 si = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[not_fresh_at_def]) >>
  `regions_disjoint (a,scap) (r,32) /\ regions_disjoint (dbase,dsize) (r,32)` by
    (qpat_assum `encoder_resource ctx fn sites a scap protected sf` mp_tac >>
     pure_rewrite_tac [encoder_resource_def, scratch_resource_def] >>
     strip_tac >> `scap <> 0 /\ dsize <> 0` by decide_tac >> metis_tac[]) >>
  `!i. a <= i /\ i < a+scap ==> ~(r <= i /\ i < r+32)` by
    (fs[regions_disjoint_def] >> decide_tac) >>
  `mload a sf = n2w N /\ (!i. a <= i /\ i < a+32 ==> i NOTIN tnf.t_mem)` by
    (qsuff_tac `mload a sf = mload a s /\
       (!i. a <= i /\ i < a+32 ==> i NOTIN tnf.t_mem)` >- simp[] >>
     irule encoder_frame_clean_word >>
     qexistsl [`tn`,`{i | r <= i /\ i < r+32}`] >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!mem. mem_agree_outside tnf.t_mem sf.vs_memory mem ==> val_in_memory tv v a mem` by
    (rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
     conj_tac >- simp[] >>
     qexistsl [`s.vs_memory`,`sf.vs_memory`,`tn.t_mem`,`tnf.t_mem`,
               `{i | r <= i /\ i < r+32}`] >>
     simp[mem_agree_outside_def] >> conj_tac >-
       (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
     gvs[mem_agree_outside_def]) >>
  `lookup_var src sf = SOME (n2w a) /\ lookup_var dst sf = SOME (n2w b) /\
   ptr_covers Gf tnf src sf scap /\ ptr_covers Gf tnf dst sf dcap /\
   ptr_covers Gf tnf src sf 32 /\ ptr_covers Gf tnf dst sf 32 /\
   not_fresh_at s1 dst` by
    (gvs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS]) >>
  qsuff_tac `a+val_footprint tv v <= b \/ b+32 <= a` >-
    (disch_then assume_tac >>
     drule_all encoder_dynamic_count_resource_counted_ptr >>
     disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
     `lookup_var src sf' = SOME (n2w a) /\ lookup_var dst sf' = SOME (n2w b) /\
      ptr_covers Gf' tnf' src sf' scap /\ ptr_covers Gf' tnf' dst sf' dcap` by
       (gvs[ptr_covers_def] >> metis_tac[]) >>
     `not_fresh_at sl src /\ not_fresh_at sl dst /\
      sl.cs_next_id IN (sites DELETE si.cs_next_id) /\
      sl.cs_next_id+2 IN (sites DELETE si.cs_next_id) /\
      MEM (did,dbase,dsize) ((si.cs_next_id,r,32)::protected)` by simp[] >>
     drule abi_encode_array_dynamic_init_shape >> strip_tac >>
     PairCases_on `labels` >>
     qpat_x_assum `cells = _` SUBST_ALL_TAC >>
     qpat_x_assum `ops = _` SUBST_ALL_TAC >>
     qpat_x_assum `buf.buf_operand = _` SUBST_ALL_TAC >>
     rule_assum_tac (PURE_REWRITE_RULE [pairTheory.FST,pairTheory.SND]) >>
     pure_rewrite_tac [pairTheory.FST,pairTheory.SND] >>
     drule_all encoder_dynamic_initialized_entry_counted_ptr >>
     disch_then (qspecl_then [`ns`,`PG`,`D`] strip_assume_tac) >>
     `encoder_dynamic_effect s1 (sites DELETE si.cs_next_id) b dcap
        Gf' tnf' sf' Gf'' tnf'' sf''` by
       (irule encoder_dynamic_outer_effect_mono >>
        qexistsl [`sl`,`sites DELETE si.cs_next_id`] >> simp[] >>
        gvs[not_fresh_at_def] >> decide_tac) >>
     `encoder_dynamic_effect s1 (sites DELETE si.cs_next_id) b dcap
        Gf tnf sf Gf'' tnf'' sf''` by
       (irule encoder_dynamic_effect_then >> metis_tac[]) >>
     `encoder_dynamic_effect si sites b dcap Gf tnf sf Gf'' tnf'' sf''` by
       (irule encoder_dynamic_outer_effect_mono >>
        qexistsl [`s1`,`sites DELETE si.cs_next_id`] >> simp[]) >>
     `encoder_dynamic_effect si sites b dcap G tn s Gf'' tnf'' sf''` by
       (irule encoder_dynamic_effect_then >> metis_tac[]) >>
     `regions_disjoint (r,32) (b,dcap)` by
       (fs[regions_disjoint_def] >> decide_tac) >>
     `encoder_resource ctx fn (sites DELETE si.cs_next_id) a scap
        ((si.cs_next_id,r,32)::protected) sf''` by
       metis_tac[encoder_dynamic_loop_inv_def] >>
     `!i. r <= i /\ i < r+32 ==>
        i NOTIN encoder_write_envelope (sites DELETE si.cs_next_id) sf'' b dcap` by
       (match_mp_tac (GEN_ALL encoder_envelope_protected) >>
        qpat_assum `encoder_resource ctx fn (sites DELETE si.cs_next_id) a scap
          ((si.cs_next_id,r,32)::protected) sf''` mp_tac >>
        qpat_assum `regions_disjoint (r,32) (b,dcap)` mp_tac >>
        rpt (pop_assum kall_tac) >> metis_tac[MEM]) >>
     `mload r sf'' = 0w /\ (!i. r <= i /\ i < r+32 ==> i NOTIN tnf''.t_mem)` by
       (qsuff_tac `mload r sf'' = mload r sf /\
          (!i. r <= i /\ i < r+32 ==> i NOTIN tnf''.t_mem)` >- simp[] >>
        irule encoder_frame_clean_word >>
        qexistsl [`tnf`,`encoder_write_envelope (sites DELETE si.cs_next_id) sf'' b dcap`] >>
        simp[] >>
        qpat_assum `encoder_dynamic_effect s1 _ _ _ Gf tnf sf Gf'' tnf'' sf''` mp_tac >>
        pure_rewrite_tac [encoder_dynamic_effect_def] >> metis_tac[]) >>
     `lookup_var parent sf'' = SOME (n2w r) /\
      ptr_covers Gf'' tnf'' parent sf'' 32 /\
      FLOOKUP sf''.vs_allocas si.cs_next_id = SOME (r,32)` by
       (qpat_assum `encoder_dynamic_effect s1 _ _ _ Gf tnf sf Gf'' tnf'' sf''` mp_tac >>
        pure_rewrite_tac [encoder_dynamic_effect_def] >> strip_tac >>
        gvs[ptr_covers_def] >> metis_tac[]) >>
     `encoder_resource ctx fn sites a scap protected sf''` by
       (match_mp_tac encoder_resource_registered_intro >>
        conj_tac >-
          (qpat_assum `encoder_resource ctx fn (sites DELETE si.cs_next_id) a scap _ sf''` mp_tac >>
           qpat_assum `FLOOKUP sf''.vs_allocas si.cs_next_id = SOME (r,32)` mp_tac >>
           qpat_assum `regions_disjoint (a,scap) (r,32)` mp_tac >>
           rpt (pop_assum kall_tac) >>
           pure_rewrite_tac [encoder_resource_def, scratch_resource_def] >>
           ntac 3 strip_tac >>
           qpat_x_assum `!id b n. MEM (id,b,n) _ ==> _` kall_tac >>
           conj_tac >- first_assum ACCEPT_TAC >>
           conj_tac >- first_assum ACCEPT_TAC >>
           conj_tac >- first_assum ACCEPT_TAC >>
           rpt gen_tac >> strip_tac >>
           Cases_on `id = si.cs_next_id`
           >- (qpat_x_assum `!id b sz. _` kall_tac >> metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
           qpat_x_assum `!id b sz. _` irule >>
           simp_tac std_ss [IN_DELETE] >> metis_tac[]) >>
        rpt gen_tac >> strip_tac >>
        qpat_assum `encoder_resource ctx fn sites a scap protected s` mp_tac >>
        qpat_assum `encoder_resource ctx fn (sites DELETE si.cs_next_id) a scap _ sf''` mp_tac >>
        pure_rewrite_tac [encoder_resource_def] >> rpt strip_tac >>
        metis_tac[MEM]) >>
     `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf' tnf' (OK sf')` by
       metis_tac[fragGasPathPtrTheory.gas_path_ptr_then, ADD_0] >>
     `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf'' tnf'' (OK sf'')` by
       metis_tac[fragGasPathPtrTheory.gas_path_ptr_then, ADD_0] >>
     qexistsl [`parent`,`cv`,`STRING #"%" (toString sl.cs_next_var)`,
       `STRING #"%" (toString (sl.cs_next_var+1))`,`r`,`p`,`c`,`Gf''`,`tnf''`,`sf''`] >>
     simp[] >> gvs[]) >> simp[] >> decide_tac
QED
