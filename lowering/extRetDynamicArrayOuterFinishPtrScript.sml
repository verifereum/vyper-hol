Theory extRetDynamicArrayOuterFinishPtr
Ancestors
  extRetSemanticDynamicArrayPtr extRetSemanticDynamicLoopPtr
  extRetDynamicExitPtr extRetDynamicBodyPtr extRetRecursiveFramePtr
  extRetRecursiveResourcePtr extRetFramedChildPtr extRetSemanticResultPtr
  extRetScratchResourcePtr extRetRobustSourceChildrenPtr abiEncoderArrayHeader abiEncoderArrayBodyCode
  abiEncoderArrayTail abiEncoderChildCode abiDecoderLoopEmit abiEncoderArrayCode
  abiEncoder compileEnv emitHelper fragExec fragGasPathPtr
  bodyPtrDefs ptrDiscipline venomState venomMemDefs valueEncoding
  vyperABI vyperTypeABI vyperTyping vyperValue
  words finite_map pred_set arithmetic list rich_list loweringStateRelDefs

(* A protected parent survives the loop even when child sites are reused. *)
Theorem encoder_dynamic_effect_parent_word:
  encoder_dynamic_effect sh (sites DELETE oid) b dcap G tn s Gf tnf sf /\
  encoder_resource ctx fn (sites DELETE oid) a scap
    ((oid,r,32)::protected) sf /\
  regions_disjoint (r,32) (b,dcap) /\
  not_fresh_at sh parent /\ lookup_var parent s = SOME (n2w r) /\
  ptr_covers G tn parent s 32 /\ mload r s = 0w /\
  (!i. r <= i /\ i < r+32 ==> i NOTIN tn.t_mem) ==>
  lookup_var parent sf = SOME (n2w r) /\
  ptr_covers Gf tnf parent sf 32 /\ mload r sf = 0w /\
  (!i. r <= i /\ i < r+32 ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >>
  `!i. r <= i /\ i < r+32 ==>
    i NOTIN encoder_write_envelope (sites DELETE oid) sf b dcap` by
    (mp_tac (GEN_ALL encoder_envelope_protected) >>
     disch_then drule >> simp[] >> metis_tac[]) >>
  `mload r sf = mload r s /\
   (!i. r <= i /\ i < r+32 ==> i NOTIN tnf.t_mem)` by
    (irule encoder_frame_clean_word >>
     qexistsl [`tn`,`encoder_write_envelope (sites DELETE oid) sf b dcap`] >>
     fs[encoder_dynamic_effect_def]) >>
  `lookup_var parent sf = lookup_var parent s /\
   FLOOKUP Gf parent = FLOOKUP G parent /\
   op_taint tnf (Var parent) = op_taint tn (Var parent)` by
    (fs[encoder_dynamic_effect_def] >> first_x_assum irule >> simp[]) >>
  gvs[ptr_covers_def]
QED

Theorem encoder_resource_restore_parent:
  encoder_resource ctx fn sites a scap protected s /\
  encoder_resource ctx fn (sites DELETE oid) a scap protected sf /\
  FLOOKUP sf.vs_allocas oid = FLOOKUP s.vs_allocas oid ==>
  encoder_resource ctx fn sites a scap protected sf
Proof
  pure_rewrite_tac [encoder_resource_def, scratch_resource_def, IN_DELETE] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem encoder_dynamic_outer_finish_counted_ptr:
  abi_encode_array_header (Var ip) (Var cv) sh = ((hdr,body_lbl,exit_lbl),sa) /\
  abi_encode_array_addresses (Var ip) (Var src) (Var dst) 32 msz sa =
    (((Var idx,Var child_src),(Var data,Var head)),sx) /\
  abi_encode_array_tail (Var data) (Var cursor) sx = ((Var off,Var child_dst),sb) /\
  compile_abi_encode_to_buf (Var child_dst) (Var child_src) ei sb = (len,se) /\
  abi_encode_child_suffix (Var head) (Var cursor) (Var off) len se = (len,ss) /\
  abi_decode_loop_suffix (Var ip) (Var idx) hdr exit_lbl ss = ((),sc) /\
  abi_encode_array_dynamic_exit (Var src) (Var cursor) sc = (Var encoded,sd) /\
  emit_op MLOAD [Var parent] sd = (Var old,s0) /\
  emit_op ADD [Var old;Var encoded] s0 = (Var sumv,s1) /\
  emit_void MSTORE [Var parent;Var sumv] s1 = ((),s2) /\
  emit_op MLOAD [Var parent] s2 = (Var out,sfcomp) /\
  fn_has_code sh sa fn /\ fn_has_code sa sx fn /\ fn_has_code sx sb fn /\
  fn_has_code sb se fn /\ fn_has_code se ss fn /\ fn_has_code ss sc fn /\
  fn_has_code sc sd fn /\ fn_has_code sd s0 fn /\ fn_has_code s0 s1 fn /\
  fn_has_code s1 s2 fn /\ fn_has_code s2 sfcomp fn /\
  sa.cs_current_bb = body_lbl /\ sa.cs_current_insts = [] /\
  sc.cs_current_bb = exit_lbl /\ sc.cs_current_insts = [] /\
  ~ctx_has_dalloca ctx /\
  not_fresh_at sh ip /\ not_fresh_at sh cursor /\ not_fresh_at sh src /\
  not_fresh_at sh dst /\ not_fresh_at sh cv /\ not_fresh_at sh parent /\
  not_fresh_at sa ip /\ not_fresh_at sa cursor /\ not_fresh_at sa src /\
  not_fresh_at sa dst /\ not_fresh_at sa cv /\
  not_fresh_at sb head /\ not_fresh_at sb off /\ not_fresh_at sb idx /\
  not_fresh_at sc cursor /\ not_fresh_at sc parent /\
  not_fresh_at sd parent /\ not_fresh_at sd encoded /\
  (!x. not_fresh_at sh x ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
  (!x. not_fresh_at sb x ==> not_fresh_at se x) /\
  (!x. not_fresh_at se x ==> not_fresh_at ss x) /\
  (!x. not_fresh_at sh x ==> not_fresh_at sc x) /\
  (!x. not_fresh_at sh x ==> not_fresh_at sd x) /\
  encoder_dynamic_loop_inv ctx fn (sites DELETE oid) ((oid,r,32)::protected)
    ip cursor src dst cv p c a b scap dcap
    (ArrayTV tv (Dynamic limit)) (ArrayV (DynArrayV vs)) N ns 0 G tn s /\
  encoder_resource ctx fn sites a scap protected s /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
  lookup_var parent s = SOME (n2w r) /\ ptr_covers G tn parent s 32 /\
  mload r s = 0w /\ (!i. r <= i /\ i < r+32 ==> i NOTIN tn.t_mem) /\
  r+32 < dimword(:256) /\ regions_disjoint (r,32) (b,dcap) /\
  oid IN sites /\ FLOOKUP s.vs_allocas oid = SOME (r,32) /\
  (!i. b <= i /\ i < b+32 ==> i NOTIN tn.t_mem) /\
  N = LENGTH vs /\ LENGTH ns = N /\ LENGTH avs = N /\ LENGTH costs = N /\
  evaluate_type env ty = SOME tv /\ msz = type_memory_size tv /\
  value_has_type (ArrayTV tv (Dynamic limit)) (ArrayV (DynArrayV vs)) /\
  (!i. i<N ==> vyper_to_abi env ty (EL i vs) = SOME (EL i avs) /\
    EL i ns = LENGTH (enc (vyper_to_abi_type env ty) (EL i avs))) /\
  vyper_to_abi env (ArrayT ty (Dynamic limit)) (ArrayV (DynArrayV vs)) = SOME av /\
  LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic limit))) av) =
    32+32*N+SUM ns /\
  N < dimword(:256) /\ 32+32*N+SUM ns <= dcap /\
  val_wf (ArrayTV tv (Dynamic limit)) (ArrayV (DynArrayV vs)) /\
  val_footprint (ArrayTV tv (Dynamic limit)) (ArrayV (DynArrayV vs)) <= scap /\
  regions_disjoint (p,32) (c,32) /\
  regions_disjoint (p,32) (b,dcap) /\ regions_disjoint (c,32) (b,dcap) /\
  regions_disjoint (a,scap) (p,32) /\ regions_disjoint (a,scap) (c,32) /\
  regions_disjoint (a,scap) (b,dcap) /\ 32 <= scap /\
  FLOOKUP s.vs_allocas pid = SOME (p,32) /\ pid IN sites DELETE oid /\ pid NOTIN children /\
  FLOOKUP s.vs_allocas cid = SOME (c,32) /\ cid IN sites DELETE oid /\ cid NOTIN children /\
  MEM (did,dbase,dsize) protected /\ dbase <= b /\ b+dcap <= dbase+dsize /\
  children SUBSET sites DELETE oid /\
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
      ((pid,p,32)::(cid,c,32)::(oid,r,32)::protected) sp ==>
    ?n Gm tnm sm. encoder_semantic_framed_result env ty (EL i vs)
      D ctx fn PG sb se children a scap
      ((pid,p,32)::(cid,c,32)::(oid,r,32)::protected) (b+32+(32*N+SUM (TAKE i ns)))
      (cap i) len n (EL i costs) Gp tnp sp Gm tnm sm) ==>
  ?Gf tnf sf.
    encoder_semantic_framed_result env (ArrayT ty (Dynamic limit))
      (ArrayV (DynArrayV vs)) D ctx fn PG sh sfcomp sites a scap protected
      b dcap (Var out) (32+32*N+SUM ns) (SUM costs) G tn s Gf tnf sf /\
    32+32*N+SUM ns <= dcap
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM (did,dbase,dsize) ((oid,r,32)::protected)` by simp[] >>
  mp_tac (encoder_semantic_dynamic_inner_loop_counted_ptr |>
    Q.INST [`sites` |-> `sites DELETE oid`,
            `protected` |-> `(oid,r,32)::protected`]) >>
  (impl_tac >- asm_rewrite_tac []) >> strip_tac >>
  `encoder_resource ctx fn (sites DELETE oid) a scap
     ((oid,r,32)::protected) sf` by fs[encoder_dynamic_loop_inv_def] >>
  drule_all encoder_dynamic_effect_parent_word >> strip_tac >>
  qpat_assum `encoder_dynamic_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sf`
    (strip_assume_tac o PURE_REWRITE_RULE [encoder_dynamic_loop_inv_def]) >>
  `sf.vs_current_bb = sc.cs_current_bb /\
   sf.vs_inst_idx = LENGTH sc.cs_current_insts` by simp[] >>
  `ptr_covers Gf tnf src sf 32` by
    (qpat_assum `ptr_covers Gf tnf src sf scap` mp_tac >>
     qpat_assum `32 <= scap` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[ptr_covers_def] >> rpt strip_tac >>
     simp[]) >>
  `!i. a <= i /\ i < a+32 ==> i NOTIN tnf.t_mem` by
    metis_tac[robust_dynamic_source_length_clean] >>
  `a < dimword(:256) /\ c < dimword(:256) /\ r < dimword(:256)` by decide_tac >>
  `!i. w2n (n2w a : bytes32) <= i /\
     i < w2n (n2w a : bytes32)+32 ==> i NOTIN tnf.t_mem` by
    simp[w2n_n2w, LESS_MOD] >>
  drule_all abi_array_dynamic_exit_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `lookup_var parent sf' = SOME (n2w r) /\
   ptr_covers Gf' tnf' parent sf' 32 /\ mload r sf' = 0w /\
   (!i. r <= i /\ i < r+32 ==> i NOTIN tnf'.t_mem)` by
    (qpat_assum `!v. not_fresh_at sc v ==> _` (qspec_then `parent` mp_tac) >>
     simp[] >> strip_tac >> fs[ptr_covers_def, mload_def]) >>
  drule_all encoder_dynamic_parent_finish_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s (SUM costs) Gf' tnf' (OK sf')` by
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `SUM costs`, `m` |-> `0`] |> SRULE []) >>
     qexistsl [`Gf`,`sf`,`tnf`] >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s (SUM costs) Gf'' tnf'' (OK sf'')` by
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `SUM costs`, `m` |-> `0`] |> SRULE []) >>
     qexistsl [`Gf'`,`sf'`,`tnf'`] >> simp[]) >>
  `encoder_resource ctx fn (sites DELETE oid) a scap protected sf` by
    (qpat_assum `encoder_resource _ _ _ _ _ ((oid,r,32)::protected) sf` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[encoder_resource_def] >> metis_tac[]) >>
  `encoder_resource ctx fn sites a scap protected sf` by
    (irule encoder_resource_restore_parent >> qexistsl [`oid`,`s`] >>
     fs[encoder_dynamic_effect_def]) >>
  `encoder_resource ctx fn sites a scap protected sf''` by
    (irule encoder_resource_fields >> qexists `sf` >> simp[]) >>
  qexistsl [`Gf''`,`tnf''`,`sf''`] >>
  pure_rewrite_tac [encoder_semantic_framed_result_def] >>
  reverse conj_tac >- simp[] >>
  reverse conj_tac >- (qexists `av` >> simp[]) >>
  pure_rewrite_tac [encoder_framed_child_result_def] >>
  `TAKE N ns = ns` by metis_tac[TAKE_LENGTH_ID] >>
  conj_tac >- asm_rewrite_tac [] >>
  conj_tac >- asm_rewrite_tac [] >>
  conj_tac >- asm_rewrite_tac [] >>
  conj_tac >- asm_rewrite_tac [] >>
  conj_tac >- metis_tac[eval_operand_def, ADD_ASSOC] >>
  conj_tac >- asm_rewrite_tac [] >>
  conj_tac >-
    (qpat_assum `regions_disjoint (r,32) (b,dcap)` mp_tac >>
     pure_rewrite_tac [regions_disjoint_def] >> strip_tac >>
     gen_tac >> strip_tac >>
     `i < r \/ r+32 <= i` by decide_tac >>
     `i NOTIN tnf.t_mem` by
       (Cases_on `i < b+32` >- metis_tac[] >>
        Cases_on `i < b+32+32*N` >- simp[] >>
        qpat_assum `!i. b+32+32*N <= i /\ _ ==> _` irule >>
        asm_rewrite_tac [] >> decide_tac) >>
     metis_tac[]) >>
  conj_tac >- asm_rewrite_tac [] >>
  qpat_assum `encoder_dynamic_effect sh _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [encoder_dynamic_effect_def]) >>
  `encoder_write_envelope (sites DELETE oid) sf b dcap SUBSET
     encoder_write_envelope sites sf'' b dcap` by
    (simp[encoder_write_envelope_def, encoder_scratch_span_def, SUBSET_DEF] >>
     metis_tac[]) >>
  `!i. r <= i /\ i < r+32 ==> i IN encoder_write_envelope sites sf'' b dcap` by
    (simp[encoder_write_envelope_def, encoder_scratch_span_def] >> metis_tac[]) >>
  conj_tac >-
    (mp_tac (Q.SPECL [`sf'`,`r`,`n2w (32+(32*N+SUM (TAKE N ns)))`]
       wordLoadStorePtrTheory.mstore_memory_frame) >>
     fs[mem_agree_outside_def, SUBSET_DEF] >> metis_tac[]) >>
  conj_tac >-
    (gen_tac >> strip_tac >>
     `i NOTIN encoder_write_envelope (sites DELETE oid) sf b dcap` by
       metis_tac[SUBSET_DEF] >>
     `i < r \/ r+32 <= i` by
       (`~(r <= i /\ i < r+32)` by metis_tac[] >> decide_tac) >>
     metis_tac[]) >>
  conj_tac >- asm_rewrite_tac [] >>
  conj_tac >- (rpt strip_tac >> asm_rewrite_tac [] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> asm_rewrite_tac [] >> fs[IN_DELETE]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  fs[encoder_ambient_frame_def]
QED
