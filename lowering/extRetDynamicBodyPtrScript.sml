Theory extRetDynamicBodyPtr
Ancestors
  extRetDynamicPreparePtr extRetFramedChildPtr extRetRecursiveChildPtr
  extRetRecursiveResourcePtr extRetRecursiveFramePtr extRetScratchResourcePtr
  extRetAbiChildComposePtr extRetAbiChildBoundaryPtr extRetLoopTailAmbientPtr
  extRetNumericLedgerPtr abiEncoderArrayDynamicMemory abiEncoderArrayBodyCode
  abiEncoderArrayTail abiEncoderChildCode abiDecoderLoopEmit fragGasPathPtr
  fragExec compileEnv bodyPtrDefs ptrDiscipline venomState venomExecSemantics
  venomMemDefs venomMemProps valueEncoding valueEncodingProps valueEncodingProofs
  robustCopyTransportPtr valueTypingMemoryProps words finite_map pred_set
  arithmetic list rich_list

(* The initialized invariant does not include a compiler program counter.
   Thus header branching and the body transition share the same invariant. *)
Definition encoder_dynamic_loop_inv_def:
  encoder_dynamic_loop_inv ctx fn sites protected
    ip cursor src dst cv p c a b scap dcap tv v N ns j G tn s <=>
    ~s.vs_halted /\
    lookup_var ip s = SOME (n2w p) /\
    lookup_var cursor s = SOME (n2w c) /\
    lookup_var src s = SOME (n2w a) /\
    lookup_var dst s = SOME (n2w b) /\
    lookup_var cv s = SOME (n2w N) /\
    ptr_covers G tn ip s 32 /\ ptr_covers G tn cursor s 32 /\
    ptr_covers G tn src s scap /\ ptr_covers G tn dst s dcap /\
    mload p s = n2w j /\ mload c s = n2w (32*N+SUM (TAKE j ns)) /\
    (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) /\
    (!i. c <= i /\ i < c+32 ==> i NOTIN tn.t_mem) /\
    op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v a mem) /\
    (!i. b+32 <= i /\ i < b+32+32*j ==> i NOTIN tn.t_mem) /\
    (!i. b+32+32*N <= i /\ i < b+32+(32*N+SUM (TAKE j ns)) ==>
      i NOTIN tn.t_mem) /\
    encoder_resource ctx fn sites a scap protected s
End

Definition encoder_dynamic_effect_def:
  encoder_dynamic_effect sa sites b cap G tn s Gf tnf sf <=>
    mem_agree_outside (encoder_write_envelope sites sf b cap)
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN encoder_write_envelope sites sf b cap ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    s.vs_alloca_next <= sf.vs_alloca_next /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP sf.vs_allocas aid = SOME (p,sz)) /\
    (!aid. aid NOTIN sites ==> FLOOKUP sf.vs_allocas aid = FLOOKUP s.vs_allocas aid) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    encoder_ambient_frame tn s tnf sf
End

Theorem encoder_dynamic_effect_refl:
  encoder_dynamic_effect sa sites b cap G tn s G tn s
Proof
  simp[encoder_dynamic_effect_def, mem_agree_outside_def,
       encoder_ambient_frame_def]
QED

Theorem encoder_dynamic_effect_then:
  encoder_dynamic_effect sa sites b cap G tn s Gm tnm sm /\
  encoder_dynamic_effect sa sites b cap Gm tnm sm Gf tnf sf ==>
  encoder_dynamic_effect sa sites b cap G tn s Gf tnf sf
Proof
  simp[encoder_dynamic_effect_def] >> strip_tac >>
  `encoder_write_envelope sites sm b cap SUBSET
    encoder_write_envelope sites sf b cap` by
    (irule encoder_envelope_registered_mono >> simp[]) >>
  conj_tac >-
    (fs[mem_agree_outside_def, SUBSET_DEF] >> metis_tac[]) >>
  conj_tac >- (fs[SUBSET_DEF] >> metis_tac[]) >>
  gvs[encoder_ambient_frame_def] >> metis_tac[]
QED

Theorem encoder_dynamic_loop_empty_prefixes:
  (!i:num. b+32 <= i /\ i < b+32+32*0 ==> i NOTIN t) /\
  (!i. b+32+32*N <= i /\ i < b+32+(32*N+SUM (TAKE 0 ns)) ==> i NOTIN t)
Proof
  simp[]
QED

Theorem encoder_dynamic_loop_completed_prefixes:
  encoder_dynamic_loop_inv ctx fn sites protected
    ip cursor src dst cv p c a b scap dcap tv v N ns N G tn s /\
  LENGTH ns = N ==>
  mload p s = n2w N /\ mload c s = n2w (32*N+SUM ns) /\
  (!i. b+32 <= i /\ i < b+32+32*N ==> i NOTIN tn.t_mem) /\
  (!i. b+32+32*N <= i /\ i < b+32+(32*N+SUM ns) ==> i NOTIN tn.t_mem)
Proof
  simp[encoder_dynamic_loop_inv_def] >> metis_tac[TAKE_LENGTH_ID]
QED

Theorem encoder_dynamic_loop_inv_memory_frame:
  encoder_dynamic_loop_inv ctx fn sites protected
    ip cursor src dst cv p c a b scap dcap tv v N ns j G tn s /\
  not_fresh_at sh ip /\ not_fresh_at sh cursor /\ not_fresh_at sh src /\
  not_fresh_at sh dst /\ not_fresh_at sh cv /\
  ~sf.vs_halted /\ sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
  sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
  sf.vs_fmp = s.vs_fmp /\
  (!x. not_fresh_at sh x ==>
    lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)) ==>
  encoder_dynamic_loop_inv ctx fn sites protected
    ip cursor src dst cv p c a b scap dcap tv v N ns j Gf tnf sf
Proof
  strip_tac >>
  `encoder_resource ctx fn sites a scap protected sf` by
    (irule encoder_resource_fields >> metis_tac[encoder_dynamic_loop_inv_def]) >>
  gvs[encoder_dynamic_loop_inv_def, mload_def, ptr_covers_def, op_prov_def] >>
  metis_tac[]
QED

(* A single execution witness supplies the exact three stores, all allocation
   fields and all six ambient fields. The recursive length is an operand. *)
Theorem encoder_dynamic_finish_counted_ptr:
  abi_encode_child_suffix (Var head) (Var cursor) (Var off) len sa = (len,sb) /\
  abi_decode_loop_suffix (Var ip) (Var idx) hdr exit_lbl sb = ((),sc) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  not_fresh_at sa head /\ not_fresh_at sa cursor /\
  not_fresh_at sa ip /\ not_fresh_at sa idx /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
  lookup_var head s = SOME (n2w h) /\ h < dimword(:256) /\
  ptr_covers G tn head s 32 /\
  lookup_var cursor s = SOME (n2w c) /\ c < dimword(:256) /\
  ptr_covers G tn cursor s 32 /\
  lookup_var off s = SOME (n2w k) /\ op_taint tn (Var off) = {} /\
  eval_operand len s = SOME (n2w n) /\ op_taint tn len = {} /\
  lookup_var idx s = SOME (n2w j) /\ op_taint tn (Var idx) = {} /\
  lookup_var ip s = SOME (n2w p) /\ ptr_covers G tn ip s 32 /\
  p+32 < dimword(:256) /\ j+1 < dimword(:256) /\ k+n < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = hdr /\ sf.vs_inst_idx = 0 /\ ~sf.vs_halted /\
    sf.vs_memory = (mstore p (n2w (j+1))
      (mstore c (n2w (k+n)) (mstore h (n2w k) s))).vs_memory /\
    tnf.t_mem = ((tn.t_mem DIFF {i | h <= i /\ i < h+32}) DIFF
      {i | c <= i /\ i < c+32}) DIFF {i | p <= i /\ i < p+32} /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    encoder_ambient_frame tn s tnf sf
Proof
  strip_tac >> drule_all abi_child_suffix_operand_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `lookup_var ip sf = SOME (n2w p) /\ ptr_covers Gf tnf ip sf 32 /\
   eval_operand (Var idx) sf = SOME (n2w j) /\ op_taint tnf (Var idx) = {} /\
   not_fresh_at sb ip /\ w2n (n2w p : bytes32)+32 < dimword(:256)` by
    (gvs[ptr_covers_def, eval_operand_def, w2n_n2w, LESS_MOD] >> metis_tac[]) >>
  drule_all abi_decode_loop_suffix_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`Gf'`,`tnf'`,`sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`,`m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`,`sf`,`tnf`] >> simp[]) >>
  simp[w2n_n2w, LESS_MOD, encoder_ambient_frame_def] >>
  qpat_x_assum `sf.vs_memory = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  MATCH_ACCEPT_TAC immutableCopyExecutionTheory.immutable_mstore_memory_cong
QED

Theorem encoder_dynamic_three_store_frame:
  mem_agree_outside
    ({i | h <= i /\ i < h+32} UNION {i | c <= i /\ i < c+32} UNION
     {i | p <= i /\ i < p+32})
    (mstore p z (mstore c y (mstore h x s))).vs_memory s.vs_memory
Proof
  irule encoder_memory_frame_union >>
  qexists_tac `(mstore c y (mstore h x s)).vs_memory` >>
  conj_tac >-
    (irule encoder_memory_frame_union >>
     qexists_tac `(mstore h x s).vs_memory` >>
     simp[wordLoadStorePtrTheory.mstore_memory_frame]) >>
  simp[wordLoadStorePtrTheory.mstore_memory_frame]
QED

Theorem encoder_dynamic_finish_exterior:
  sf.vs_memory = (mstore p z (mstore c y (mstore h x s))).vs_memory /\
  tnf.t_mem = ((tn.t_mem DIFF {i | h <= i /\ i < h+32}) DIFF
    {i | c <= i /\ i < c+32}) DIFF {i | p <= i /\ i < p+32} /\
  {i | h <= i /\ i < h+32} SUBSET writes /\
  {i | c <= i /\ i < c+32} SUBSET writes /\
  {i | p <= i /\ i < p+32} SUBSET writes ==>
  mem_agree_outside writes sf.vs_memory s.vs_memory /\
  (!i. i NOTIN writes ==> (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >> conj_tac >-
    (irule encoder_memory_frame_mono >>
     asm_rewrite_tac [] >>
     irule_at Any encoder_dynamic_three_store_frame >>
     fs[SUBSET_DEF] >> metis_tac[]) >>
  fs[SUBSET_DEF, IN_DIFF] >> metis_tac[]
QED

(* Finish transport is independent of the recursive implementation. The child
   has already cleaned its new tail; the concrete suffix cleans the new head. *)
Theorem encoder_dynamic_finish_invariant:
  encoder_dynamic_loop_inv ctx fn sites protected
    ip cursor src dst cv p c a b scap dcap tv v N ns j G tn s /\
  j < LENGTH ns /\ val_wf tv v /\
  regions_disjoint (p,32) (c,32) /\
  (!i. a <= i /\ i < a+val_footprint tv v ==>
    i NOTIN ({i | b+32+32*j <= i /\ i < b+32+32*j+32} UNION
      {i | c <= i /\ i < c+32} UNION {i | p <= i /\ i < p+32})) /\
  (!i. b+32+32*N <= i /\
    i < b+32+(32*N+SUM (TAKE j ns)+EL j ns) ==> i NOTIN tn.t_mem) /\
  ~sf.vs_halted /\
  sf.vs_memory = (mstore p (n2w (j+1))
    (mstore c (n2w (32*N+SUM (TAKE j ns)+EL j ns))
      (mstore (b+32+32*j) (n2w (32*N+SUM (TAKE j ns))) s))).vs_memory /\
  tnf.t_mem = ((tn.t_mem DIFF
    {i | b+32+32*j <= i /\ i < b+32+32*j+32}) DIFF
    {i | c <= i /\ i < c+32}) DIFF {i | p <= i /\ i < p+32} /\
  sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
  sf.vs_fmp = s.vs_fmp /\
  (!x. x = ip \/ x = cursor \/ x = src \/ x = dst \/ x = cv ==>
    lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)) ==>
  encoder_dynamic_loop_inv ctx fn sites protected
    ip cursor src dst cv p c a b scap dcap tv v N ns (j+1) Gf tnf sf
Proof
  strip_tac >>
  `encoder_resource ctx fn sites a scap protected sf` by
    (irule encoder_resource_fields >> metis_tac[encoder_dynamic_loop_inv_def]) >>
  `32*N+SUM (TAKE (j+1) ns) = 32*N+SUM (TAKE j ns)+EL j ns` by
    metis_tac[TAKE_SUC_BY_TAKE, GSYM ADD1, SUM_SNOC, ADD_ASSOC] >>
  `!mem. mem_agree_outside tnf.t_mem sf.vs_memory mem ==>
    val_in_memory tv v a mem` by
    (gen_tac >> strip_tac >> irule robust_val_in_memory_exterior_frame >>
     conj_tac >- simp[] >>
     qexistsl_tac [`s.vs_memory`, `sf.vs_memory`, `tn.t_mem`, `tnf.t_mem`] >>
     qexists_tac `({i | b+32+32*j <= i /\ i < b+32+32*j+32} UNION
       {i | c <= i /\ i < c+32} UNION {i | p <= i /\ i < p+32})` >>
     simp[] >> conj_tac >- metis_tac[encoder_dynamic_loop_inv_def] >>
     `mem_agree_outside
       ({i | b+32+32*j <= i /\ i < b+32+32*j+32} UNION
        {i | c <= i /\ i < c+32} UNION {i | p <= i /\ i < p+32})
       sf.vs_memory s.vs_memory` by
       (asm_rewrite_tac [] >> irule encoder_dynamic_three_store_frame) >>
     gvs[mem_agree_outside_def] >> metis_tac[]) >>
  gvs[encoder_dynamic_loop_inv_def, ptr_covers_def, op_prov_def] >>
  conj_tac >- metis_tac[mload_def, mload_mstore_same] >>
  conj_tac >- metis_tac[mload_def, mload_mstore_same, mload_mstore_disjoint,
                       regions_disjoint_def] >>
  rpt conj_tac >> rpt strip_tac >>
  Cases_on `i < b+32+32*j` >- (gvs[] >> metis_tac[]) >> decide_tac
QED

Theorem encoder_dynamic_subregion_exterior[local]:
  scratch_resource ctx fn sites q cap s /\
  q <= r /\ r+len <= q+cap /\ regions_disjoint (r,len) (dst,dlen) ==>
  !i. r <= i /\ i < r+len ==> i NOTIN encoder_write_envelope sites s dst dlen
Proof
  strip_tac >> gen_tac >> strip_tac >>
  simp[encoder_write_envelope_def, encoder_scratch_span_def] >>
  conj_tac >- (fs[regions_disjoint_def] >> decide_tac) >>
  rpt gen_tac >> strip_tac >> spose_not_then strip_assume_tac >>
  `cap <> 0` by decide_tac >>
  fs[scratch_resource_def] >>
  `regions_disjoint (q,cap) (b,n)` by metis_tac[] >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem encoder_dynamic_inv_exterior_frame[local]:
  encoder_dynamic_loop_inv ctx fn sites protected
    ip cursor src dst cv p c a b scap dcap tv v N ns j G tn s /\
  val_wf tv v /\
  mem_agree_outside writes sf.vs_memory s.vs_memory /\
  (!i. i NOTIN writes ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN writes) /\
  (!i. c <= i /\ i < c+32 ==> i NOTIN writes) /\
  (!i. a <= i /\ i < a+val_footprint tv v ==> i NOTIN writes) /\
  (!i. b+32 <= i /\ i < b+32+32*j ==> i NOTIN writes) /\
  (!i. b+32+32*N <= i /\ i < b+32+(32*N+SUM (TAKE j ns)) ==> i NOTIN writes) /\
  ~sf.vs_halted /\ encoder_resource ctx fn sites a scap protected sf /\
  (!x. x = ip \/ x = cursor \/ x = src \/ x = dst \/ x = cv ==>
    lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)) ==>
  encoder_dynamic_loop_inv ctx fn sites protected
    ip cursor src dst cv p c a b scap dcap tv v N ns j Gf tnf sf
Proof
  strip_tac >>
  `(!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) /\
   (!i. c <= i /\ i < c+32 ==> i NOTIN tn.t_mem) /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v a mem)` by
    gvs[encoder_dynamic_loop_inv_def] >>
  `mload p sf = mload p s /\ (!i. p <= i /\ i < p+32 ==> i NOTIN tnf.t_mem)` by
    (irule encoder_frame_clean_word >> qexistsl_tac [`tn`,`writes`] >> simp[]) >>
  `mload c sf = mload c s /\ (!i. c <= i /\ i < c+32 ==> i NOTIN tnf.t_mem)` by
    (irule encoder_frame_clean_word >> qexistsl_tac [`tn`,`writes`] >> simp[]) >>
  `!mem. mem_agree_outside tnf.t_mem sf.vs_memory mem ==> val_in_memory tv v a mem` by
    (gen_tac >> strip_tac >> irule robust_val_in_memory_exterior_frame >>
     conj_tac >- simp[] >>
     qexistsl_tac [`s.vs_memory`,`sf.vs_memory`,`tn.t_mem`,`tnf.t_mem`,`writes`] >>
     gvs[mem_agree_outside_def]) >>
  gvs[encoder_dynamic_loop_inv_def, ptr_covers_def, op_prov_def] >> metis_tac[]
QED

Theorem encoder_dynamic_body_backedge_counted_ptr:
  abi_encode_array_addresses (Var ip) (Var src) (Var dst) 32 msz sa =
    (((Var idx,Var child_src),(Var data,Var head)),sx) /\
  abi_encode_array_tail (Var data) (Var cursor) sx =
    ((Var off,Var child_dst),sb) /\
  compile_abi_encode_to_buf (Var child_dst) (Var child_src) ei sb = (len,se) /\
  abi_encode_child_suffix (Var head) (Var cursor) (Var off) len se = (len,ss) /\
  abi_decode_loop_suffix (Var ip) (Var idx) hdr exit_lbl ss = ((),sc) /\
  fn_has_code sa sx fn /\ fn_has_code sx sb fn /\ fn_has_code sb se fn /\
  fn_has_code se ss fn /\ fn_has_code ss sc fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~ctx_has_dalloca ctx /\
  not_fresh_at sa ip /\ not_fresh_at sa cursor /\ not_fresh_at sa src /\
  not_fresh_at sa dst /\ not_fresh_at sa cv /\
  not_fresh_at sb head /\ not_fresh_at sb off /\ not_fresh_at sb idx /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
  (!x. not_fresh_at sb x ==> not_fresh_at se x) /\
  (!x. not_fresh_at se x ==> not_fresh_at ss x) /\
  encoder_dynamic_loop_inv ctx fn sites protected
    ip cursor src dst cv p c a b scap dcap tv v N ns j G tn s /\
  j < N /\ LENGTH ns = N /\ k = 32*N+SUM (TAKE j ns) /\ n = EL j ns /\
  n <= capj /\ 32+k+capj <= dcap /\ 32+j*msz+msz <= scap /\
  val_wf tv v /\ val_footprint tv v <= scap /\
  regions_disjoint (p,32) (c,32) /\
  regions_disjoint (p,32) (b,dcap) /\
  regions_disjoint (c,32) (b,dcap) /\
  regions_disjoint (a,scap) (p,32) /\
  regions_disjoint (a,scap) (c,32) /\
  regions_disjoint (a,scap) (b,dcap) /\
  FLOOKUP s.vs_allocas pid = SOME (p,32) /\ pid IN sites /\ pid NOTIN children /\
  FLOOKUP s.vs_allocas cid = SOME (c,32) /\ cid IN sites /\ cid NOTIN children /\
  MEM (did,dbase,dsize) protected /\ dbase <= b /\ b+dcap <= dbase+dsize /\
  children SUBSET sites /\
  p+32 < dimword(:256) /\ c+32 < dimword(:256) /\
  a+scap < dimword(:256) /\ b+dcap < dimword(:256) /\
  j+1 < dimword(:256) /\ k+n < dimword(:256) /\
  (!Gp tnp sp.
    sp.vs_current_bb = sb.cs_current_bb /\
    sp.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sp.vs_halted /\
    lookup_var child_src sp = SOME (n2w (a+32+j*msz)) /\
    ptr_covers Gp tnp child_src sp msz /\
    lookup_var child_dst sp = SOME (n2w (b+32+k)) /\
    ptr_covers Gp tnp child_dst sp capj /\
    (!mem. mem_agree_outside tnp.t_mem sp.vs_memory mem ==>
       val_in_memory tv v a mem) /\
    encoder_resource ctx fn children a scap
      ((pid,p,32)::(cid,c,32)::protected) sp ==>
    ?Gm tnm sm. encoder_framed_child_result D ctx fn PG sb se children a scap
      ((pid,p,32)::(cid,c,32)::protected) (b+32+k) capj len n cost
      Gp tnp sp Gm tnm sm) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s cost Gf tnf (OK sf) /\
    sf.vs_current_bb = hdr /\ sf.vs_inst_idx = 0 /\
    encoder_dynamic_loop_inv ctx fn sites protected
      ip cursor src dst cv p c a b scap dcap tv v N ns (j+1) Gf tnf sf /\
    encoder_dynamic_effect sa sites b dcap G tn s Gf tnf sf
Proof
  strip_tac >>
  `~s.vs_halted /\ lookup_var ip s = SOME (n2w p) /\
   lookup_var cursor s = SOME (n2w c) /\
   lookup_var src s = SOME (n2w a) /\ lookup_var dst s = SOME (n2w b) /\
   ptr_covers G tn ip s 32 /\ ptr_covers G tn cursor s 32 /\
   ptr_covers G tn src s scap /\ ptr_covers G tn dst s dcap /\
   mload p s = n2w j /\ mload c s = n2w k /\
   (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) /\
   (!i. c <= i /\ i < c+32 ==> i NOTIN tn.t_mem)` by
    gvs[encoder_dynamic_loop_inv_def] >>
  `w2n (n2w a : bytes32) = a /\ w2n (n2w b : bytes32) = b /\
   w2n (n2w p : bytes32) = p /\ c < dimword(:256) /\
   32+j*32+32 <= dcap /\ 32+k+capj <= dcap` by
    (`a < dimword(:256) /\ b < dimword(:256) /\ p < dimword(:256)` by decide_tac >>
     simp[w2n_n2w, LESS_MOD] >> decide_tac) >>
  `mload (w2n (n2w p : bytes32)) s = n2w j /\
   (!i. w2n (n2w p : bytes32) <= i /\ i < w2n (n2w p : bytes32)+32 ==>
     i NOTIN tn.t_mem) /\
   w2n (n2w a : bytes32)+scap < dimword(:256) /\
   w2n (n2w b : bytes32)+dcap < dimword(:256)` by simp[] >>
  drule_all abi_array_prepare_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`]
    (qx_choose_then `Gp` (qx_choose_then `tnp` (qx_choose_then `sp` strip_assume_tac)))) >>
  `encoder_resource ctx fn sites a scap protected s /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v a mem)` by
    gvs[encoder_dynamic_loop_inv_def] >>
  `encoder_resource ctx fn sites a scap protected sp` by
    (irule encoder_resource_fields >> qexists_tac `s` >> simp[]) >>
  `encoder_resource ctx fn children a scap ((cid,c,32)::protected) sp` by
    (irule encoder_resource_push >> simp[] >> qexists_tac `sites` >> simp[]) >>
  `encoder_resource ctx fn children a scap ((pid,p,32)::(cid,c,32)::protected) sp` by
    (irule encoder_resource_push >> simp[] >> qexists_tac `children` >> simp[]) >>
  `!mem. mem_agree_outside tnp.t_mem sp.vs_memory mem ==> val_in_memory tv v a mem` by
    simp[] >>
  qpat_x_assum `!Gp tnp sp. _` (qspecl_then [`Gp`,`tnp`,`sp`] mp_tac) >>
  simp[] >>
  disch_then (qx_choose_then `Gm` (qx_choose_then `tnm` (qx_choose_then `sm` assume_tac))) >>
  qhdtm_assum `encoder_framed_child_result` mp_tac >>
  pure_rewrite_tac[encoder_framed_child_result_def] >> strip_tac >>
  `scratch_resource ctx fn children a scap sm` by
    gvs[encoder_resource_def] >>
  `scratch_resource ctx fn sites a scap sp` by
    gvs[encoder_resource_def] >>
  `scratch_resource ctx fn sites a scap sm` by
    (irule encoder_child_scratch_restore >> qexistsl_tac [`children`,`sp`] >> simp[]) >>
  `encoder_resource ctx fn sites a scap protected sm` by
    (irule encoder_child_resource_restore >> simp[] >> qexists_tac `sp` >> simp[]) >>
  `scratch_resource ctx fn children p 32 sm /\
   scratch_resource ctx fn children c 32 sm /\
   scratch_resource ctx fn children dbase dsize sm` by
    (qpat_assum `encoder_resource _ _ children _ _ _ sm`
       (strip_assume_tac o SRULE [encoder_resource_def]) >>
     first_assum (qspecl_then [`did`,`dbase`,`dsize`] mp_tac) >> simp[] >> strip_tac >>
     first_assum (qspecl_then [`cid`,`c`,`32`] mp_tac) >> simp[] >> strip_tac >>
     first_assum (qspecl_then [`pid`,`p`,`32`] mp_tac) >> simp[]) >>
  `!i. p <= i /\ i < p+32 ==>
    i NOTIN encoder_write_envelope children sm (b+32+k) capj` by
    (match_mp_tac (encoder_dynamic_subregion_exterior |> Q.INST [`q` |-> `p`, `cap` |-> `32`]) >>
     simp[] >>
     qpat_assum `regions_disjoint (p,32) (b,dcap)` mp_tac >>
     qpat_assum `32+k+capj <= dcap` mp_tac >>
     qpat_assum `k = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[regions_disjoint_def] >> decide_tac) >>
  `!i. c <= i /\ i < c+32 ==>
    i NOTIN encoder_write_envelope children sm (b+32+k) capj` by
    (match_mp_tac (encoder_dynamic_subregion_exterior |> Q.INST [`q` |-> `c`, `cap` |-> `32`]) >>
     simp[] >>
     qpat_assum `regions_disjoint (c,32) (b,dcap)` mp_tac >>
     qpat_assum `32+k+capj <= dcap` mp_tac >> qpat_assum `k = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[regions_disjoint_def] >> decide_tac) >>
  `!i. a <= i /\ i < a+scap ==>
    i NOTIN encoder_write_envelope children sm (b+32+k) capj` by
    (match_mp_tac (encoder_dynamic_subregion_exterior |> Q.INST [`q` |-> `a`, `cap` |-> `scap`]) >>
     simp[] >>
     qpat_assum `regions_disjoint (a,scap) (b,dcap)` mp_tac >>
     qpat_assum `32+k+capj <= dcap` mp_tac >> qpat_assum `k = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[regions_disjoint_def] >> decide_tac) >>
  `!i. b+32 <= i /\ i < b+32+32*j ==>
    i NOTIN encoder_write_envelope children sm (b+32+k) capj` by
    (match_mp_tac (encoder_dynamic_subregion_exterior |>
       Q.INST [`q` |-> `dbase`, `cap` |-> `dsize`]) >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `!i. b+32 <= i /\ i < b+32+k ==>
    i NOTIN encoder_write_envelope children sm (b+32+k) capj` by
    (match_mp_tac (encoder_dynamic_subregion_exterior |>
       Q.INST [`q` |-> `dbase`, `cap` |-> `dsize`]) >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `encoder_dynamic_loop_inv ctx fn sites protected
    ip cursor src dst cv p c a b scap dcap tv v N ns j Gp tnp sp` by
    (irule encoder_dynamic_loop_inv_memory_frame >>
     conj_tac >- simp[] >> qexistsl_tac [`G`,`s`,`sa`,`tn`] >> simp[]) >>
  `encoder_dynamic_loop_inv ctx fn sites protected
    ip cursor src dst cv p c a b scap dcap tv v N ns j Gm tnm sm` by
    (irule encoder_dynamic_inv_exterior_frame >>
     conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
     qexistsl_tac [`Gp`,`sp`,`tnp`,`encoder_write_envelope children sm (b+32+k) capj`] >>
     simp[] >> conj_tac >- metis_tac[] >>
     qpat_assum `sp.vs_memory = _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  `lookup_var head sm = SOME (n2w (b+32+32*j)) /\
   ptr_covers Gm tnm head sm 32 /\
   lookup_var off sm = SOME (n2w k) /\ op_taint tnm (Var off) = {} /\
   lookup_var idx sm = SOME (n2w j) /\ op_taint tnm (Var idx) = {}` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `lookup_var cursor sm = SOME (n2w c) /\ ptr_covers Gm tnm cursor sm 32 /\
   lookup_var ip sm = SOME (n2w p) /\ ptr_covers Gm tnm ip sm 32` by
    gvs[encoder_dynamic_loop_inv_def] >>
  `not_fresh_at se head /\ not_fresh_at se cursor /\
   not_fresh_at se ip /\ not_fresh_at se idx /\
   b+32+32*j < dimword(:256) /\
   eval_operand len sm = SOME (n2w n)` by (simp[] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  drule_all encoder_dynamic_finish_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`]
    (qx_choose_then `Gf` (qx_choose_then `tnf` (qx_choose_then `sf` strip_assume_tac)))) >>
  `!i. b+32+32*N <= i /\ i < b+32+(32*N+SUM (TAKE j ns)+EL j ns) ==>
    i NOTIN tnm.t_mem` by
    (gen_tac >> strip_tac >> Cases_on `i < b+32+k`
     >- (qpat_assum `encoder_dynamic_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Gm tnm sm` mp_tac >>
         qpat_assum `i < b+32+k` mp_tac >>
         qpat_assum `b+32+32*N <= i` mp_tac >>
         qpat_assum `k = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[encoder_dynamic_loop_inv_def] >> rpt strip_tac >>
         qpat_assum `!i. 32*N+(b+32) <= i /\ _ ==> i NOTIN tnm.t_mem` irule >>
         decide_tac) >>
     qpat_assum `!i. _ <= i /\ i < _ + EL j ns ==> i NOTIN tnm.t_mem` irule >>
     simp[] >> decide_tac) >>
  `!i. a <= i /\ i < a+val_footprint tv v ==>
    i NOTIN ({i | b+32+32*j <= i /\ i < b+32+32*j+32} UNION
      {i | c <= i /\ i < c+32} UNION {i | p <= i /\ i < p+32})` by
    (qpat_assum `regions_disjoint (a,scap) (p,32)` mp_tac >>
     qpat_assum `regions_disjoint (a,scap) (c,32)` mp_tac >>
     qpat_assum `regions_disjoint (a,scap) (b,dcap)` mp_tac >>
     qpat_assum `val_footprint tv v <= scap` mp_tac >>
     qpat_assum `32+j*32+32 <= dcap` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[regions_disjoint_def] >> decide_tac) >>
  `encoder_dynamic_loop_inv ctx fn sites protected
    ip cursor src dst cv p c a b scap dcap tv v N ns (j+1) Gf tnf sf` by
    (irule encoder_dynamic_finish_invariant >>
     simp[] >> qexistsl_tac [`Gm`,`sm`,`tnm`] >> simp[] >>
     rpt strip_tac >> metis_tac[]) >>
  `encoder_write_envelope children sm (b+32+k) capj SUBSET
    encoder_write_envelope sites sf b dcap` by
    (qpat_assum `sf.vs_allocas = sm.vs_allocas` mp_tac >>
     qpat_assum `children SUBSET sites` mp_tac >>
     qpat_assum `32+k+capj <= dcap` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >> strip_tac >> strip_tac >>
     simp[encoder_write_envelope_def, encoder_scratch_span_def, SUBSET_DEF] >>
     rpt strip_tac >> gvs[] >> metis_tac[SUBSET_DEF]) >>
  `FLOOKUP sf.vs_allocas pid = SOME (p,32) /\
   FLOOKUP sf.vs_allocas cid = SOME (c,32)` by metis_tac[] >>
  `{i | b+32+32*j <= i /\ i < b+32+32*j+32} SUBSET
    encoder_write_envelope sites sf b dcap` by
    (simp[encoder_write_envelope_def, SUBSET_DEF] >> rpt strip_tac >>
     disj1_tac >> decide_tac) >>
  `{i | p <= i /\ i < p+32} SUBSET encoder_write_envelope sites sf b dcap /\
   {i | c <= i /\ i < c+32} SUBSET encoder_write_envelope sites sf b dcap` by
    (simp[encoder_write_envelope_def, encoder_scratch_span_def, SUBSET_DEF] >>
     conj_tac >> rpt strip_tac >> disj2_tac >> metis_tac[]) >>
  `mem_agree_outside (encoder_write_envelope sites sf b dcap)
     sf.vs_memory sm.vs_memory /\
   (!i. i NOTIN encoder_write_envelope sites sf b dcap ==>
      (i IN tnf.t_mem <=> i IN tnm.t_mem))` by
    (drule encoder_dynamic_finish_exterior >>
     disch_then (qspecl_then [`encoder_write_envelope sites sf b dcap`,`tnf`,`tnm`] mp_tac) >>
     simp[]) >>
  qexistsl_tac [`Gf`,`tnf`,`sf`] >> simp[] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gm`,`sm`,`tnm`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gp`,`sp`,`tnp`] >> simp[]) >>
  pure_rewrite_tac[encoder_dynamic_effect_def] >>
  conj_tac >-
    (qpat_assum `mem_agree_outside (encoder_write_envelope children _ _ _) _ _` mp_tac >>
     qpat_assum `mem_agree_outside (encoder_write_envelope sites _ _ _) _ _` mp_tac >>
     qpat_assum `encoder_write_envelope children _ _ _ SUBSET _` mp_tac >>
     qpat_assum `sp.vs_memory = s.vs_memory` mp_tac >>
     qpat_assum `k = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[mem_agree_outside_def, SUBSET_DEF] >> metis_tac[]) >>
  conj_tac >-
    (qpat_assum `!i. i NOTIN encoder_write_envelope children _ _ _ ==> _` mp_tac >>
     qpat_assum `!i. i NOTIN encoder_write_envelope sites _ _ _ ==> _` mp_tac >>
     qpat_assum `encoder_write_envelope children _ _ _ SUBSET _` mp_tac >>
     qpat_assum `tnp.t_mem = tn.t_mem` mp_tac >>
     qpat_assum `k = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[SUBSET_DEF] >> metis_tac[]) >>
  conj_tac >- (gvs[] >> decide_tac) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (fs[SUBSET_DEF] >> metis_tac[]) >>
  conj_tac >-
    (qpat_assum `!v. not_fresh_at sa v ==> _` mp_tac >>
     qpat_assum `!v. not_fresh_at sb v ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at se x ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sb x` mp_tac >>
     qpat_assum `!x. not_fresh_at sb x ==> not_fresh_at se x` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  gvs[encoder_ambient_frame_def]
QED
