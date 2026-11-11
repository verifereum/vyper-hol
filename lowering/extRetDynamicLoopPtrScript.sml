Theory extRetDynamicLoopPtr
Ancestors
  extRetDynamicBodyPtr extRetEvaluatedStaticLoopPtr extRetFramedChildPtr
  extRetRecursiveResourcePtr extRetNumericLedgerPtr abiEncoderArrayHeader
  abiEncoderArrayBodyCode abiEncoderArrayTail abiEncoderChildCode abiDecoderLoopEmit
  fragGasPathPtr fragExec compileEnv bodyPtrDefs ptrDiscipline venomState
  venomExecSemantics valueEncoding valueEncodingProofs words finite_map pred_set
  arithmetic list rich_list

Theorem encoder_dynamic_header_counted_ptr[local]:
  abi_encode_array_header (Var ip) (Var cv) sh = ((hdr,body_lbl,exit_lbl),sa) /\
  fn_has_code sh sa fn /\ ~ctx_has_dalloca ctx /\
  not_fresh_at sh ip /\ not_fresh_at sh cursor /\ not_fresh_at sh src /\
  not_fresh_at sh dst /\ not_fresh_at sh cv /\
  encoder_dynamic_loop_inv ctx fn sites protected
    ip cursor src dst cv p c a b scap dcap tv v N ns j G tn s /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
  p < dimword(:256) /\ j <= N /\ N < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = (if j<N then body_lbl else exit_lbl) /\
    sf.vs_inst_idx = 0 /\
    encoder_dynamic_loop_inv ctx fn sites protected
      ip cursor src dst cv p c a b scap dcap tv v N ns j Gf tnf sf /\
    encoder_dynamic_effect sh sites b dcap G tn s Gf tnf sf
Proof
  strip_tac >>
  qhdtm_assum `encoder_dynamic_loop_inv` mp_tac >>
  pure_rewrite_tac[encoder_dynamic_loop_inv_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `w2n (n2w p : bytes32) = p` by simp[w2n_n2w, LESS_MOD] >>
  `mload (w2n (n2w p : bytes32)) s = n2w j /\
   (!i. w2n (n2w p : bytes32) <= i /\ i < w2n (n2w p : bytes32)+32 ==>
     i NOTIN tn.t_mem)` by simp[] >>
  drule_all encoder_static_loop_header_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `encoder_dynamic_loop_inv ctx fn sites protected
    ip cursor src dst cv p c a b scap dcap tv v N ns j Gf tnf sf` by
    (irule encoder_dynamic_loop_inv_memory_frame >>
     conj_tac >- simp[] >> qexistsl_tac [`G`,`s`,`sh`,`tn`] >> simp[] >>
     simp[encoder_dynamic_loop_inv_def]) >>
  qexistsl_tac [`Gf`,`tnf`,`sf`] >>
  gvs[encoder_dynamic_loop_inv_def, encoder_dynamic_effect_def,
      encoder_ambient_frame_def, mem_agree_outside_def]
QED

Theorem encoder_dynamic_inner_loop_counted_ptr:
  !r j G tn s.
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
    ip cursor src dst cv p c a b scap dcap tv v N ns j G tn s /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ N = r+j /\
  LENGTH ns = N /\ LENGTH costs = N /\ N < dimword(:256) /\
  32+32*N+SUM ns <= dcap /\
  val_wf tv v /\ val_footprint tv v <= scap /\
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
      val_in_memory tv v a mem) /\
    encoder_resource ctx fn children a scap
      ((pid,p,32)::(cid,c,32)::protected) sp ==>
    ?Gm tnm sm. encoder_framed_child_result D ctx fn PG sb se children a scap
      ((pid,p,32)::(cid,c,32)::protected) (b+32+(32*N+SUM (TAKE i ns)))
      (cap i) len (EL i ns) (EL i costs) Gp tnp sp Gm tnm sm) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s (SUM (DROP j costs)) Gf tnf (OK sf) /\
    sf.vs_current_bb = exit_lbl /\ sf.vs_inst_idx = 0 /\
    encoder_dynamic_loop_inv ctx fn sites protected
      ip cursor src dst cv p c a b scap dcap tv v N ns N Gf tnf sf /\
    encoder_dynamic_effect sh sites b dcap G tn s Gf tnf sf
Proof
  Induct >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  >- (
    `j = N /\ j <= N /\ p < dimword(:256)` by decide_tac >>
    drule_all encoder_dynamic_header_counted_ptr >>
    disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
    `DROP j costs = [] /\ ~(j<N)` by
      (conj_tac >- (irule DROP_LENGTH_TOO_LONG >> decide_tac) >> decide_tac) >>
    qpat_x_assum `N = 0+j` kall_tac >>
    qexistsl_tac [`Gf`,`tnf`,`sf`] >> asm_simp_tac bool_ss [SUM] >> metis_tac[]) >>
  qpat_x_assum `!j G tn s. abi_encode_array_header _ _ _ = _ /\ _ ==> _` (mk_asm "ih") >>
  `j < N /\ j <= N /\ p < dimword(:256)` by decide_tac >>
  drule_at (Pat `encoder_dynamic_loop_inv ctx fn sites protected ip cursor src dst cv p c a b scap dcap tv v N ns j G tn s`)
    encoder_dynamic_header_counted_ptr >>
  disch_then (qspecl_then [`sh`,`sa`,`hdr`,`exit_lbl`,`body_lbl`,`PG`,`D`] mp_tac) >>
  (impl_tac >- asm_simp_tac bool_ss []) >>
  disch_then (qx_choose_then `Gh` (qx_choose_then `tnh` (qx_choose_then `shead` strip_assume_tac))) >>
  `EL j ns <= cap j /\ 32+(32*N+SUM (TAKE j ns))+cap j <= dcap /\
   32+j*msz+msz <= scap` by metis_tac[] >>
  `j+1 < dimword(:256) /\ 32*N+SUM (TAKE j ns)+EL j ns < dimword(:256)` by
    decide_tac >>
  `FLOOKUP shead.vs_allocas pid = SOME (p,32) /\
   FLOOKUP shead.vs_allocas cid = SOME (c,32)` by
    (gvs[encoder_dynamic_effect_def] >> metis_tac[]) >>
  `shead.vs_current_bb = sa.cs_current_bb /\
   shead.vs_inst_idx = LENGTH sa.cs_current_insts` by simp[] >>
  qpat_assum `j < N` (fn bound =>
    qpat_assum `!i Gp tnp sp. _`
      (qspec_then `j` (assume_tac o REWRITE_RULE [bound]))) >>
  drule_at (Pat `encoder_dynamic_loop_inv ctx fn sites protected ip cursor src dst cv p c a b scap dcap tv v N ns j Gh tnh shead`)
    (encoder_dynamic_body_backedge_counted_ptr |>
    Q.INST [`capj` |-> `cap j`, `k` |-> `32*N+SUM (TAKE j ns)`,
            `n` |-> `EL j ns`, `cost` |-> `EL j costs`]) >>
  disch_then (drule_all o REWRITE_RULE []) >>
  disch_then (qx_choose_then `Gb` (qx_choose_then `tnb` (qx_choose_then `sbody` strip_assume_tac))) >>
  asm "ih" (qspecl_then [`j+1`,`Gb`,`tnb`,`sbody`] mp_tac) >>
  (impl_tac >-
    (asm_simp_tac bool_ss [] >> conj_tac >- decide_tac >>
     gvs[encoder_dynamic_effect_def] >> metis_tac[])) >>
  disch_then (qx_choose_then `Gf` (qx_choose_then `tnf` (qx_choose_then `sf` strip_assume_tac))) >>
  `encoder_dynamic_effect sh sites b dcap Gh tnh shead Gb tnb sbody` by
    (fs[encoder_dynamic_effect_def] >> metis_tac[]) >>
  `encoder_dynamic_effect sh sites b dcap G tn s Gb tnb sbody` by
    (irule encoder_dynamic_effect_then >> metis_tac[]) >>
  `encoder_dynamic_effect sh sites b dcap G tn s Gf tnf sf` by
    (irule encoder_dynamic_effect_then >> metis_tac[]) >>
  `j < LENGTH costs` by decide_tac >>
  `SUM (DROP j costs) = EL j costs + SUM (DROP (j+1) costs)` by
    (qpat_assum `j < LENGTH costs` (mp_tac o MATCH_MP DROP_CONS_EL) >>
     disch_then (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [th]) >>
     simp[SUM, ADD1]) >>
  qexistsl_tac [`Gf`,`tnf`,`sf`] >> asm_simp_tac bool_ss [] >>
  irule gas_path_ptr_then >> goal_assum (drule_at Any) >> simp[] >>
  irule gas_path_ptr_then >> goal_assum (drule_at Any) >> simp[]
QED
