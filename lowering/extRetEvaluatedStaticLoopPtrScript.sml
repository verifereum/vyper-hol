Theory extRetEvaluatedStaticLoopPtr
Ancestors
  extRetEvaluatedStaticBodyPtr extRetLoopHeaderAmbientPtr extRetLoopTailAmbientPtr
  extRetAbiArrayStaticLoopPtr extRetAbiArrayHeaderPtr extRetRecursiveResourcePtr
  abiEncoderArrayHeader abiEncoderArrayBodyCode abiDecoderLoopEmit
  fragExec fragGasPathPtr compileEnv emitHelperProps ptrDiscipline bodyPtrDefs
  venomState venomExecSemantics words finite_map list rich_list arithmetic pred_set
  valueEncoding valueEncodingProofs vyperTypeABI vyperTyping
  robustCopyTransportPtr valueTypingMemoryProps loweringPosts

Theorem encoder_static_loop_header_ambient_counted_ptr:
  abi_encode_array_header (Var ip) (Var cv) sh = ((hdr,body_lbl,exit_lbl),sb) /\
  fn_has_code sh sb fn /\ not_fresh_at sh cv /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ptr_covers G tn ip s 32 /\ lookup_var ip s = SOME p /\
  ~ctx_has_dalloca ctx /\
  (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tn.t_mem) /\
  op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
  lookup_var cv s = SOME (n2w n) /\
  mload (w2n p) s = n2w j /\ j <= n /\ n < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = (if j<n then body_lbl else exit_lbl) /\
    sf.vs_inst_idx = 0 /\ ~sf.vs_halted /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_alloca_next = s.vs_alloca_next /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sh v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >>
  qabbrev_tac `iv = STRING #"%" (toString sh.cs_next_var)` >>
  qabbrev_tac `cmp = STRING #"%" (toString (sh.cs_next_var+1))` >>
  qabbrev_tac `done = STRING #"%" (toString (sh.cs_next_var+2))` >>
  `!v. not_fresh_at sh v ==> v <> iv /\ v <> cmp /\ v <> done` by
    (gvs[not_fresh_at_def, Abbr `iv`, Abbr `cmp`, Abbr `done`] >>
     metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
  drule_all abi_encode_array_header_code_ptr >> strip_tac >>
  `eval_operand (Var cv) s = SOME (n2w n) /\ cv <> iv` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  `bb.bb_instructions = abi_encode_array_header_insts (sh.cs_next_id+1)
    (Var ip) (Var cv) iv cmp done body_lbl exit_lbl` by
    simp[Abbr `iv`, Abbr `cmp`, Abbr `done`] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all (abi_encode_array_header_ambient_counted_ptr |>
    Q.INST [`count_op` |-> `Var cv`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`,`tnf`,
    `jump_to (if j<n then body_lbl else exit_lbl)
      (abi_encode_array_header_state iv cmp done j n s)`] >>
  simp[jump_to_def, abi_encode_array_header_state_def, update_var_def] >>
  rpt strip_tac >>
  `v <> iv /\ v <> cmp /\ v <> done` by metis_tac[] >>
  simp[lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Definition encoder_static_loop_inv_def:
  encoder_static_loop_inv ctx fn sites q len protected
      ip src dst cv p a b scap dcap tv maxn vs k j G tn s <=>
    ~s.vs_halted /\
    lookup_var ip s = SOME p /\ lookup_var src s = SOME a /\
    lookup_var dst s = SOME b /\ lookup_var cv s = SOME (n2w (LENGTH vs)) /\
    ptr_covers G tn ip s 32 /\ ptr_covers G tn src s scap /\ ptr_covers G tn dst s dcap /\
    mload (w2n p) s = n2w j /\
    (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tn.t_mem) /\
    op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
    (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
      val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) (w2n a) mem') /\
    (!i. w2n b <= i /\ i < w2n b+32+j*k ==> i NOTIN tn.t_mem) /\
    encoder_resource ctx fn sites q len protected s
End

Theorem encoder_static_loop_inv_memory_frame[local]:
  encoder_static_loop_inv ctx fn sites q len protected
    ip src dst cv p a b scap dcap tv maxn vs k j G tn s /\
  not_fresh_at sh ip /\ not_fresh_at sh src /\
  not_fresh_at sh dst /\ not_fresh_at sh cv /\
  ~sf.vs_halted /\ sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
  sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
  sf.vs_fmp = s.vs_fmp /\
  (!v. not_fresh_at sh v ==>
    lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
    op_taint tnf (Var v) = op_taint tn (Var v)) ==>
  encoder_static_loop_inv ctx fn sites q len protected
    ip src dst cv p a b scap dcap tv maxn vs k j Gf tnf sf
Proof
  strip_tac >>
  `encoder_resource ctx fn sites q len protected sf` by
    (irule encoder_resource_fields >> metis_tac[encoder_static_loop_inv_def]) >>
  gvs[encoder_static_loop_inv_def, mload_def, ptr_covers_def, op_prov_def] >>
  metis_tac[]
QED

Theorem encoder_static_loop_clean_prefix[local]:
  (!i:num. b <= i /\ i < b+32+j*k ==> i NOTIN t) ==>
  (!i. b <= i /\ i < b+32+(j+1)*k ==>
    i NOTIN (t DIFF {i | b+32+j*k <= i /\ i < b+32+j*k+k}))
Proof
  simp[IN_DIFF] >> rpt strip_tac >>
  `i < b+32+j*k \/ (b+32+j*k <= i /\ i < b+32+j*k+k)` by
    (fs[ADD_CLAUSES, RIGHT_ADD_DISTRIB] >> decide_tac) >> simp[]
QED

Theorem encoder_static_loop_index_source_frame[local]:
  !(a:bytes32) (p:bytes32) tv maxn vs scap sf s tnf tn.
  value_has_type (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
  type_memory_size (ArrayTV tv (Dynamic maxn)) <= scap /\
  (w2n a+scap <= w2n p \/ w2n p+32 <= w2n a) /\
  mem_agree_outside {i | w2n p <= i /\ i < w2n p+32} sf.vs_memory s.vs_memory /\
  tnf.t_mem = tn.t_mem DIFF {i | w2n p <= i /\ i < w2n p+32} /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) (w2n a) mem') ==>
  (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) (w2n a) mem')
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  rpt gen_tac >> strip_tac >>
  irule robust_val_in_memory_exterior_frame >>
  conj_tac >- metis_tac[value_has_type_memory_wf] >>
  qexistsl_tac [`s.vs_memory`, `sf.vs_memory`, `tn.t_mem`, `tnf.t_mem`,
    `{i | w2n p <= i /\ i < w2n p+32}`] >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  conj_tac >- simp[] >>
  conj_tac >-
    (qpat_x_assum `mem_agree_outside _ sf.vs_memory s.vs_memory` mp_tac >>
     rewrite_tac[mem_agree_outside_def]) >>
  conj_tac >-
    (simp[NoAsms, val_footprint_def] >> rpt strip_tac >> decide_tac) >>
  simp[]
QED

Theorem encoder_loop_memory_exterior_compose[local]:
  A SUBSET U /\ B SUBSET U /\
  mem_agree_outside A m2 m1 /\ mem_agree_outside B m1 m0 ==>
  mem_agree_outside U m2 m0
Proof
  rewrite_tac[SUBSET_DEF, mem_agree_outside_def] >> metis_tac[]
QED

Theorem encoder_loop_taint_exterior_compose[local]:
  (A:num set) SUBSET U /\ B SUBSET U /\
  (!i. i NOTIN A ==> (i IN t2 <=> i IN t1)) /\
  (!i. i NOTIN B ==> (i IN t1 <=> i IN t0)) ==>
  (!i. i NOTIN U ==> (i IN t2 <=> i IN t0))
Proof
  rewrite_tac[SUBSET_DEF] >> metis_tac[]
QED

Theorem encoder_evaluated_static_loop_step:
  abi_encode_array_header (Var ip) (Var cv) sh = ((hdr,body_lbl,exit_lbl),sb) /\
  abi_encode_array_static_body (Var ip) (Var src) (Var dst) ei k k sb = (idx,st) /\
  abi_decode_loop_suffix (Var ip) idx hdr exit_lbl st = ((),se) /\
  fn_has_code sh se fn /\
  not_fresh_at sh ip /\ not_fresh_at sh src /\
  not_fresh_at sh dst /\ not_fresh_at sh cv /\ ~ctx_has_dalloca ctx /\
  encoder_static_loop_inv ctx fn sites q len protected
    ip src dst cv p a b scap dcap tv maxn vs k j G tn s /\
  s.vs_current_bb = body_lbl /\ s.vs_inst_idx = 0 /\
  evaluate_type env ty = SOME tv /\ ~is_dynamic (vyper_to_abi_type env ty) /\
  k = type_memory_size tv /\
  ((ei = AbiPrimWord /\ k = 32) \/ ei = AbiCopy k) /\
  type_memory_size (ArrayTV tv (Dynamic maxn)) <= scap /\
  value_has_type (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
  j < LENGTH vs /\ LENGTH vs < dimword(:256) /\ 32+LENGTH vs*k <= dcap /\
  w2n a+scap < dimword(:256) /\ w2n b+dcap < dimword(:256) /\
  w2n p+32 < dimword(:256) /\
  (w2n a+scap <= w2n b \/ w2n b+dcap <= w2n a) /\
  (w2n a+scap <= w2n p \/ w2n p+32 <= w2n a) /\
  (w2n p+32 <= w2n b \/ w2n b+dcap <= w2n p) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = hdr /\ sf.vs_inst_idx = 0 /\
    encoder_static_loop_inv ctx fn sites q len protected
      ip src dst cv p a b scap dcap tv maxn vs k (j+1) Gf tnf sf /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    mem_agree_outside
      ({i | w2n b <= i /\ i < w2n b+dcap} UNION
       {i | w2n p <= i /\ i < w2n p+32}) sf.vs_memory s.vs_memory /\
    (!i. i NOTIN ({i | w2n b <= i /\ i < w2n b+dcap} UNION
       {i | w2n p <= i /\ i < w2n p+32}) ==>
       (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    (!v. not_fresh_at sh v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all abi_array_static_loop_phase_code >> strip_tac >>
  `!v. not_fresh_at sh v ==> not_fresh_at sb v /\ not_fresh_at st v` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  qhdtm_assum `encoder_static_loop_inv` mp_tac >>
  pure_rewrite_tac[encoder_static_loop_inv_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
   not_fresh_at sb ip /\ not_fresh_at sb src /\ not_fresh_at sb dst` by
    (simp[] >> metis_tac[]) >>
  drule_all encoder_evaluated_static_body_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `!i. w2n b <= i /\ i < w2n b+32+(j+1)*k ==> i NOTIN tnf.t_mem` by
    (qpat_assum `tnf.t_mem = _` (fn th => pure_rewrite_tac[th]) >>
     simp[encoder_static_loop_clean_prefix]) >>
  `lookup_var ip sf = SOME p /\ lookup_var src sf = SOME a /\ lookup_var dst sf = SOME b /\
   not_fresh_at st ip /\ j+1 < dimword(:256)` by (simp[] >> metis_tac[LESS_EQ_LESS_TRANS, LESS_EQ_IFF_LESS_SUC]) >>
  drule_all abi_decode_loop_suffix_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `!mem'. mem_agree_outside tnf'.t_mem sf'.vs_memory mem' ==>
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) (w2n a) mem'` by
    (rpt gen_tac >> strip_tac >>
     irule encoder_static_loop_index_source_frame >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     qexistsl_tac [`p`,`sf`,`scap`,`sf'`,`tnf`,`tnf'`] >> simp[]) >>
  qexistsl_tac [`Gf'`,`tnf'`,`sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`,`sf`,`tnf`] >> simp[]) >>
  `encoder_resource ctx fn sites q len protected sf'` by
    (irule encoder_resource_fields >> qexists_tac `sf` >> simp[]) >>
  `lookup_var cv sf' = SOME (n2w (LENGTH vs)) /\
   op_taint tnf' (Var cv) = {} /\ op_prov Gf' (Var cv) = NONE` by
    (fs[op_prov_def] >> metis_tac[]) >>
  `ptr_covers Gf' tnf' src sf' scap` by
    (qpat_x_assum `ptr_covers Gf tnf src sf scap` mp_tac >>
     simp[ptr_covers_def] >> metis_tac[]) >>
  `ptr_covers Gf' tnf' dst sf' dcap` by
    (qpat_x_assum `ptr_covers Gf tnf dst sf dcap` mp_tac >>
     simp[ptr_covers_def] >> metis_tac[]) >>
  `!i. w2n b <= i /\ i < w2n b+32+(j+1)*k ==> i NOTIN tnf'.t_mem` by
    (qpat_assum `tnf'.t_mem = _` (fn th => pure_rewrite_tac[th]) >>
     simp_tac bool_ss [IN_DIFF] >> metis_tac[]) >>
  `32+j*k+k <= dcap` by
    (`j*k+k <= LENGTH vs*k` by
       (irule abiDecoderArraySliceTheory.abi_decoder_array_cell_capacity >> simp[]) >>
     qpat_x_assum `32+LENGTH vs*k <= dcap` mp_tac >>
     qpat_x_assum `j*k+k <= LENGTH vs*k` mp_tac >> decide_tac) >>
  `{i | w2n p <= i /\ i < w2n p+32} SUBSET
      ({i | w2n b <= i /\ i < w2n b+dcap} UNION
       {i | w2n p <= i /\ i < w2n p+32})` by simp[SUBSET_UNION] >>
  `{i | w2n b+32+j*k <= i /\ i < w2n b+32+j*k+k} SUBSET
      ({i | w2n b <= i /\ i < w2n b+dcap} UNION
       {i | w2n p <= i /\ i < w2n p+32})` by
    (simp[NoAsms, SUBSET_DEF] >> rpt strip_tac >>
     disj1_tac >>
     qpat_x_assum `32+j*k+k <= dcap` mp_tac >> decide_tac) >>
  `mem_agree_outside
      ({i | w2n b <= i /\ i < w2n b+dcap} UNION
       {i | w2n p <= i /\ i < w2n p+32}) sf'.vs_memory s.vs_memory` by
    (irule encoder_loop_memory_exterior_compose >>
     qexistsl_tac [`{i | w2n p <= i /\ i < w2n p+32}`,
       `{i | w2n b+32+j*k <= i /\ i < w2n b+32+j*k+k}`, `sf.vs_memory`] >>
     simp[]) >>
  `!i. i NOTIN ({i | w2n b <= i /\ i < w2n b+dcap} UNION
       {i | w2n p <= i /\ i < w2n p+32}) ==>
       (i IN tnf'.t_mem <=> i IN tn.t_mem)` by
    (ho_match_mp_tac (encoder_loop_taint_exterior_compose |> Q.INST
       [`A` |-> `{i | w2n (p:bytes32) <= i /\ i < w2n p+32}`,
        `B` |-> `{i | w2n (b:bytes32)+32+j*k <= i /\ i < w2n b+32+j*k+k}`,
        `t1` |-> `tnf.t_mem`]) >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     qpat_assum `tnf.t_mem = _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, IN_DIFF] >> metis_tac[]) >>
  asm_simp_tac bool_ss [encoder_static_loop_inv_def]
QED

Theorem encoder_evaluated_static_loop_counted_ptr:
  !r j G tn s.
  abi_encode_array_header (Var ip) (Var cv) sh = ((hdr,body_lbl,exit_lbl),sb) /\
  abi_encode_array_static_body (Var ip) (Var src) (Var dst) ei k k sb = (idx,st) /\
  abi_decode_loop_suffix (Var ip) idx hdr exit_lbl st = ((),se) /\
  fn_has_code sh se fn /\
  not_fresh_at sh ip /\ not_fresh_at sh src /\
  not_fresh_at sh dst /\ not_fresh_at sh cv /\ ~ctx_has_dalloca ctx /\
  encoder_static_loop_inv ctx fn sites q len protected
    ip src dst cv p a b scap dcap tv maxn vs k j G tn s /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ LENGTH vs = r+j /\
  evaluate_type env ty = SOME tv /\ ~is_dynamic (vyper_to_abi_type env ty) /\
  k = type_memory_size tv /\
  ((ei = AbiPrimWord /\ k = 32) \/ ei = AbiCopy k) /\
  type_memory_size (ArrayTV tv (Dynamic maxn)) <= scap /\
  value_has_type (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
  LENGTH vs < dimword(:256) /\ 32+LENGTH vs*k <= dcap /\
  w2n a+scap < dimword(:256) /\ w2n b+dcap < dimword(:256) /\
  w2n p+32 < dimword(:256) /\
  (w2n a+scap <= w2n b \/ w2n b+dcap <= w2n a) /\
  (w2n a+scap <= w2n p \/ w2n p+32 <= w2n a) /\
  (w2n p+32 <= w2n b \/ w2n b+dcap <= w2n p) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = exit_lbl /\ sf.vs_inst_idx = 0 /\
    encoder_static_loop_inv ctx fn sites q len protected
      ip src dst cv p a b scap dcap tv maxn vs k (LENGTH vs) Gf tnf sf /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    mem_agree_outside
      ({i | w2n b <= i /\ i < w2n b+dcap} UNION
       {i | w2n p <= i /\ i < w2n p+32}) sf.vs_memory s.vs_memory /\
    (!i. i NOTIN ({i | w2n b <= i /\ i < w2n b+dcap} UNION
       {i | w2n p <= i /\ i < w2n p+32}) ==>
       (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    (!v. not_fresh_at sh v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  Induct >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  >- (
    `j = LENGTH vs` by decide_tac >>
    drule_all abi_array_static_loop_phase_code >> strip_tac >>
    qhdtm_assum `encoder_static_loop_inv` mp_tac >>
    pure_rewrite_tac[encoder_static_loop_inv_def] >>
    disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
    `j <= LENGTH vs` by decide_tac >>
    drule_all encoder_static_loop_header_ambient_counted_ptr >>
    disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
    `encoder_static_loop_inv ctx fn sites q len protected
      ip src dst cv p a b scap dcap tv maxn vs k j Gf tnf sf` by
      (irule encoder_static_loop_inv_memory_frame >>
       conj_tac >- simp[] >> qexistsl_tac [`G`,`s`,`sh`,`tn`] >> simp[]) >>
    qexistsl_tac [`Gf`,`tnf`,`sf`] >>
    qpat_x_assum `LENGTH vs = 0+j` kall_tac >>
    asm_simp_tac bool_ss [mem_agree_outside_def] >>
    gvs[encoder_static_loop_inv_def]) >>
  drule_all abi_array_static_loop_phase_code >> strip_tac >>
  qhdtm_assum `encoder_static_loop_inv` mp_tac >>
  pure_rewrite_tac[encoder_static_loop_inv_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `j < LENGTH vs /\ j <= LENGTH vs` by decide_tac >>
  drule_all encoder_static_loop_header_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `encoder_static_loop_inv ctx fn sites q len protected
    ip src dst cv p a b scap dcap tv maxn vs k j Gf tnf sf` by
    (irule encoder_static_loop_inv_memory_frame >>
     conj_tac >- simp[] >> qexistsl_tac [`G`,`s`,`sh`,`tn`] >> simp[]) >>
  `sf.vs_current_bb = body_lbl` by simp[] >>
  drule_all encoder_evaluated_static_loop_step >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  rename1 `LENGTH vs = SUC remaining+j` >>
  `LENGTH vs = remaining+(j+1)` by decide_tac >>
  qpat_x_assum `!j G tn s. _` (qspecl_then [`j+1`,`Gf'`,`tnf'`,`sf'`] mp_tac) >>
  (impl_tac >- asm_simp_tac bool_ss []) >> strip_tac >>
  qexistsl_tac [`Gf''`,`tnf''`,`sf''`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`,`sf`,`tnf`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`,`sf'`,`tnf'`] >> simp[]) >>
  qpat_assum `encoder_static_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Gf'' tnf'' sf''` mp_tac >>
  pure_rewrite_tac[encoder_static_loop_inv_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  asm_simp_tac bool_ss [] >-
    (qpat_x_assum `mem_agree_outside _ sf''.vs_memory _` mp_tac >>
     qpat_x_assum `mem_agree_outside _ sf'.vs_memory _` mp_tac >>
     simp_tac bool_ss [mem_agree_outside_def] >> metis_tac[]) >>
  metis_tac[]
QED
