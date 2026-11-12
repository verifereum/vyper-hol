Theory extRetEvaluatedStaticLoopResourcePtr
Ancestors
  extRetEvaluatedStaticLoopPtr extRetLoopInitAmbientPtr
  extRetRecursiveResourcePtr extRetScratchResourcePtr
  abiEncoderWindowArray abiDecoderIndexInit abiBuiltinAllocation
  allocaSiteResource allocationPtr fragExec fragGasPathPtr compileEnv
  emitHelper ptrDiscipline bodyPtrDefs venomState venomExecSemantics
  venomMemDefs venomInst exprLoweringProps words finite_map pred_set arithmetic list
  robustCopyTransportPtr valueTypingMemoryProps loweringPosts valueEncoding
  valueEncodingProofs vyperTyping extRetLoopHeaderAmbientPtr extRetLoopTailAmbientPtr
  abiEncoderArrayCode abiEncoderArrayContext abiEncoderArrayPhaseAppend
  abiEncoderArrayPhases abiEncoderArrayHeader abiDecoderLoopEmit
  extRetAbiArrayStaticLoopPtr emitHelperProps fragGasSeqPtr
  bodyPtrPopMemoryHeader valueEncodingProps abiEncoderArrayLoopLayout

(* Project the allocator's checked resource transition to the allocation-only
   state used by the compiler-phase interfaces. No runtime address is assumed. *)
Theorem encoder_index_allocate_resource:
  encoder_resource ctx fn sites q len protected s /\ id IN sites /\
  MEM (mk_inst id ALLOCA [Lit 32w] [ip]) (fn_insts fn) ==>
  ?addr.
    encoder_resource ctx fn sites q len protected
      (abi_builtin_allocate_state id 32 s) /\
    FLOOKUP (abi_builtin_allocate_state id 32 s).vs_allocas id = SOME (addr,32) /\
    addr+32 < dimword(:256) /\
    s.vs_alloca_next <= (abi_builtin_allocate_state id 32 s).vs_alloca_next /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP (abi_builtin_allocate_state id 32 s).vs_allocas aid = SOME (p,sz)) /\
    (len <> 0 ==> regions_disjoint (q,len) (addr,32)) /\
    (!pid b n. MEM (pid,b,n) protected /\ n <> 0 ==>
      regions_disjoint (b,n) (addr,32))
Proof
  strip_tac >>
  `scratch_resource ctx fn sites q len s` by fs[encoder_resource_def] >>
  mp_tac (Q.INST [`inst` |-> `mk_inst id ALLOCA [Lit 32w] [ip]`, `out` |-> `ip`]
    scratch_resource_alloca) >> simp[mk_inst_def] >> strip_tac >>
  `t.vs_allocas = (abi_builtin_allocate_state id 32 s).vs_allocas /\
   t.vs_alloca_next = (abi_builtin_allocate_state id 32 s).vs_alloca_next` by
    (Cases_on `FLOOKUP s.vs_allocas id` >>
     gvs[exec_alloca_def, mk_inst_def, abi_builtin_allocate_state_def,
         update_var_def, AllCaseEqs(), dimword_def]) >>
  `scratch_resource ctx fn sites q len (abi_builtin_allocate_state id 32 s)` by
    (irule scratch_resource_fields >> qexists_tac `t` >> simp[]) >>
  `encoder_resource ctx fn sites q len protected
     (abi_builtin_allocate_state id 32 s)` by
    (irule encoder_resource_registered_intro >> simp[] >>
     fs[encoder_resource_def] >> metis_tac[]) >>
  `b+32 < dimword(:256)` by
    (`alloca_inv t /\ alloca_room ctx fn t` by
       (qpat_assum `scratch_resource _ _ _ _ _ t` mp_tac >>
        simp_tac std_ss [scratch_resource_def]) >>
     drule_all alloca_site_registered_below >>
     drule alloca_room_next_lt >> decide_tac) >>
  `!pid a n. MEM (pid,a,n) protected /\ n <> 0 ==>
     regions_disjoint (a,n) (b,32)` by
    (rpt gen_tac >> strip_tac >>
     drule_all encoder_resource_protected >> strip_tac >>
     `alloca_inv (abi_builtin_allocate_state id 32 s)` by
       (qpat_assum `scratch_resource _ _ _ a n _` mp_tac >>
        simp_tac std_ss [scratch_resource_def]) >>
     irule alloca_site_registered_disjoint >>
     qexistsl_tac [`pid`,`id`,`abi_builtin_allocate_state id 32 s`] >>
     simp[] >> metis_tac[]) >>
  qexists_tac `b` >> simp[] >> metis_tac[]
QED

Theorem encoder_index_init_resource_ambient_counted_ptr:
  abi_decode_index_init sa = (Var ip,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ encoder_resource ctx fn sites q len protected s /\
  sa.cs_next_id IN sites ==>
  ?addr Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w addr) /\ ptr_covers Gf tnf ip sf 32 /\
    sf.vs_allocas = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas /\
    sf.vs_alloca_next = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_alloca_next /\
    sf.vs_fmp = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_fmp /\
    encoder_resource ctx fn sites q len protected sf /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (addr,32) /\
    addr+32 < dimword(:256) /\ mload addr sf = 0w /\
    (!i. addr <= i /\ i < addr+32 ==> i NOTIN tnf.t_mem) /\
    s.vs_alloca_next <= sf.vs_alloca_next /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP sf.vs_allocas aid = SOME (p,sz)) /\
    (len <> 0 ==> regions_disjoint (q,len) (addr,32)) /\
    (!pid b n. MEM (pid,b,n) protected /\ n <> 0 ==>
      regions_disjoint (b,n) (addr,32)) /\
    mem_agree_outside {i | addr <= i /\ i < addr+32} sf.vs_memory s.vs_memory /\
    (!i. i < addr \/ addr+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    sf.vs_memory = (mstore addr 0w s).vs_memory /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_labels = s.vs_labels
Proof
  strip_tac >>
  drule_all window_array_index_alloca_member >> strip_tac >>
  drule_all encoder_index_allocate_resource >> strip_tac >>
  drule_all abi_decode_index_init_ambient_counted_ptr >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `encoder_resource ctx fn sites q len protected sf` by
    (irule encoder_resource_fields >>
     qexists_tac `abi_builtin_allocate_state sa.cs_next_id 32 s` >> simp[]) >>
  qexistsl_tac [`addr`,`Gf`,`tnf`,`sf`] >> simp[] >> metis_tac[]
QED

Theorem encoder_evaluated_static_index_init:
  abi_decode_index_init sa = (Var ip,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  encoder_resource ctx fn sites (w2n a) scap protected s /\
  sa.cs_next_id IN sites /\ MEM (did,w2n b,dcap) protected /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\ not_fresh_at sa cv /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  lookup_var cv s = SOME (n2w (LENGTH vs)) /\
  ptr_covers G tn src s scap /\ ptr_covers G tn dst s dcap /\
  op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
  type_memory_size (ArrayTV tv (Dynamic maxn)) <= scap /\
  value_has_type (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
  32 <= scap /\ 32 <= dcap /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) (w2n a) mem') /\
  (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tn.t_mem) ==>
  ?addr Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    encoder_static_loop_inv ctx fn sites (w2n a) scap protected
      ip src dst cv (n2w addr) a b scap dcap tv maxn vs k 0 Gf tnf sf /\
    sf.vs_allocas = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas /\
    sf.vs_alloca_next = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_alloca_next /\
    sf.vs_fmp = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_fmp /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (addr,32) /\
    addr+32 < dimword(:256) /\
    (w2n a+scap <= addr \/ addr+32 <= w2n a) /\
    (w2n b+dcap <= addr \/ addr+32 <= w2n b) /\
    mem_agree_outside {i | addr <= i /\ i < addr+32} sf.vs_memory s.vs_memory /\
    (!i. i < addr \/ addr+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all encoder_index_init_resource_ambient_counted_ptr >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `w2n a+scap <= addr \/ addr+32 <= w2n a` by
    (gvs[regions_disjoint_def] >> decide_tac) >>
  `w2n b+dcap <= addr \/ addr+32 <= w2n b` by
    (qpat_x_assum `!pid b n. MEM _ protected /\ _ ==> _` drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `addr < dimword(:256)` by decide_tac >>
  `w2n (n2w addr : bytes32) = addr` by simp[w2n_n2w] >>
  `lookup_var src sf = SOME a /\ lookup_var dst sf = SOME b /\
   lookup_var cv sf = SOME (n2w (LENGTH vs)) /\
   ptr_covers Gf tnf src sf scap /\ ptr_covers Gf tnf dst sf dcap /\
   op_taint tnf (Var cv) = {} /\ op_prov Gf (Var cv) = NONE` by
    (gvs[ptr_covers_def, op_prov_def] >> metis_tac[]) >>
  `!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tnf.t_mem` by
    (rpt strip_tac >> `i < addr \/ addr+32 <= i` by decide_tac >> metis_tac[]) >>
  `!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
     val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) (w2n a) mem'` by
    (rpt gen_tac >> strip_tac >>
     irule robust_val_in_memory_exterior_frame >>
     conj_tac >- metis_tac[value_has_type_memory_wf] >>
     qexistsl_tac [`s.vs_memory`,`sf.vs_memory`,`tn.t_mem`,`tnf.t_mem`,
       `{i | addr <= i /\ i < addr+32}`] >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     conj_tac >-
       (simp[NoAsms] >> rpt strip_tac >>
        `i < addr \/ addr+32 <= i` by decide_tac >> metis_tac[]) >>
     conj_tac >-
       (qpat_x_assum `mem_agree_outside _ sf.vs_memory s.vs_memory` mp_tac >>
        rewrite_tac[mem_agree_outside_def]) >>
     conj_tac >- (simp[NoAsms, val_footprint_def] >> rpt strip_tac >> decide_tac) >>
     simp[]) >>
  qexistsl_tac [`addr`,`Gf`,`tnf`,`sf`] >>
  asm_simp_tac bool_ss [encoder_static_loop_inv_def] >>
  simp[] >> metis_tac[]
QED

Theorem compile_evaluated_dyn_static_loop_resource_counted_ptr:
  compile_abi_encode_dyn_static_loop (Var dst) (Var src) ei k k (Var cv) sa = (out,se) /\
  fn_has_code sa se fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  encoder_resource ctx fn sites (w2n a) scap protected s /\
  sa.cs_next_id IN sites /\ MEM (did,w2n b,dcap) protected /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\ not_fresh_at sa cv /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  lookup_var cv s = SOME (n2w (LENGTH vs)) /\
  ptr_covers G tn src s scap /\ ptr_covers G tn dst s dcap /\
  op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
  evaluate_type env ty = SOME tv /\ ~is_dynamic (vyper_to_abi_type env ty) /\
  k = type_memory_size tv /\ ((ei = AbiPrimWord /\ k = 32) \/ ei = AbiCopy k) /\
  type_memory_size (ArrayTV tv (Dynamic maxn)) <= scap /\
  value_has_type (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
  32 <= scap /\ LENGTH vs < dimword(:256) /\ 32+LENGTH vs*k <= dcap /\
  w2n a+scap < dimword(:256) /\ w2n b+dcap < dimword(:256) /\
  (w2n a+scap <= w2n b \/ w2n b+dcap <= w2n a) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) (w2n a) mem') /\
  (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tn.t_mem) ==>
  ?addr ip Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = se.cs_current_bb /\
    sf.vs_inst_idx = LENGTH se.cs_current_insts /\
    eval_operand out sf = SOME (n2w (32+LENGTH vs*k)) /\ op_taint tnf out = {} /\
    encoder_static_loop_inv ctx fn sites (w2n a) scap protected
      ip src dst cv (n2w addr) a b scap dcap tv maxn vs k (LENGTH vs) Gf tnf sf /\
    sf.vs_allocas = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas /\
    sf.vs_alloca_next = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_alloca_next /\
    sf.vs_fmp = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_fmp /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (addr,32) /\ addr+32 < dimword(:256) /\
    mem_agree_outside
      ({i | w2n b <= i /\ i < w2n b+dcap} UNION {i | addr <= i /\ i < addr+32})
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN ({i | w2n b <= i /\ i < w2n b+dcap} UNION
      {i | addr <= i /\ i < addr+32}) ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule abi_encode_array_static_loop_trace >> strip_tac >>
  PairCases_on `labels` >>
  `cs_extends sa owner_st /\ cs_extends owner_st body_st /\
   cs_extends body_st body_end /\ cs_extends body_end exit_st /\ cs_extends exit_st se` by
    metis_tac[abi_encoder_appends_result, abi_encode_array_phase_append] >>
  `cs_extends owner_st exit_st /\ cs_extends owner_st se /\ cs_extends body_st se` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sa owner_st fn /\ fn_has_code owner_st exit_st fn /\
   fn_has_code owner_st body_st fn /\ fn_has_code exit_st se fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  rename1 `abi_decode_index_init sa = (index_op,owner_st)` >>
  drule abi_decode_index_init_shape >> strip_tac >>
  qpat_x_assum `index_op = Var _` SUBST_ALL_TAC >>
  qabbrev_tac `ip = STRING #"%" (toString sa.cs_next_var)` >>
  `32 <= dcap` by decide_tac >>
  drule_all encoder_evaluated_static_index_init >>
  disch_then (qspecl_then [`k`,`PG`,`D`]
    (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  `~sf.vs_halted` by
    (qpat_x_assum `encoder_static_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[encoder_static_loop_inv_def]) >>
  `addr < dimword(:256)` by decide_tac >>
  `w2n (n2w addr : bytes32) = addr` by simp[w2n_n2w] >>
  `not_fresh_at owner_st ip /\
   (!x. not_fresh_at sa x ==> not_fresh_at owner_st x)` by
    (simp[not_fresh_at_def, Abbr `ip`] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  drule_all abi_array_header_entry_ambient_counted_ptr >>
  disch_then (qspecl_then [`tnf`,`PG`,`Gf`,`D`] assume_tac) >>
  `encoder_static_loop_inv ctx fn sites (w2n a) scap protected
    ip src dst cv (n2w addr) a b scap dcap tv maxn vs k 0
    Gf tnf (jump_to labels0 sf)` by
    (qpat_x_assum `encoder_static_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sf` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac std_ss [encoder_static_loop_inv_def] >> strip_tac >>
     `encoder_resource ctx fn sites (w2n a) scap protected (jump_to labels0 sf)` by
       (irule encoder_resource_fields >> qexists_tac `sf` >> simp[jump_to_def]) >>
     simp[jump_to_def, ptr_covers_def, lookup_var_def, mload_def] >>
     gvs[jump_to_def, ptr_covers_def, lookup_var_def, mload_def, encoder_resource_fields]) >>
  `not_fresh_at owner_st src /\ not_fresh_at owner_st dst /\ not_fresh_at owner_st cv` by
    metis_tac[] >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [] >> disch_tac >>
  Q.SUBGOAL_THEN
    `(jump_to labels0 sf).vs_current_bb = labels0 /\
    (jump_to labels0 sf).vs_inst_idx = 0 /\
    w2n (n2w addr : bytes32)+32 < dimword(:256) /\
    (w2n a+scap <= w2n (n2w addr : bytes32) \/ w2n (n2w addr : bytes32)+32 <= w2n a) /\
    (w2n (n2w addr : bytes32)+32 <= w2n b \/ w2n b+dcap <= w2n (n2w addr : bytes32))`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)
    >- (simp[jump_to_def] >> metis_tac[]) >>
  (let
     val th = encoder_evaluated_static_loop_counted_ptr
     val vs = List.find (fn v => fst (dest_var v) = "vs") (free_vars (concl th))
              |> valOf
     val th0 = SPEC (listSyntax.mk_length vs) th |> SPEC ``0:num``
   in drule_all (GEN_ALL (SRULE [] th0)) end) >>
  disch_then (qspecl_then [`PG`,`D`]
    (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  qpat_assum `encoder_static_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sf'` mp_tac >>
  pure_rewrite_tac[encoder_static_loop_inv_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `mload (w2n a) sf' = n2w (LENGTH vs)` by
    (`val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs))
       (w2n a) sf'.vs_memory` by
       (qpat_assum `!mem'. mem_agree_outside tnf'.t_mem sf'.vs_memory mem' ==> _`
          (qspec_then `sf'.vs_memory` mp_tac) >> simp[mem_agree_outside_def]) >>
     pop_assum mp_tac >>
     simp[val_in_memory_def, mload_def, mem_word_at_def]) >>
  drule pop_robust_dynarray_header_clean >> disch_tac >>
  `ptr_covers Gf' tnf' src sf' 32` by
    (qpat_assum `ptr_covers Gf' tnf' src sf' scap` mp_tac >>
     simp_tac bool_ss [ptr_covers_def] >> rpt strip_tac >>
     simp[ptr_covers_def] >> qexistsl_tac [`w`,`b'`,`sz'`] >> simp[] >> decide_tac) >>
  `exit_st.cs_current_bb = labels2 /\ exit_st.cs_current_insts = []` by
    (qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decode_loop_suffix_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >> rpt (pairarg_tac >> simp[]) >> strip_tac >>
     gvs[new_block_def, comp_bind_def, comp_return_def]) >>
  `sf'.vs_current_bb = exit_st.cs_current_bb /\
   sf'.vs_inst_idx = LENGTH exit_st.cs_current_insts` by simp[] >>
  drule_all abi_array_static_exit_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`]
    (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  drule_all abi_array_static_loop_phase_code >> strip_tac >>
  `body_end.cs_next_var <= exit_st.cs_next_var` by
    (qpat_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decode_loop_suffix_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >> rpt (pairarg_tac >> simp[]) >> strip_tac >>
     gvs[new_block_def, emit_op_def, emit_void_def, emit_inst_def,
         fresh_var_def, fresh_id_def, emit_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  `!x. not_fresh_at owner_st x ==> not_fresh_at exit_st x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `encoder_static_loop_inv ctx fn sites (w2n a) scap protected
    ip src dst cv (n2w addr) a b scap dcap tv maxn vs k (LENGTH vs)
    Gf'' tnf'' sf''` by
    (qpat_assum `k = type_memory_size tv` mp_tac >>
     qpat_assum `encoder_static_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sf'` mp_tac >>
     qpat_assum `!x. not_fresh_at exit_st x ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at owner_st x ==> not_fresh_at exit_st x` mp_tac >>
     qpat_assum `not_fresh_at owner_st ip` mp_tac >>
     qpat_assum `not_fresh_at owner_st src` mp_tac >>
     qpat_assum `not_fresh_at owner_st dst` mp_tac >>
     qpat_assum `not_fresh_at owner_st cv` mp_tac >>
     qpat_assum `sf''.vs_memory = sf'.vs_memory` mp_tac >>
     qpat_assum `tnf''.t_mem = tnf'.t_mem` mp_tac >>
     qpat_assum `sf''.vs_allocas = sf'.vs_allocas` mp_tac >>
     qpat_assum `sf''.vs_alloca_next = sf'.vs_alloca_next` mp_tac >>
     qpat_assum `sf''.vs_fmp = sf'.vs_fmp` mp_tac >>
     qpat_assum `~sf''.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `encoder_resource ctx fn sites (w2n a) scap protected sf''` by
       (irule encoder_resource_fields >> qexists_tac `sf'` >>
        fs[encoder_static_loop_inv_def]) >>
     gvs[encoder_static_loop_inv_def, mload_def, ptr_covers_def, op_prov_def] >>
     metis_tac[]) >>
  qexistsl_tac [`addr`,`ip`,`Gf''`,`tnf''`,`sf''`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`,`m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`,`sf`,`tnf`] >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`,`m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`,`jump_to labels0 sf`,`tnf`] >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`,`m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`,`sf'`,`tnf'`] >> simp[]) >>
  simp[jump_to_def] >>
  conj_tac >-
    (qpat_assum `encoder_static_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sf''` mp_tac >>
     qpat_assum `w2n (n2w addr : bytes32) = addr` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[encoder_static_loop_inv_def]) >>
  conj_tac >-
    (qpat_assum `FLOOKUP sf.vs_allocas _ = _` mp_tac >>
     qpat_assum `sf.vs_allocas = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  conj_tac >-
    (qpat_assum `mem_agree_outside _ sf'.vs_memory _` mp_tac >>
     qpat_assum `mem_agree_outside _ sf.vs_memory _` mp_tac >>
     qpat_assum `w2n (n2w addr : bytes32) = addr` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[jump_to_def, mem_agree_outside_def, ADD_COMM] >> metis_tac[]) >>
  rpt strip_tac >>
  `i < addr \/ addr+32 <= i` by decide_tac >>
  qpat_assum `!i. _ ==> (i IN tnf'.t_mem <=> _)` (qspec_then `i` mp_tac) >>
  qpat_assum `!i. _ ==> (i IN tnf.t_mem <=> _)` (qspec_then `i` mp_tac) >>
  simp[] >> metis_tac[]
QED
