(* Fixed-source robustness for dynamic arrays with static ABI children. *)
Theory extRetAbiSourceArrayStaticCountedPtr
Ancestors
  extRetAbiArrayParentPtr abiEncoderSourceTransport abiEncoderInput
  valueEncodingProps valueTypingMemoryProps robustCopyTransportPtr
  bodyPtrDefs loweringPosts contractABI words list arithmetic

Theorem abi_encoder_source_dynamic_static_input:
  evaluate_type env (ArrayT t (Dynamic maxn)) =
    SOME (ArrayTV tv (Dynamic maxn)) /\
  value_has_type (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
  vyper_to_abi env (ArrayT t (Dynamic maxn)) (ArrayV (DynArrayV vs)) =
    SOME (contractABI$ListV avs) /\
  ct = vyper_to_abi_type env t /\ ~is_dynamic ct /\
  has_type (Array NONE ct) (contractABI$ListV avs) /\
  asz = abi_member_head_size ct /\ static_length ct = asz /\
  type_memory_size tv = asz /\ msz = type_memory_size tv /\
  ((ei = AbiPrimWord /\ asz = 32) \/ ei = AbiCopy asz) /\
  type_memory_size (ArrayTV tv (Dynamic maxn)) <= scap /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) sb mem') ==>
  !mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiDynArray ei asz msz F)
      (Array NONE ct) (contractABI$ListV avs) sb scap mem'
Proof
  rpt strip_tac >>
  qpat_x_assum `!mem'. _ ==> val_in_memory _ _ _ _` drule >> strip_tac >>
  drule_all abi_encoder_dynamic_source >> strip_tac >> gvs[] >>
  simp[abi_encoder_array_input_iff] >>
  rpt strip_tac >>
  qpat_x_assum `!i. i < LENGTH vs ==> _` drule >> strip_tac >>
  drule_all val_in_memory_static_abi >> strip_tac >>
  qpat_x_assum `has_types _ _` mp_tac >>
  simp[has_types_LIST_REL, LIST_REL_EL_EQN] >> strip_tac >>
  qpat_x_assum `!n. n < LENGTH vs ==> _` drule >>
  simp[rich_listTheory.EL_REPLICATE, abi_encoder_input_word_iff, abi_encoder_input_copy_iff] >>
  qpat_x_assum `mem_bytes_at _ (type_memory_size tv) _ = _` mp_tac >> simp[]
QED

Theorem compile_abi_encode_source_dyn_static_loop_parent_counted_ptr:
  compile_abi_encode_dyn_static_loop (Var dst) (Var src) ei asz msz (Var cv) sa = (out,se) /\
  fn_has_code sa se fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\ not_fresh_at sa cv /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s scap /\
  lookup_var dst s = SOME b /\ ptr_covers G tn dst s dcap /\
  lookup_var cv s = SOME (n2w (LENGTH avs)) /\
  op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
  evaluate_type env (ArrayT t (Dynamic maxn)) = SOME (ArrayTV tv (Dynamic maxn)) /\
  value_has_type (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
  vyper_to_abi env (ArrayT t (Dynamic maxn)) (ArrayV (DynArrayV vs)) = SOME (contractABI$ListV avs) /\
  ct = vyper_to_abi_type env t /\ ~is_dynamic ct /\
  has_type (Array NONE ct) (contractABI$ListV avs) /\
  asz = abi_member_head_size ct /\ static_length ct = asz /\
  type_memory_size tv = asz /\ msz = type_memory_size tv /\
  type_memory_size (ArrayTV tv (Dynamic maxn)) <= scap /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) (w2n a) mem') /\
  mem_bytes_at (w2n b) 32 s.vs_memory = header /\ LENGTH header = 32 /\
  (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tn.t_mem) /\
  ((ei = AbiPrimWord /\ asz = 32) \/ ei = AbiCopy asz) /\
  LENGTH (enc (Array NONE ct) (contractABI$ListV avs)) <= dcap /\
  32+LENGTH avs*asz <= dcap /\ LENGTH avs < dimword(:256) /\
  w2n a+scap < dimword(:256) /\ w2n b+dcap < dimword(:256) /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas sa.cs_next_id = SOME (addr,32) /\
  addr+32 < dimword(:256) /\
  (w2n a+scap <= w2n b \/ w2n b+dcap <= w2n a) /\
  (w2n a+scap <= addr \/ addr+32 <= w2n a) /\
  (w2n b+dcap <= addr \/ addr+32 <= w2n b) /\
  not_fresh_at sa parent_dyn_ptr /\ lookup_var parent_dyn_ptr s = SOME q /\
  ptr_covers G tn parent_dyn_ptr s 32 /\
  (!i. w2n q <= i /\ i < w2n q+32 ==> i NOTIN tn.t_mem) /\
  DISJOINT {i | w2n q <= i /\ i < w2n q+32}
    ({i | w2n b <= i /\ i < w2n b+dcap} UNION {i | addr <= i /\ i < addr+32}) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = se.cs_current_bb /\ sf.vs_inst_idx = LENGTH se.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (n2w (32+LENGTH avs*asz)) /\ op_taint tnf out = {} /\
    mem_bytes_at (w2n b) (32+LENGTH avs*asz) sf.vs_memory = header ++ FLAT (MAP (enc ct) avs) /\
    (!i. w2n b <= i /\ i < w2n b+32+LENGTH avs*asz ==> i NOTIN tnf.t_mem) /\
    lookup_var src sf = SOME a /\ ptr_covers Gf tnf src sf scap /\
    lookup_var dst sf = SOME b /\ ptr_covers Gf tnf dst sf dcap /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      abi_encoder_input (AbiDynArray ei asz msz F) (Array NONE ct) (contractABI$ListV avs) (w2n a) scap mem') /\
    sf.vs_allocas = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas /\
    sf.vs_alloca_next = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_alloca_next /\
    sf.vs_fmp = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_fmp /\
    (!site region. FLOOKUP s.vs_allocas site = SOME region ==>
      FLOOKUP sf.vs_allocas site = SOME region) /\
    mem_agree_outside
      ({i | w2n b <= i /\ i < w2n b+dcap} UNION {i | addr <= i /\ i < addr+32})
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN ({i | w2n b <= i /\ i < w2n b+dcap} UNION
      {i | addr <= i /\ i < addr+32}) ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    lookup_var parent_dyn_ptr sf = SOME q /\ ptr_covers Gf tnf parent_dyn_ptr sf 32 /\
    mload (w2n q) sf = mload (w2n q) s /\
    (!i. w2n q <= i /\ i < w2n q+32 ==> i NOTIN tnf.t_mem) /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) (w2n a) mem')
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiDynArray ei asz msz F) (Array NONE ct) (contractABI$ListV avs)
      (w2n a) scap mem'` by
    (rpt strip_tac >> irule abi_encoder_source_dynamic_static_input >> metis_tac[]) >>
  drule_all compile_abi_encode_dyn_static_loop_parent_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`,`tnf`,`sf`] >> asm_rewrite_tac[] >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- (drule value_has_type_memory_wf >> simp[]) >>
  qexistsl_tac [`s.vs_memory`, `sf.vs_memory`, `tn.t_mem`, `tnf.t_mem`,
    `{i | w2n b <= i /\ i < w2n b+dcap} UNION {i | addr <= i /\ i < addr+32}`] >>
  simp[] >> conj_tac
  >- (qpat_x_assum `mem_agree_outside _ sf.vs_memory s.vs_memory` mp_tac >>
      simp[mem_agree_outside_def]) >>
  simp[val_footprint_def] >> rpt strip_tac >> decide_tac
QED
