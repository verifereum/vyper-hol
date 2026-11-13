Theory abiEncTuplePtrStoreSequence
Ancestors
  abiEncTuplePtrRawSlot abiEncTuplePtrStoreFrame abiTupleEncodePrepare
  abiTupleEncodeInput abiTupleEncodeMemory abiTupleProps abiBuiltinEncodeWord abiTupleEncodeSlot
  bodyPtrDefs exprSimCopy localPtrsProps wordArgsPtr fragGasPathPtr
  abiDecoderContract abiDecoderReentry compileEnv emitHelperProps
  exprLowering loweringStateRelDefs venomState venomExecSemantics
  valueEncodingProps words arithmetic list finite_map

Theorem compile_store_abi_tuple_ptr:
  !xs ce bx off st final s b ats avs lo hi G tn.
  compile_store_abi_tuple ce (Var bx) off xs st = ((),final) /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  lookup_var bx s = SOME (n2w b) /\ ptr_covers G tn bx s N /\
  not_fresh_at st bx /\ off+abi_tuple_bytes ce xs <= N /\ b+N < dimword(:256) /\
  lo <= b+off /\ b+off+abi_tuple_bytes ce xs <= hi /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_tuple_encode_inputs sf ce xs ats avs st.cs_next_var lo hi (s with vs_memory := mem)) /\
  (!op ty. MEM (op,ty) xs ==>
    (is_word_type ty ==> op_taint tn op = {}) /\
    (~is_word_type ty /\ 0 < type_memory_bytes ce ty ==>
      ?x. op = Var x /\ ptr_covers G tn x s (type_memory_bytes ce ty))) /\
  local_ptrs_reserved cenv st /\ local_ptrs_rel func cenv es.scopes s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  ghost_inv rb cenv cx es G tn s /\
  fr.cs_next_id <= st.cs_next_id /\
  (!x. not_fresh_at fr x ==> not_fresh_at st x) /\
  (!name base sz. local_region cenv es.scopes s name base sz ==>
    regions_disjoint lo (hi-lo) base sz) /\
  (!aid base sz. FLOOKUP s.vs_allocas aid = SOME (base,sz) /\
    aid < fr.cs_next_id /\
    (!name p k. local_region cenv es.scopes s name p k ==>
      base+sz <= p \/ p+k <= base) ==>
    regions_disjoint lo (hi-lo) base sz) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK t) /\
    ghost_inv rb cenv cx es H tm t /\ ghost_kept cenv es fr G tn s H tm /\
    ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    lookup_var bx t = SOME (n2w b) /\ ptr_covers H tm bx t N /\
    (!x. not_fresh_at st x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x) /\
      (!k. ptr_covers G tn x s k ==> ptr_covers H tm x t k)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    abi_decode_frame (b+off) (abi_tuple_bytes ce xs) s t /\
    (!i. ~(b+off <= i /\ i < b+off+abi_tuple_bytes ce xs) ==>
      (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tm.t_mem t.vs_memory mem ==>
      abi_tuple_encode_memory sf ce xs ats avs (b+off) mem)
Proof
  Induct
  >- (simp[compile_store_abi_tuple_def, comp_return_def, abi_tuple_bytes_def] >>
      rpt strip_tac >> gvs[] >> qexistsl_tac [`G`,`tn`,`s`] >>
      simp[gas_path_ptr_rules, ghost_kept_def, abi_decode_frame_def] >>
      `abi_tuple_encode_inputs sf ce [] ats avs st.cs_next_var lo hi
        (s with vs_memory := s.vs_memory)` by
        (first_x_assum irule >> simp[mem_agree_outside_def]) >>
      gvs[abi_tuple_encode_inputs_def, abi_tuple_encode_memory_def]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac bool_ss [abi_tuple_encode_store_cons, comp_ignore_bind_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `compile_abi_tuple_slot ce (Var bx) off h0 h1 st = ((),middle)` >>
  `abi_tuple_encode_inputs sf ce ((h0,h1)::xs) ats avs st.cs_next_var lo hi
    (s with vs_memory := s.vs_memory)` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  gvs[abi_tuple_encode_inputs_def] >>
  drule abi_tuple_encode_slot_shape >> strip_tac >>
  drule abi_tuple_encode_store_shape >> strip_tac >>
  `cs_extends st middle /\ cs_extends middle final` by
    gvs[cs_extends_def] >>
  `fn_has_code st middle func /\ fn_has_code middle final func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `is_word_type h1 ==> type_memory_bytes ce h1 = 32` by
    metis_tac[abi_builtin_encode_word_info] >>
  `?v. eval_operand h0 s = SOME v` by
    (qpat_x_assum `abi_tuple_encode_input _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[abi_tuple_encode_input_def] >>
     Cases_on `is_word_type h1` >> simp[] >> strip_tac >>
     Cases_on `h0` >> gvs[eval_operand_def, lookup_var_def]) >>
  `!x. h0 = Var x ==> not_fresh_at st x` by
    (qpat_x_assum `abi_tuple_encode_input _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_tuple_encode_input_def] >> strip_tac >>
     rpt strip_tac >> gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `off+type_memory_bytes ce h1 <= N` by
    gvs[abi_tuple_bytes_def] >>
  `!name base sz. local_region cenv es.scopes s name base sz ==>
     regions_disjoint (b+off) (type_memory_bytes ce h1) base sz` by
    (rpt strip_tac >>
     qpat_x_assum `!name base sz. local_region _ _ _ _ _ _ ==> _` drule >>
     gvs[regions_disjoint_def, abi_tuple_bytes_def] >> decide_tac) >>
  `!aid base sz. FLOOKUP s.vs_allocas aid = SOME (base,sz) /\
     aid < fr.cs_next_id /\
     (!name p k. local_region cenv es.scopes s name p k ==> base+sz <= p \/ p+k <= base) ==>
     regions_disjoint (b+off) (type_memory_bytes ce h1) base sz` by
    (rpt strip_tac >>
     qpat_x_assum `!ce bx off st final s b ats avs lo hi G tn. _` kall_tac >>
     qpat_x_assum `!aid base sz. FLOOKUP s.vs_allocas aid = SOME (base,sz) /\ _ ==> _`
       (qspecl_then [`aid`,`base'`,`sz`] mp_tac) >> simp[ADD_COMM] >>
     (impl_tac >- (rpt strip_tac >>
       qpat_x_assum `!name p k. local_region _ _ _ _ _ _ ==> _` drule >>
       decide_tac)) >> strip_tac >>
     gvs[regions_disjoint_def, abi_tuple_bytes_def] >> decide_tac) >>
  mp_tac (compile_abi_tuple_slot_resources_ptr |> SPEC_ALL
    |> Q.INST [`op` |-> `h0`, `ty` |-> `h1`, `final` |-> `middle`,
      `n` |-> `type_memory_bytes ce h1`]) >>
  (impl_tac >- (
    qpat_x_assum `!ce bx off st final s b ats avs lo hi G tn. _` kall_tac >>
    gvs[ADD_COMM] >> metis_tac[])) >> strip_tac >>
  cheat
QED
