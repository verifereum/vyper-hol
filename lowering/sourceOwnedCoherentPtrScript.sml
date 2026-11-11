(* The owned source decoder contract, by rule induction on abi_decoder_coherent:
   the decoder for any coherent type, run on the actual state, decodes the
   source value into its destination with exact scratch ownership, frames and
   safety from the original state. *)
Theory sourceOwnedCoherentPtr
Ancestors
  sourceOwnedLeafPtr sourceOwnedComplexPtr sourceOwnedArrayConstructorPtr
  abiDecoderCoherence sourceArrayInputs sourceAggregateInputs decoderBlockGrowth
  placeMemoryTypedBase sourceEncodingLayout abiDecoderMemberInfos
  abiDecoderRecursiveArray decoderGhostFramePtr vyperABIRoundtrip
  valueEncodingProofs abiDecoderContract abiEncoderSourceTransport rich_list list

Theorem source_owned_coherent_decoder_ptr:
  !ce env sf ty tv.
  abi_decoder_coherent ce env sf ty tv ==>
  !v av child childsrc e srcpos root d outsz middle end_st r G tn oid base_addr
   owner_cap ctx fn site limit lower PG.
    compile_abi_decode_to_buf (Var child) childsrc CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
    value_has_type tv v /\
    vyper_to_abi env ty v = SOME av /\
    mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) av))
      r.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) av /\
    srcpos + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
    eval_operand childsrc r = SOME (n2w srcpos) /\
    lookup_var child r = SOME (n2w e) /\ lookup_var root r = SOME (n2w d) /\
    abi_decoder_operand_live middle.cs_next_var childsrc /\
    abi_decoder_operand_live middle.cs_next_var (Var child) /\
    abi_decoder_operand_live middle.cs_next_var (Var root) /\
    ptr_covers G tn child r (type_memory_size tv) /\
    ptr_covers G tn root r outsz /\ op_taint tn childsrc = {} /\ op_prov G childsrc = NONE /\
    alloca_inv r /\ alloca_frontier_inv ctx fn site r /\
    unit_alloca_budget ctx < dimword (:256) /\
    FLOOKUP r.vs_allocas oid = SOME (base_addr,owner_cap) /\
    (oid < middle.cs_next_id \/ end_st.cs_next_id <= oid) /\
    base_addr <= e /\ e + type_memory_size tv <= base_addr + owner_cap /\
    e + type_memory_size tv < dimword (:256) /\
    (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP r.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= r.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    fn_has_code middle end_st fn /\ fn_inst_ids_distinct fn /\
    (middle.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    end_st.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit r /\
    allocas_from lower r /\ lower <= r.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
    ~r.vs_halted /\ r.vs_current_bb = middle.cs_current_bb /\
    r.vs_inst_idx = LENGTH middle.cs_current_insts ==>
    ?t H u fp.
      abi_decode_sim ctx fn r t /\
      ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
      t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ fresh_vars_wrt limit t /\
      val_in_memory tv v e t.vs_memory /\
      (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
        val_in_memory tv v e mem) /\
      abi_decode_footprint_frame ((e,type_memory_size tv)::fp) r t /\
      abi_footprint_disjoint base_addr owner_cap fp /\
      alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lower t /\
      r.vs_alloca_next <= t.vs_alloca_next /\
      FLOOKUP t.vs_allocas oid = SOME (base_addr,owner_cap) /\
      (!id p k. FLOOKUP r.vs_allocas id = SOME (p,k) ==>
        FLOOKUP t.vs_allocas id = SOME (p,k)) /\
      (!id. id < middle.cs_next_id \/ end_st.cs_next_id <= id ==>
        FLOOKUP t.vs_allocas id = FLOOKUP r.vs_allocas id) /\
      (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (p,k) ==>
        k = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      (!p k. MEM (p,k) fp ==> ?id. middle.cs_next_id <= id /\
        id < end_st.cs_next_id /\ FLOOKUP t.vs_allocas id = SOME (p,k)) /\
      ptr_covers H u child t (type_memory_size tv) /\ ptr_covers H u root t outsz /\
      (!op. abi_decoder_operand_live middle.cs_next_var op ==>
        eval_operand op t = eval_operand op r) /\
      (!x. not_fresh_at middle x ==> FLOOKUP H x = FLOOKUP G x /\
        op_taint u (Var x) = op_taint tn (Var x)) /\
      u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
      u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
        !fuel. ptr_safe_run D lower fuel ctx fn PG G tn r) /\
      t.vs_accounts = r.vs_accounts /\ t.vs_transient = r.vs_transient /\
      t.vs_logs = r.vs_logs /\ t.vs_outcomes = r.vs_outcomes /\
      t.vs_requests = r.vs_requests /\
      t.vs_pending_deletions = r.vs_pending_deletions /\ t.vs_tx_ctx = r.vs_tx_ctx /\
      t.vs_block_ctx = r.vs_block_ctx /\ t.vs_fmp = r.vs_fmp /\
      t.vs_gas_readings = r.vs_gas_readings
Proof
  ho_match_mp_tac abi_decoder_coherent_strongind >> rpt conj_tac
  >- suspend "base"
  >- suspend "flag"
  >- suspend "array"
  >- suspend "tuple"
  >> suspend "struct"
QED

Resume source_owned_coherent_decoder_ptr[base]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf (BaseT bt) (BaseTV bt)` by
    simp[abi_decoder_coherent_base_iff] >>
  (Q.SUBGOAL_THEN
    `((?clamp. type_to_abi_dec_info sf ce (BaseT bt) = DecPrimWord clamp /\
       is_word_type (BaseT bt)) \/
      (?m. type_to_abi_dec_info sf ce (BaseT bt) = DecBytestring m))` assume_tac
    >- (qpat_x_assum `abi_decoder_scalar_valid bt` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `bt` >>
     simp[exprLoweringTheory.type_to_abi_dec_info_def,
       compileEnvTheory.is_word_type_def, abi_decoder_scalar_valid_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     simp[exprLoweringTheory.type_to_abi_dec_info_def,
       compileEnvTheory.is_word_type_def, abi_decoder_scalar_valid_def])) >>
  drule_all source_owned_primitive_decoder_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`t`,`H`,`u`,`[]`] >>
  asm_rewrite_tac[abiDecoderFrameTheory.abi_footprint_disjoint_def,
    listTheory.MEM]
QED

Resume source_owned_coherent_decoder_ptr[flag]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf (FlagT nsid) (FlagTV n)` by
    metis_tac[abi_decoder_coherent_flag_iff] >>
  (Q.SUBGOAL_THEN
    `((?clamp. type_to_abi_dec_info sf ce (FlagT nsid) = DecPrimWord clamp /\
       is_word_type (FlagT nsid)) \/
      (?m. type_to_abi_dec_info sf ce (FlagT nsid) = DecBytestring m))` assume_tac
    >- metis_tac[exprLoweringTheory.type_to_abi_dec_info_def,
      compileEnvTheory.is_word_type_def]) >>
  drule_all source_owned_primitive_decoder_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`t`,`H`,`u`,`[]`] >>
  asm_rewrite_tac[abiDecoderFrameTheory.abi_footprint_disjoint_def,
    listTheory.MEM]
QED

Resume source_owned_coherent_decoder_ptr[array]:
  rpt gen_tac >> strip_tac >>
  Cases_on `bound`
  >- suspend "fixed"
  >> suspend "dynamic"
QED

Resume source_owned_coherent_decoder_ptr[dynamic]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf (ArrayT ty (Dynamic n)) (ArrayTV tv (Dynamic n))` by
    simp[abi_decoder_coherent_array_iff] >>
  Cases_on `~is_abi_dynamic ce.ce_struct_fields ty /\
    ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- (pop_assum strip_assume_tac >>
      drule_all source_owned_bulk_array_ptr >>
      disch_then (qspec_then `PG` strip_assume_tac) >>
      qexistsl_tac [`t`,`H`,`u`,`[]`] >>
      asm_rewrite_tac[abiDecoderFrameTheory.abi_footprint_disjoint_def,
        listTheory.MEM]) >>
  suspend "nonbulk"
QED

Resume source_owned_coherent_decoder_ptr[nonbulk]:
  drule_all source_dynamic_array_values >> strip_tac >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  qpat_x_assum `av = _` SUBST_ALL_TAC >>
  `is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)` by
    (qpat_assum `~(~_ /\ ~_)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `abi_decoder_header ce env ty tv` by
    (qpat_assum `abi_decoder_coherent ce env sf ty tv`
       (mp_tac o MATCH_MP abi_decoder_coherent_header) >> simp_tac bool_ss []) >>
  `type_memory_size tv = type_memory_bytes ce ty` by
    (qpat_assum `abi_decoder_header ce env ty tv` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[abi_decoder_header_def]) >>
  `compile_abi_decode_to_buf (Var child) childsrc CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_size tv)
      (is_abi_dynamic ce.ce_struct_fields ty) n) middle = ((),end_st)` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
     simp_tac bool_ss [exprLoweringTheory.type_to_abi_dec_info_def] >>
     asm_rewrite_tac[]) >>
  `evaluate_type env (ArrayT ty (Dynamic n)) = SOME (ArrayTV tv (Dynamic n))` by
    (qpat_assum `abi_decoder_header ce env (ArrayT _ _) _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[abi_decoder_header_def]) >>
  `0 < type_slot_size tv /\ n < dimword (:256)` by
    (qpat_assum `evaluate_type env (ArrayT _ _) = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     disch_then (strip_assume_tac o MATCH_MP typed_memory_array_stride_bounds) >>
     gvs[vyperASTTheory.bound_length_def]) >>
  `!bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
    (qpat_x_assum `!v av child childsrc e srcpos root d outsz middle end_st r G tn oid base_addr owner_cap ctx fn site limit lower PG. _` kall_tac >>
     `middle.cs_blocks <> end_st.cs_blocks` by
       (irule nonbulk_decoder_blocks_grow >>
        goal_assum (drule_at Any) >>
        asm_rewrite_tac[abi_decode_source_opcode_def]) >>
     metis_tac[]) >>
  `LIST_REL (\aty av. ~is_dynamic aty ==>
    LENGTH (enc aty av) = abi_member_head_size aty)
    (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty)) avs` by
    (qpat_assum `abi_decoder_coherent ce env sf ty tv` mp_tac >>
     qpat_assum `EVERY (value_has_type tv) xs` mp_tac >>
     qpat_assum `vyper_to_abi_same env ty xs = SOME avs` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule abi_encoder_same_conversion >> strip_tac >>
     simp[LIST_REL_EL_EQN, EL_REPLICATE] >> qx_gen_tac `i` >> rpt strip_tac >>
     `abi_encoder_layout_valid (vyper_to_abi_type env ty) (EL i avs)` by
       (irule coherent_source_encoding_layout >>
        qexistsl_tac [`ce`,`sf`,`tv`,`EL i xs`] >>
        metis_tac[EVERY_EL]) >>
     metis_tac[abiEncoderOpenInputTheory.abi_encoder_layout_valid_def,
       abiDecodeRangesTheory.abi_member_head_size_def]) >>
  mp_tac (Q.INST [`root` |-> `child`, `d` |-> `e`,
    `outsz` |-> `type_memory_size (ArrayTV tv (Dynamic n))`,
    `src` |-> `childsrc`, `dyn` |-> `is_abi_dynamic ce.ce_struct_fields ty`,
    `maxn` |-> `n`, `cdsbase` |-> `srcpos`] source_owned_nonbulk_array_ptr) >>
  (impl_tac >-
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     first_x_assum irule >> asm_rewrite_tac[] >> metis_tac[])) >>
  disch_then (qspecl_then [`r`,`G`,`tn`,`middle`,`end_st`] mp_tac) >>
  (impl_tac >-
    (qpat_x_assum `!v av child childsrc e srcpos root d outsz middle end_st r G tn oid base_addr owner_cap ctx fn site limit lower PG. _` kall_tac >>
     asm_rewrite_tac[valueEncodingTheory.type_memory_size_def,
       vyperABITheory.vyper_to_abi_type_def] >>
     qpat_assum `mem_bytes_at srcpos _ _ = _` mp_tac >>
     qpat_assum `srcpos + LENGTH _ < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[vyperABITheory.vyper_to_abi_type_def])) >>
  strip_tac >>
  qpat_x_assum `!v av child childsrc e srcpos root d outsz middle end_st r G tn oid base_addr owner_cap ctx fn site limit lower PG. _` kall_tac >>
  qexistsl_tac [`t`,`H`,`u`,`fp`] >>
  asm_rewrite_tac[] >>
  irule ptr_covers_frame >> goal_assum (drule_at Any) >>
  asm_rewrite_tac[] >>
  `not_fresh_at middle root` by
    (qpat_assum `abi_decoder_operand_live middle.cs_next_var (Var root)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def,
       compileEnvTheory.not_fresh_at_def]) >>
  metis_tac[venomStateTheory.eval_operand_def]
QED

Resume source_owned_coherent_decoder_ptr[fixed]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `evaluate_type env ty = SOME tv` by
    (qpat_assum `abi_decoder_coherent ce env sf ty tv`
       (mp_tac o MATCH_MP abi_decoder_coherent_header) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[abi_decoder_header_def]) >>
  drule_all source_fixed_array_values >> strip_tac >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  qpat_x_assum `av = _` SUBST_ALL_TAC >>
  `LIST_REL (abi_decoder_coherent ce env sf) (REPLICATE n ty) (REPLICATE n tv)` by
    (qpat_assum `abi_decoder_coherent ce env sf ty tv` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[LIST_REL_EL_EQN, EL_REPLICATE]) >>
  `LENGTH avs = n` by
    (qpat_assum `vyper_to_abi_list env (REPLICATE n ty) vs = SOME avs`
       (mp_tac o MATCH_MP abi_encoder_list_conversion) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `enc (vyper_to_abi_type env (ArrayT ty (Fixed n))) (ListV avs) =
    enc (Tuple (MAP (vyper_to_abi_type env) (REPLICATE n ty))) (ListV avs)` by
    (qpat_assum `LENGTH avs = n` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[vyperABITheory.vyper_to_abi_type_def, map_replicate,
       contractABITheory.enc_def]) >>
  qpat_x_assum `enc _ _ = enc _ _` SUBST_ALL_TAC >>
  drule_all coherent_member_infos_indexed >> strip_tac >>
  drule_all coherent_source_list_head_lengths >> strip_tac >>
  `compile_abi_decode_complex_elems (Var child) childsrc CALLDATALOAD
    (Lit 0w) (Lit 0w) (abi_decoder_member_infos sf ce (REPLICATE n ty))
    0 0 middle = ((),end_st)` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[exprLoweringTheory.type_to_abi_dec_info_def,
       Once abiEncoderTheory.compile_abi_decode_to_buf_def,
       abi_decoder_member_infos_def, map_replicate, REPLICATE_GENLIST]) >>
  mp_tac (Q.INST [`tys` |-> `REPLICATE n ty`, `tvs` |-> `REPLICATE n tv`,
    `root` |-> `child`, `d` |-> `e`,
    `cap` |-> `type_memory_size (ArrayTV tv (Fixed n))`,
    `src` |-> `childsrc`, `cdsbase` |-> `srcpos`,
    `ats` |-> `MAP (vyper_to_abi_type env) (REPLICATE n ty)`,
    `elems` |-> `abi_decoder_member_infos sf ce (REPLICATE n ty)`,
    `sb` |-> `end_st`, `lo` |-> `lower`] source_owned_complex_elems_ptr) >>
  (impl_tac >-
    (qx_gen_tac `i` >> rpt gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `EL i (REPLICATE n tv) = tv /\ EL i (REPLICATE n ty) = ty` by
       (qpat_assum `i < LENGTH (REPLICATE n ty)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[EL_REPLICATE]) >>
     qpat_x_assum `EL i (REPLICATE n tv) = tv` SUBST_ALL_TAC >>
     qpat_x_assum `EL i (REPLICATE n ty) = ty` SUBST_ALL_TAC >>
     first_x_assum irule >> asm_rewrite_tac[] >> metis_tac[])) >>
  disch_then (qspecl_then [`middle`,`r`,`G`,`tn`] mp_tac) >>
  (impl_tac >-
    (qpat_x_assum `!v av child childsrc e srcpos root d outsz middle end_st r G tn oid base_addr owner_cap ctx fn site limit lower PG. _` kall_tac >>
     asm_rewrite_tac[] >> conj_tac
     >- (qx_gen_tac `i` >> strip_tac >>
         `i < LENGTH (MAP (vyper_to_abi_type env) (REPLICATE n ty))` by
           (qpat_assum `i < LENGTH (REPLICATE n ty)` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
         drule_all sourceEncodingWindowsTheory.structural_tuple_indexed_source >>
         strip_tac >> decide_tac) >>
     simp[NoAsms, map_replicate, SUM_REPLICATE,
       valueEncodingTheory.type_memory_size_def] >>
     qpat_assum `abi_decoder_operand_live middle.cs_next_var childsrc` mp_tac >>
     qpat_assum `abi_decoder_operand_live middle.cs_next_var (Var child)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def,
       compileEnvTheory.not_fresh_at_def] >>
     Cases_on `childsrc` >> simp[])) >>
  strip_tac >>
  qpat_x_assum `!v av child childsrc e srcpos root d outsz middle end_st r G tn oid base_addr owner_cap ctx fn site limit lower PG. _` kall_tac >>
  `!mem. (!i. i < n ==> val_in_memory (EL i (REPLICATE n tv)) (EL i vs)
      (e + SUM (MAP type_memory_size (TAKE i (REPLICATE n tv)))) mem) ==>
    val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV sp)) e mem` by
    (gen_tac >> strip_tac >> irule typed_memory_sarray_intro >>
     asm_rewrite_tac[] >> qx_gen_tac `i` >> strip_tac >>
     qpat_x_assum `!i. i < n ==> val_in_memory _ _ _ mem` (qspec_then `i` mp_tac) >>
     qpat_assum `!i. i < n ==> EL i vs = _` (qspec_then `i` mp_tac) >>
     qpat_assum `i < n` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[EL_REPLICATE, entryDecodeStaticPropsTheory.sparse_val_def] >>
     simp[Once REPLICATE_GENLIST, TAKE_GENLIST] >>
     simp[GSYM REPLICATE_GENLIST, map_replicate, SUM_REPLICATE] >>
     rpt strip_tac >> gvs[arithmeticTheory.MIN_DEF, arithmeticTheory.MULT_COMM]) >>
  qexistsl_tac [`t`,`H`,`u`,`fp`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (qpat_x_assum `!mem. (!i. i < n ==> _) ==> _` irule >>
      qpat_x_assum `!i. i < LENGTH (REPLICATE n ty) ==> _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!mem. (!i. i < n ==> _) ==> _` irule >>
      qpat_x_assum `!i. i < LENGTH (REPLICATE n ty) ==> _` mp_tac >>
      qpat_assum `mem_agree_outside _ _ mem` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[]) >>
  irule ptr_covers_frame >> goal_assum (drule_at Any) >>
  asm_rewrite_tac[] >>
  `not_fresh_at middle root` by
    (qpat_assum `abi_decoder_operand_live middle.cs_next_var (Var root)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def,
       compileEnvTheory.not_fresh_at_def]) >>
  metis_tac[venomStateTheory.eval_operand_def]
QED

Resume source_owned_coherent_decoder_ptr[tuple]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `LIST_REL _ tys tvs` mp_tac >>
  pure_rewrite_tac[LIST_REL_EL_EQN] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `!n. n < LENGTH tys ==> _` (mk_asm "members") >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `LIST_REL (abi_decoder_coherent ce env sf) tys tvs` by
    (simp_tac bool_ss [LIST_REL_EL_EQN] >>
     asm_rewrite_tac[] >> qx_gen_tac `i` >> strip_tac >>
     asm_x "members" (qspec_then `i` mp_tac) >>
     asm_rewrite_tac[] >> simp_tac bool_ss []) >>
  drule_all source_tuple_values >> strip_tac >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  qpat_x_assum `av = _` SUBST_ALL_TAC >>
  drule_all coherent_member_infos_indexed >> strip_tac >>
  drule_all coherent_source_list_head_lengths >> strip_tac >>
  `compile_abi_decode_complex_elems (Var child) childsrc CALLDATALOAD
    (Lit 0w) (Lit 0w) (abi_decoder_member_infos sf ce tys)
    0 0 middle = ((),end_st)` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[exprLoweringTheory.type_to_abi_dec_info_def,
       Once abiEncoderTheory.compile_abi_decode_to_buf_def,
       abi_decoder_member_infos_def]) >>
  mp_tac (Q.INST [`root` |-> `child`, `d` |-> `e`,
    `cap` |-> `type_memory_size (TupleTV tvs)`,
    `src` |-> `childsrc`, `cdsbase` |-> `srcpos`,
    `ats` |-> `MAP (vyper_to_abi_type env) tys`,
    `elems` |-> `abi_decoder_member_infos sf ce tys`,
    `sb` |-> `end_st`, `lo` |-> `lower`] source_owned_complex_elems_ptr) >>
  (impl_tac >-
    (qx_gen_tac `i` >> rpt gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     asm_x "members" (qspec_then `i` drule) >> strip_tac >>
     first_x_assum irule >> asm_rewrite_tac[] >> metis_tac[])) >>
  disch_then (qspecl_then [`middle`,`r`,`G`,`tn`] mp_tac) >>
  (impl_tac >-
    (asm_x "members" kall_tac >>
     qpat_assum `mem_bytes_at srcpos _ _ = _` mp_tac >>
     qpat_assum `srcpos + LENGTH _ < dimword (:256)` mp_tac >>
     simp_tac bool_ss [vyperABITheory.vyper_to_abi_type_def,
       abiDecoderMembersTheory.vyper_to_abi_types_MAP] >> rpt disch_tac >>
     asm_rewrite_tac[] >> conj_tac
     >- (qx_gen_tac `i` >> strip_tac >>
         `i < LENGTH (MAP (vyper_to_abi_type env) tys)` by simp[] >>
         drule_all sourceEncodingWindowsTheory.structural_tuple_indexed_source >>
         strip_tac >> decide_tac) >>
     simp[NoAsms, valueEncodingTheory.type_memory_size_def,
       valueEncodingProofsTheory.type_memory_size_list_sum] >>
     qpat_assum `abi_decoder_operand_live middle.cs_next_var childsrc` mp_tac >>
     qpat_assum `abi_decoder_operand_live middle.cs_next_var (Var child)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def,
       compileEnvTheory.not_fresh_at_def] >>
     Cases_on `childsrc` >> simp[])) >>
  strip_tac >> asm_x "members" kall_tac >>
  qexistsl_tac [`t`,`H`,`u`,`fp`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (simp[NoAsms, Once valueEncodingTheory.val_in_memory_def] >>
      irule typedCopyTuplePtrTheory.tuple_in_memory_from_elements >>
      qpat_assum `LIST_REL value_has_type tvs vs` mp_tac >>
      qpat_assum `LENGTH tys = LENGTH tvs` mp_tac >>
      qpat_assum `!i. i < LENGTH tys ==> val_in_memory _ _ _ _ /\ _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[LIST_REL_EL_EQN] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      simp[NoAsms, Once valueEncodingTheory.val_in_memory_def] >>
      irule typedCopyTuplePtrTheory.tuple_in_memory_from_elements >>
      qpat_assum `LIST_REL value_has_type tvs vs` mp_tac >>
      qpat_assum `LENGTH tys = LENGTH tvs` mp_tac >>
      qpat_assum `!i. i < LENGTH tys ==> val_in_memory _ _ _ _ /\ _` mp_tac >>
      qpat_assum `mem_agree_outside _ _ mem` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[LIST_REL_EL_EQN] >> metis_tac[]) >>
  irule ptr_covers_frame >> goal_assum (drule_at Any) >>
  asm_rewrite_tac[] >>
  `not_fresh_at middle root` by
    (qpat_assum `abi_decoder_operand_live middle.cs_next_var (Var root)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def,
       compileEnvTheory.not_fresh_at_def]) >>
  metis_tac[venomStateTheory.eval_operand_def]
QED

Resume source_owned_coherent_decoder_ptr[struct]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `LIST_REL _ (MAP SND args) tvs` mp_tac >>
  pure_rewrite_tac[LIST_REL_EL_EQN] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `!n. n < LENGTH (MAP SND args) ==> _` (mk_asm "members") >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `LIST_REL (abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid))
    (MAP SND args) tvs` by
    (simp_tac bool_ss [LIST_REL_EL_EQN] >> asm_rewrite_tac[] >>
     qx_gen_tac `i` >> strip_tac >>
     asm_x "members" (qspec_then `i` mp_tac) >>
     asm_rewrite_tac[] >> simp_tac bool_ss []) >>
  `LENGTH args = LENGTH tvs` by
    (qpat_assum `LENGTH (MAP SND args) = LENGTH tvs` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  drule_all source_struct_values >> strip_tac >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  qpat_x_assum `av = _` SUBST_ALL_TAC >>
  drule_all coherent_member_infos_indexed >> strip_tac >>
  drule_all coherent_source_list_head_lengths >> strip_tac >>
  `MAP (FST o SND) fields = MAP SND args` by
    (qpat_assum `MAP (\(name,ty,sz). (name,ty)) fields = args` (SUBST1_TAC o SYM) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]) >>
  `compile_abi_decode_complex_elems (Var child) childsrc CALLDATALOAD
    (Lit 0w) (Lit 0w) (abi_decoder_member_infos (sf \\ nsid_to_string nsid) ce (MAP SND args))
    0 0 middle = ((),end_st)` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
     drule abi_decoder_struct_infos >> disch_then (qspec_then `ce` SUBST1_TAC) >>
     asm_rewrite_tac[] >>
     simp[Once abiEncoderTheory.compile_abi_decode_to_buf_def]) >>
  mp_tac (Q.INST [`env` |-> `env \\ nsid`, `sf` |-> `sf \\ nsid_to_string nsid`,
    `tys` |-> `MAP SND (args : (string # vyperAST$type) list)`,
    `vs` |-> `MAP SND (fields' : (string # vyperValue$value) list)`,
    `root` |-> `child`, `d` |-> `e`,
    `cap` |-> `type_memory_size (StructTV (ZIP (MAP FST (args : (string # vyperAST$type) list),tvs)))`,
    `src` |-> `childsrc`, `cdsbase` |-> `srcpos`,
    `ats` |-> `MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND (args : (string # vyperAST$type) list))`,
    `elems` |-> `abi_decoder_member_infos (sf \\ nsid_to_string nsid) ce (MAP SND (args : (string # vyperAST$type) list))`,
    `sb` |-> `end_st`, `lo` |-> `lower`] source_owned_complex_elems_ptr) >>
  (impl_tac >-
    (qx_gen_tac `i` >> rpt gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     asm_x "members" (qspec_then `i` drule) >> strip_tac >>
     first_x_assum irule >> asm_rewrite_tac[] >> metis_tac[])) >>
  disch_then (qspecl_then [`middle`,`r`,`G`,`tn`] mp_tac) >>
  (impl_tac >-
    (asm_x "members" kall_tac >>
     `vyper_to_abi_type env (StructT nsid) =
       Tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))` by
       (qpat_assum `FLOOKUP env nsid = _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[Once vyperABITheory.vyper_to_abi_type_def,
          abiDecoderMembersTheory.vyper_to_abi_types_MAP]) >>
     qpat_assum `mem_bytes_at srcpos _ _ = _` mp_tac >>
     qpat_assum `srcpos + LENGTH _ < dimword (:256)` mp_tac >>
     rpt disch_tac >>
     qpat_x_assum `vyper_to_abi_type env (StructT nsid) = _` SUBST_ALL_TAC >>
     asm_rewrite_tac[] >>
     conj_tac
     >- (qx_gen_tac `i` >> strip_tac >>
         `i < LENGTH (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))` by simp[] >>
         drule_all sourceEncodingWindowsTheory.structural_tuple_indexed_source >>
         strip_tac >>
         qpat_assum `abi_tuple_child_offset _ _ i + _ <= _` mp_tac >>
         qpat_assum `srcpos + LENGTH _ < dimword (:256)` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     `SUM (MAP type_memory_size tvs) <=
       type_memory_size (StructTV (ZIP (MAP FST args,tvs)))` by
       (qpat_assum `LENGTH args = LENGTH tvs` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[valueEncodingTheory.type_memory_size_def,
          valueEncodingProofsTheory.type_memory_size_fields_sum, MAP_ZIP]) >>
     asm_rewrite_tac[] >>
     qpat_assum `abi_decoder_operand_live middle.cs_next_var childsrc` mp_tac >>
     qpat_assum `abi_decoder_operand_live middle.cs_next_var (Var child)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def,
       compileEnvTheory.not_fresh_at_def] >>
     Cases_on `childsrc` >> simp[])) >>
  strip_tac >> asm_x "members" kall_tac >>
  qexistsl_tac [`t`,`H`,`u`,`fp`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (simp[NoAsms, Once valueEncodingTheory.val_in_memory_def,
        valueEncodingProofsTheory.fields_in_memory_tuple, MAP_ZIP] >>
      irule typedCopyTuplePtrTheory.tuple_in_memory_from_elements >>
      qpat_assum `LIST_REL value_has_type tvs (MAP SND fields')` mp_tac >>
      qpat_assum `LENGTH args = LENGTH tvs` mp_tac >>
      qpat_assum `!i. i < LENGTH (MAP SND args) ==> val_in_memory _ _ _ _ /\ _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[LIST_REL_EL_EQN, MAP_ZIP] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      simp[NoAsms, Once valueEncodingTheory.val_in_memory_def,
        valueEncodingProofsTheory.fields_in_memory_tuple, MAP_ZIP] >>
      irule typedCopyTuplePtrTheory.tuple_in_memory_from_elements >>
      qpat_assum `LIST_REL value_has_type tvs (MAP SND fields')` mp_tac >>
      qpat_assum `LENGTH args = LENGTH tvs` mp_tac >>
      qpat_assum `!i. i < LENGTH (MAP SND args) ==> val_in_memory _ _ _ _ /\ _` mp_tac >>
      qpat_assum `mem_agree_outside _ _ mem` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[LIST_REL_EL_EQN, MAP_ZIP] >> metis_tac[]) >>
  irule ptr_covers_frame >> goal_assum (drule_at Any) >>
  asm_rewrite_tac[] >>
  `not_fresh_at middle root` by
    (qpat_assum `abi_decoder_operand_live middle.cs_next_var (Var root)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def,
       compileEnvTheory.not_fresh_at_def]) >>
  metis_tac[venomStateTheory.eval_operand_def]
QED

Finalise source_owned_coherent_decoder_ptr
