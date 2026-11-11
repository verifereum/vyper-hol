(* Counted physical execution of heterogeneous aggregate decoders. *)
Theory bodyIntCallDecoderCountedAggregates
Ancestors
  bodyIntCallDecoderCountedMembers bodyIntCallDecoderCountedMembersContract bodyIntCallDecoderCountedEmpty
  bodyIntCallDecoderCountedContract abiScratchDecoderTuple abiScratchDecoderRecursive
  abiDecoderFixedMemory abiDecoderStruct abiStaticDynarrayLayout vyperTyping vyperValue vyperAST finite_map
  abiDecoderComplexExecute abiDecoderComplexGuard abiDecoderComplexHead
  abiScratchAfterAddress abiScratchEffect abiDecoderMembers abiDecoderContract
  abiDecoderEffect abiDecoderReentry abiScratchDecoderContract
  abiDecoderTypedContract abiDecoderMemberInfos abiDecoderLoop abiDecodeRanges
  compileEnv valueEncoding valueEncodingProps vyperABI fragGasPath venomState venomExecSemantics
  words list rich_list arithmetic

Theorem intcall_scratch_decoder_complex_execute:
  LIST_REL (intcall_scratch_decoder_counted ce env sf) tys tvs /\
  compile_abi_decode_to_buf dst src opc base_op hi (DecComplex dyn (abi_decoder_member_infos sf ce tys))
    st = ((),final) /\ fn_has_code st final func /\
  (st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_members ce env sf tys tvs
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs bs) vs /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
  abi_scratch_decoder_ranges opc base_op hi src dst B sb (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) tys)) first last b cap initial /\
  mem_bytes_at (B + sb) (LENGTH bs) (abi_decode_source opc initial) = bs /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_operand_live st.cs_next_var base_op /\ (base_op = Lit 0w \/ opc = MLOAD) /\
  abi_decoder_budget first last b cap initial /\ first <= abi_decoder_entry_floor st /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. tuple_in_memory vs tvs d actual.vs_memory /\
    abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
      d (SUM (MAP (type_memory_bytes ce) tys)) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_complex_guard_inputs >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_complex_trace >> strip_tac >>
  rename1 `abi_decode_complex_head_guard src hi _ st = ((),middle)` >>
  drule_all abi_decoder_complex_code >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var /\ first <= abi_decoder_entry_floor middle` by
    (fs[abi_decoder_entry_floor_def] >> decide_tac) >>
  mp_tac (Q.INST [`st'` |-> `middle`, `head_sz` |->
    `FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys)`]
    intcall_decoder_complex_head_guard_path) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  strip_tac >> rename1 `abi_decoder_address_frame _ initial prepared` >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`,
    `new_next` |-> `middle.cs_next_var`, `len` |-> `LENGTH (bs:word8 list)`,
    `sz` |-> `SUM (MAP (type_memory_bytes ce) tys)`, `hi_op` |-> `hi:operand`]
    abi_scratch_decoder_address_observations) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule intcall_scratch_decoder_members_counted_list >> strip_tac >>
  mp_tac (SIMP_RULE bool_ss [MAP, SUM, APPEND, ADD_CLAUSES]
    (Q.INST [`st` |-> `middle`, `initial` |-> `prepared:venom_state`, `pretys` |-> `[]`]
      intcall_scratch_decoder_members_counted_run)) >>
  impl_tac >- asm_simp_tac (srw_ss()) [Once abi_decoder_members_def, Excl "enc_def"] >>
  strip_tac >> rename1 `gas_path ctx func prepared n' (OK actual)` >>
  `abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
    d (SUM (MAP (type_memory_bytes ce) tys)) b cap initial actual` by
    (irule abi_scratch_effect_after_address >>
     qexistsl_tac [`d`, `final.cs_next_id`, `abi_decoder_entry_floor middle`,
       `middle.cs_next_var`, `SUM (MAP (type_memory_bytes ce) tys)`, `prepared`] >>
     asm_simp_tac arith_ss [abi_decoder_entry_floor_def]) >>
  qexistsl_tac [`actual`, `n + n'`] >> asm_simp_tac bool_ss [] >>
  irule gas_path_then >> goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_scratch_decoder_counted_tuple:
  LIST_REL (intcall_scratch_decoder_counted ce env sf) tys tvs ==>
  intcall_scratch_decoder_counted ce env sf (TupleT tys) (TupleTV tvs)
Proof
  disch_tac >> simp_tac bool_ss [intcall_scratch_decoder_counted_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_decoder_tuple_inputs >> strip_tac >>
  gnvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_tuple_infos]) >>
  mp_tac (Q.INST [`st` |-> `start`, `final` |-> `end_st`,
    `B` |-> `src_base`, `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields) tys`]
    intcall_scratch_decoder_complex_execute) >>
  impl_tac >- asm_simp_tac arith_ss [ADD_COMM] >>
  simp_tac bool_ss [val_in_memory_tuple]
QED

Theorem intcall_scratch_decoder_counted_fixed_array:
  intcall_scratch_decoder_counted ce env sf ty tv /\
  (0 < n /\ is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) ==>
  intcall_scratch_decoder_counted ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [intcall_scratch_decoder_counted_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_decoder_fixed_array_inputs >> strip_tac >>
  qpat_x_assum `LENGTH vs = n` (SUBST_ALL_TAC o SYM) >> gnvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  `LIST_REL (intcall_scratch_decoder_counted ce env sf)
    (REPLICATE (LENGTH vs) ty) (REPLICATE (LENGTH vs) tv)` by simp[LIST_REL_REPLICATE_same] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_fixed_array_infos]) >>
  qmatch_asmsub_rename_tac `abi_scratch_decoder_ranges opc base_op hi src dst B sb` >>
  mp_tac (SIMP_RULE bool_ss [map_replicate, SUM_REPLICATE]
    (Q.INST [`st` |-> `start`, `final` |-> `end_st`, `tys` |-> `REPLICATE (LENGTH vs) ty`,
      `tvs` |-> `REPLICATE (LENGTH vs) tv`, `dyn` |-> `is_abi_dynamic ce.ce_struct_fields ty`]
      intcall_scratch_decoder_complex_execute)) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [EVERY_MEM, MEM_REPLICATE,
    Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
    Cases_on `vs` >> gvs[MULT_CLAUSES, Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"]) >>
  strip_tac >>
  `val_in_memory (ArrayTV tv (Fixed (LENGTH vs)))
    (ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs))) d actual.vs_memory`
    by (irule abi_decoder_fixed_array_memory >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [map_replicate, SUM_REPLICATE] >>
  goal_assum (drule_at Any)
QED

Theorem intcall_scratch_decoder_counted_struct:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  LIST_REL (intcall_scratch_decoder_counted ce (env \\ nsid) (sf \\ nsid_to_string nsid))
    (MAP SND args) tvs ==>
  intcall_scratch_decoder_counted ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH tvs = LENGTH args` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  simp_tac bool_ss [intcall_scratch_decoder_counted_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_struct_inputs >> strip_tac >> gnvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  qmatch_asmsub_rename_tac `abi_scratch_decoder_ranges opc base_op hi src dst B sb` >>
  drule abi_decoder_struct_infos >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `final` |-> `end_st`,
    `env` |-> `env \\ nsid`, `sf` |-> `sf \\ nsid_to_string nsid`,
    `tys` |-> `MAP SND (args:(string # vyperAST$type) list)`,
    `vs` |-> `MAP SND (fields:(string # value) list)`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields)
      (MAP SND (args:(string # vyperAST$type) list))`]
    intcall_scratch_decoder_complex_execute) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> metis_tac[ADD_COMM]) >> strip_tac >>
  rename1 `tuple_in_memory (MAP SND fields) tvs d actual.vs_memory` >>
  `fields_in_memory fields (ZIP (MAP FST args,tvs)) d actual.vs_memory` by
    (irule static_fields_memory_zip >> fs[Once value_has_type_def]) >>
  goal_assum (drule_at Any) >> asm_simp_tac bool_ss [val_in_memory_struct]
QED
