Theory abiDecoderValidFixed
Ancestors
  abiDecoderValidContract abiDecoderValidBytesInput abiValidBytesReentry abiDecoderValidBytes
  abiDecoderBytesTyped abiDecoderBytes abiDecoderCorrectLeaves abiDecoderEffect
  abiDecoderContract abiDecoderTypedContract abiDecoderReentry abiDecoderTypedCompose
  abiDecoderLoop abiDecoderFrame abiEncoderSequence abiEncoder fragExec instIdxIndep compileEnv
  emitHelperProps valueEncoding vyperABI vyperValue venomState venomExecSemantics words list
  abiDecoderValidPrefix contractABI abiDecoderMemberInfos abiDecoderMembers abiValidMembers
  abiDecodeRanges arithmetic abiDecoderComplexExecute abiDecoderComplexGuard
  abiDecoderComplexHead abiDecoderValidMemberCons abiDecoderValidMembersCorrect
  abiDecoderArraySetupInputs abiDecoderArraySetupCode abiDecoderArrayInitExec
  abiDecoderDynamicLoopSetup abiDecoderAllocation valueEncodingTyping abiDecoderStruct
  abiDecoderCoherence pair abiStaticDynarrayLayout valueEncodingProps vyperTyping
  abiDecoderTupleInputs vyperABIValid abiDecoderFixedInputs abiValidAggregateHeads
  abiCanonicalHeadSize rich_list abiDecoderFixedMemory

(* Actual noncanonical Bytes/String execution closes the recursive child API. *)
Theorem abi_decoder_valid_bytes_reach:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decoder_valid_bytes_pre n at bs payload st src dst opc hi sb d
    (abi_decoder_prune_vars st.cs_next_var initial) /\ fn_has_code st st' func /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d actual.vs_memory /\
    val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d actual.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule_all abi_decoder_valid_bytes_reentry >> strip_tac >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_valid_bytes_pre_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  drule abi_decoder_inst_extends_prefix >> strip_tac >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial reached` >> qexists_tac `reached` >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx] >> first_assum ACCEPT_TAC
QED

Theorem abi_decoder_valid_pre_output_separated:
  abi_decoder_valid_pre ce env sf ty tv bs v st src dst opc hi sb d b cap initial ==>
  d + type_memory_bytes ce ty <= b \/ b + cap <= d
Proof
  simp_tac bool_ss [abi_decoder_valid_pre_def, abi_decoder_ranges_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> first_assum ACCEPT_TAC
QED

Theorem abi_decoder_valid_correct_bytestring:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) ==>
  abi_decoder_valid_correct ce env sf ty tv
Proof
  disch_then assume_tac >> simp_tac bool_ss [abi_decoder_valid_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_bytes_input >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_decoder_valid_bytes_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `val_in_memory tv v d actual.vs_memory` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  drule abi_decoder_valid_pre_output_separated >> disch_then assume_tac >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
    `lo` |-> `start.cs_next_id`, `hi` |-> `end_st.cs_next_id`, `next` |-> `start.cs_next_var`,
    `sz` |-> `type_memory_bytes ce ty`] abi_decoder_scratch_free_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >>
  qpat_assum `type_memory_bytes ce ty = abi_decode_bytes_copy_size n`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  asm_simp_tac bool_ss []
QED

(* All primitive source types close the actual-source recursive API. *)
Theorem abi_decoder_valid_base_cases:
  !bt. ~is_dynamic (vyper_to_abi_type env (BaseT bt)) \/
    ?n. bt = BytesT (Dynamic n) \/ bt = StringT n
Proof
  Cases >> simp[vyper_to_abi_type_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >> simp[]
QED

Theorem abi_decoder_valid_correct_base:
  abi_decoder_valid_correct ce env sf (BaseT bt) (BaseTV bt)
Proof
  mp_tac (Q.SPEC `bt` abi_decoder_valid_base_cases) >>
  disch_then (DISJ_CASES_THEN2 assume_tac (qx_choose_then `n` assume_tac))
  >- (irule abi_decoder_valid_correct_static >> first_assum ACCEPT_TAC) >>
  irule abi_decoder_valid_correct_bytestring >> qexists_tac `n` >> asm_simp_tac (srw_ss()) []
QED

Theorem abi_decoder_valid_correct_flag:
  abi_decoder_valid_correct ce env sf (FlagT nsid) (FlagTV n)
Proof
  irule abi_decoder_valid_correct_static >> simp[vyper_to_abi_type_def]
QED

(* ===== Inputs ===== *)

(* Actual source validity supplies the emitted aggregate head-window guard. *)

Theorem abi_decoder_valid_complex_guard_inputs:
  abi_decoder_members ce env sf tys tvs avs vs /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) tys)) b cap initial ==>
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys) <= hb /\
    hb < dimword (:256))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_members_relations >> strip_tac >>
  drule abi_decoder_member_infos_layout >> strip_tac >>
  drule abi_valid_members_view >> strip_tac >>
  `FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys) <= LENGTH bs`
    by (asm_simp_tac bool_ss [] >> decide_tac) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  asm_simp_tac bool_ss [] >> Cases_on `hi = Lit 0w` >- simp[] >>
  qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `eval_operand hi initial = SOME (n2w hb)` >>
  qexists_tac `hb` >> asm_simp_tac bool_ss [] >> decide_tac
QED

(* ===== Execute ===== *)

(* Execute a DecComplex guard and its actual noncanonical member slices.
   TOP-LEVEL: abi_decoder_valid_complex_execute. *)

Theorem abi_decoder_valid_complex_execute:
  LIST_REL (abi_decoder_valid_correct ce env sf) tys tvs /\
  compile_abi_decode_to_buf dst src opc hi (DecComplex dyn (abi_decoder_member_infos sf ce tys))
    st = ((),final) /\ fn_has_code st final func /\
  (st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_members ce env sf tys tvs
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs bs) vs /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) tys)) b cap initial /\
  mem_bytes_at sb (LENGTH bs)
    (abi_decode_source opc initial) = bs /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. tuple_in_memory vs tvs d actual.vs_memory /\
    abi_decoder_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
      d (SUM (MAP (type_memory_bytes ce) tys)) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_complex_guard_inputs >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_complex_trace >> strip_tac >>
  rename1 `abi_decode_complex_head_guard src hi _ st = ((),middle)` >>
  drule_all abi_decoder_complex_code >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var /\ first <= middle.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`st'` |-> `middle`, `head_sz` |->
    `FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys)`]
    abi_decode_complex_head_guard_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  drule_all abi_decoder_address_frame_ranges >> strip_tac >>
  drule_all abi_decoder_address_frame_source >> disch_then (qspec_then `opc` assume_tac) >>
  `abi_decoder_budget first last b cap prepared` by
    (qpat_assum `abi_decoder_address_frame _ _ _`
      (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
     mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `prepared:venom_state`]
       abi_decoder_budget_transport) >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live middle.cs_next_var src /\ abi_decoder_operand_live middle.cs_next_var dst /\
   abi_decoder_operand_live middle.cs_next_var hi` by
    (rpt conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  drule abi_decoder_valid_members_correct_list >> strip_tac >>
  mp_tac (SIMP_RULE bool_ss [MAP, SUM, APPEND, ADD_CLAUSES]
    (Q.INST [`st` |-> `middle`, `initial` |-> `prepared:venom_state`,
      `pretys` |-> `[]`]
      abi_decoder_valid_members_correct_run)) >>
  impl_tac >- asm_simp_tac (srw_ss()) [Once abi_decoder_members_def, Excl "enc_def"] >>
  strip_tac >> rename1 `tuple_in_memory vs tvs d actual.vs_memory` >>
  `abi_decoder_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
    d (SUM (MAP (type_memory_bytes ce) tys)) b cap initial actual` by
    (mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `final.cs_next_id`,
      `next` |-> `st.cs_next_var`, `child_lo` |-> `middle.cs_next_id`,
      `child_next` |-> `middle.cs_next_var`, `s` |-> `initial:venom_state`,
      `prepared` |-> `prepared:venom_state`, `t` |-> `actual:venom_state`,
      `sz` |-> `SUM (MAP (type_memory_bytes ce) tys)`] abi_decoder_address_then_effect) >>
     asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

(* ===== Inputs ===== *)

(* Positional struct metadata and ranges over actual noncanonical source bytes. *)

Theorem abi_decoder_valid_struct_inputs:
  FLOOKUP env nsid = SOME (StructArgs args) /\ LENGTH tvs = LENGTH args /\
  abi_decoder_valid_pre ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
    bs v st src dst opc hi sb d b cap initial ==>
  ?cfields fields.
    FLOOKUP sf (nsid_to_string nsid) = SOME cfields /\
    MAP (FST o SND) cfields = MAP SND args /\
    v = StructV fields /\
    value_has_type (StructTV (ZIP (MAP FST args,tvs))) (StructV fields) /\
    abi_decoder_members ce (env \\ nsid) (sf \\ nsid_to_string nsid)
      (MAP SND args) tvs
      (abi_decode_members (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) bs bs)
      (MAP SND fields) /\
    vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) bs bs /\
    type_memory_bytes ce (StructT nsid) = SUM (MAP (type_memory_bytes ce) (MAP SND args)) /\
    abi_decoder_ranges opc hi src dst sb
      (LENGTH bs)
      d (SUM (MAP (type_memory_bytes ce) (MAP SND args))) b cap initial /\
    mem_bytes_at sb
      (LENGTH bs)
      (abi_decode_source opc initial) =
        bs /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var hi
Proof
  simp_tac bool_ss [abi_decoder_valid_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  drule abi_decoder_struct_values >> strip_tac >> gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  drule_all abi_decoder_struct_members_at >> strip_tac >>
  drule abi_decoder_members_relations >> strip_tac >>
  drule abi_decoder_member_infos_layout >> strip_tac >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (irule type_memory_size_fields_zip >> simp[]) >>
  `type_memory_bytes ce (StructT nsid) = SUM (MAP (type_memory_bytes ce) (MAP SND args))` by
    fs[Once type_memory_size_def, Excl "enc_def"] >>
  drule_all abi_decoder_struct_field_types >> strip_tac >>
  `vyper_decode_valid_enc (Tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))) bs` by
    (qpat_x_assum `vyper_decode_valid_enc _ bs` mp_tac >>
     asm_simp_tac (srw_ss()) [Once vyper_to_abi_type_def, vyper_to_abi_types_MAP,
       Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"]) >>
  drule abi_valid_tuple_view >> strip_tac >>
  qexists_tac `cfields` >>
  gvs[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP,
    Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  qpat_x_assum `vyper_decode_valid_enc (Tuple _) bs` mp_tac >> simp_tac bool_ss [Once vyper_decode_valid_enc_def]
QED

(* ===== Decoder Valid Struct ===== *)

(* Actual-source struct correctness retains independently descending type maps. *)

Theorem abi_decoder_valid_correct_struct:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  LIST_REL (abi_decoder_valid_correct ce (env \\ nsid) (sf \\ nsid_to_string nsid))
    (MAP SND args) tvs ==>
  abi_decoder_valid_correct ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH tvs = LENGTH args` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  simp_tac bool_ss [abi_decoder_valid_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_struct_inputs >> strip_tac >> gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  (drule abi_decoder_struct_infos >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `final` |-> `end_st`,
    `env` |-> `env \\ nsid`, `sf` |-> `sf \\ nsid_to_string nsid`,
    `tys` |-> `MAP SND (args:(string # vyperAST$type) list)`,
    `vs` |-> `MAP SND (fields:(string # value) list)`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields)
      (MAP SND (args:(string # vyperAST$type) list))`]
    abi_decoder_valid_complex_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `tuple_in_memory (MAP SND fields) tvs d actual.vs_memory` >>
  `fields_in_memory fields (ZIP (MAP FST args,tvs)) d actual.vs_memory` by
    (irule static_fields_memory_zip >> fs[Once value_has_type_def]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [val_in_memory_struct])
QED

(* ===== Inputs ===== *)

(* Recover tuple metadata from the actual valid source bytes. *)

Theorem abi_decoder_valid_tuple_inputs:
  abi_decoder_valid_pre ce env sf (TupleT tys) (TupleTV tvs) bs v
    st src dst opc hi sb d b cap initial ==>
  ?vs. v = ArrayV (TupleV vs) /\
    abi_decoder_members ce env sf tys tvs
      (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs bs) vs /\
    vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
    type_memory_bytes ce (TupleT tys) = SUM (MAP (type_memory_bytes ce) tys) /\
    abi_decoder_ranges opc hi src dst sb (LENGTH bs)
      d (SUM (MAP (type_memory_bytes ce) tys)) b cap initial /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var hi
Proof
  simp_tac bool_ss [abi_decoder_valid_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `type_memory_bytes ce (TupleT tys) = SUM (MAP (type_memory_bytes ce) tys)`
    by (simp[Once type_memory_bytes_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  `vyper_decode_valid_enc (Tuple (MAP (vyper_to_abi_type env) tys)) bs` by
    (qpat_x_assum `vyper_decode_valid_enc _ bs` mp_tac >>
     simp_tac bool_ss [Once vyper_to_abi_type_def, vyper_to_abi_types_MAP]) >>
  drule abi_valid_tuple_view >> strip_tac >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  drule abi_decoder_tuple_values >> strip_tac >>
  gvs[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP,
    Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  drule_all abi_decoder_tuple_members >> strip_tac >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `vyper_decode_valid_enc (Tuple _) bs` mp_tac >> simp_tac bool_ss [Once vyper_decode_valid_enc_def]
QED

(* ===== Decoder Valid Tuple ===== *)

(* Tuple decoding follows arbitrary source-valid member offsets and payloads. *)

Theorem abi_decoder_valid_correct_tuple:
  LIST_REL (abi_decoder_valid_correct ce env sf) tys tvs ==>
  abi_decoder_valid_correct ce env sf (TupleT tys) (TupleTV tvs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [abi_decoder_valid_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_valid_tuple_inputs >> strip_tac >>
  gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_tuple_infos]) >>
  mp_tac (Q.INST [`st` |-> `start`, `final` |-> `end_st`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields) tys`] abi_decoder_valid_complex_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  asm_simp_tac bool_ss [val_in_memory_tuple]
QED

Theorem abi_decoder_valid_base_member_nonempty:
  !bt. is_dynamic (vyper_to_abi_type env (BaseT bt)) ==>
    !elem. vyper_to_abi_type env (BaseT bt) <> Array (SOME 0) elem
Proof
  Cases >> simp[vyper_to_abi_type_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >> simp[]
QED

Theorem abi_decoder_valid_correct_base_tuple:
  !bts. abi_decoder_valid_correct ce env sf
    (TupleT (MAP BaseT bts)) (TupleTV (MAP BaseTV bts))
Proof
  gen_tac >>
  `LIST_REL (abi_decoder_valid_correct ce env sf) (MAP BaseT bts) (MAP BaseTV bts)` by
    (Induct_on `bts` >> simp[abi_decoder_valid_correct_base]) >>
  `EVERY (\ty. is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) (MAP BaseT bts)` by
    (simp_tac bool_ss [EVERY_MAP, EVERY_MEM, combinTheory.o_DEF] >>
     qx_gen_tac `bt` >> strip_tac >>
     MATCH_ACCEPT_TAC (Q.SPEC `bt` abi_decoder_valid_base_member_nonempty)) >>
  irule abi_decoder_valid_correct_tuple >> asm_simp_tac bool_ss []
QED

(* ===== Inputs ===== *)

(* Fixed arrays use the actual repeated-type member view of source-valid bytes. *)

Theorem abi_decoder_valid_fixed_view:
  vyper_decode_valid_enc (Array (SOME n) at) bs ==>
  vyper_decode_valid_enc_tuple (REPLICATE n at) bs bs /\
  dec (Array (SOME n) at) bs = ListV (abi_decode_members (REPLICATE n at) bs bs)
Proof
  strip_tac >>
  `vyper_decode_valid_enc_tuple (REPLICATE n at) bs bs` by
    fs[Once vyper_decode_valid_enc_def, vyper_decode_valid_enc_tuple_REPLICATE, Excl "dec_def"] >>
  asm_simp_tac (srw_ss()) [Once dec_def, LET_THM, abi_decode_array_members, abi_decode_members_value,
    Excl "dec_def", Excl "enc_def", Excl "vyper_decode_valid_enc_def"]
QED

Theorem abi_decoder_valid_fixed_array_inputs:
  abi_decoder_valid_pre ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
    bs v st src dst opc hi sb d b cap initial ==>
  ?vs. v = ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs)) /\ LENGTH vs = n /\
    abi_decoder_members ce env sf (REPLICATE n ty) (REPLICATE n tv)
      (abi_decode_members (MAP (vyper_to_abi_type env) (REPLICATE n ty)) bs bs) vs /\
    vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) (REPLICATE n ty)) bs bs /\
    type_memory_bytes ce (ArrayT ty (Fixed n)) = SUM (MAP (type_memory_bytes ce) (REPLICATE n ty)) /\
    abi_decoder_ranges opc hi src dst sb (LENGTH bs)
      d (SUM (MAP (type_memory_bytes ce) (REPLICATE n ty))) b cap initial /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var hi
Proof
  simp_tac bool_ss [abi_decoder_valid_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_fixed_array_values >> strip_tac >>
  `type_memory_bytes ce (ArrayT ty (Fixed n)) = SUM (MAP (type_memory_bytes ce) (REPLICATE n ty))`
    by simp[Once type_memory_bytes_def, map_replicate, SUM_REPLICATE] >>
  `vyper_decode_valid_enc (Array (SOME n) (vyper_to_abi_type env ty)) bs` by
    (qpat_x_assum `vyper_decode_valid_enc _ bs` mp_tac >> simp_tac bool_ss [Once vyper_to_abi_type_def]) >>
  drule abi_decoder_valid_fixed_view >> strip_tac >>
  gvs[Once vyper_to_abi_type_def, map_replicate,
    Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  qexists_tac `vs` >> asm_simp_tac bool_ss []
QED

(* ===== Decoder Valid Fixed ===== *)

(* Actual-source fixed arrays execute the shared member decoder and recover sparse values. *)

Theorem abi_decoder_valid_correct_fixed_array:
  abi_decoder_valid_correct ce env sf ty tv /\
  (0 < n /\ is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) ==>
  abi_decoder_valid_correct ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> simp_tac bool_ss [abi_decoder_valid_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_valid_fixed_array_inputs >> strip_tac >> gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  (`LIST_REL (abi_decoder_valid_correct ce env sf) (REPLICATE (LENGTH vs) ty) (REPLICATE (LENGTH vs) tv)`
    by simp[LIST_REL_REPLICATE_same] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_fixed_array_infos]) >>
  mp_tac (SIMP_RULE bool_ss [map_replicate, SUM_REPLICATE]
    (Q.INST [`st` |-> `start`, `final` |-> `end_st`, `tys` |-> `REPLICATE (LENGTH vs) ty`,
      `tvs` |-> `REPLICATE (LENGTH vs) tv`, `dyn` |-> `is_abi_dynamic ce.ce_struct_fields ty`]
      abi_decoder_valid_complex_execute)) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [EVERY_MEM, MEM_REPLICATE,
    Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
    Cases_on `vs` >> gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"]) >> strip_tac >>
  rename1 `tuple_in_memory vs (REPLICATE (LENGTH vs) tv) d actual.vs_memory` >>
  `val_in_memory (ArrayTV tv (Fixed (LENGTH vs)))
    (ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs))) d actual.vs_memory`
    by (irule abi_decoder_fixed_array_memory >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [])
QED
