Theory abiScratchDecoderTuple
Ancestors
  vyperABIValid abiScratchDecoderRanges abiScratchDecoderContract abiDecoderValidContract
  abiDecoderPrefixPre abiDecoderDynamic abiDecoderCoherence abiDecoderTypedContract
  abiDecoderContract abiDecoderReentry abiValidStatic abiDecodeRanges compileEnv valueEncoding
  vyperABI contractABI venomState words list rich_list abiScratchLeafEffect
  abiScratchEncoderContract abiDecoderReentryPointer abiDecoderPrimitiveCaller
  abiDecoderCorrectLeaves abiDecoderLoop abiDecoderFrame abiDecoderAllocation abiEncoder
  fragExec abiScratchDecoderTransport abiScratchAddress abiDecoderArraySetupCode
  abiDecoderArraySetupInputs abiDecoderDynamicLoopSetup arithmetic abiDecoderValidBytesInput
  abiDecoderValidFixed abiDecoderBytesTyped exprLowering vyperAST abiDecoderMemberInfos
  abiDecoderMembers abiValidMembers abiScratchAfterAddress abiDecoderComplexExecute
  abiDecoderComplexGuard abiDecoderComplexHead abiScratchDecoderMemberCons
  abiScratchDecoderMembersContract abiDecoderArrayInitExec abiDecoderEffect venomExecSemantics
  abiDecoderTupleInputs valueEncodingProps vyperValue

(* Existing scalar execution can use a derived empty reservation at the frontier.
   Actual bytes determine the readable prefix; no canonical whole-input equality is assumed. *)
Theorem abi_scratch_decoder_static_prefix:
  ~is_dynamic at /\ valid_enc at bs /\ abi_member_head_size at <= LENGTH bs ==>
  LENGTH (enc at (dec at bs)) <= LENGTH bs /\
  TAKE (LENGTH (enc at (dec at bs))) bs = enc at (dec at bs)
Proof
  strip_tac >>
  `static_length at <= LENGTH bs` by
    (qpat_x_assum `abi_member_head_size at <= LENGTH bs` mp_tac >>
     asm_simp_tac bool_ss [abi_member_head_size_def]) >>
  drule abi_static_prefix_static >> simp_tac bool_ss [abi_static_prefix_def] >>
  disch_then (qspec_then `bs` mp_tac) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  asm_simp_tac (srw_ss()) [LENGTH_TAKE_EQ, TAKE_TAKE_MIN, Excl "enc_def", Excl "dec_def"]
QED

Theorem abi_scratch_decoder_static_pre:
  abi_scratch_decoder_input ce env sf ty tv bs v st src dst opc hi sb d first last b cap s /\
  abi_decoder_budget first last b cap s /\ ~is_dynamic (vyper_to_abi_type env ty) ==>
  abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty)
    (dec (vyper_to_abi_type env ty) bs) v st st.cs_next_id src dst opc hi sb d
    s.vs_alloca_next 0 (abi_decoder_prune_vars st.cs_next_var s)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_input_point >> strip_tac >>
  `abi_decoder_reservation st.cs_next_id st.cs_next_id s.vs_alloca_next 0 s` by
    (mp_tac abi_scratch_decoder_point_reservation >> asm_simp_tac bool_ss []) >>
  `vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
   abi_member_head_size (vyper_to_abi_type env ty) <= LENGTH bs` by
    fs[abi_scratch_decoder_input_def, abi_member_head_size_def,
      Excl "vyper_decode_valid_enc_def", Excl "dec_def"] >>
  `valid_enc (vyper_to_abi_type env ty) bs` by
    (irule vyper_decode_valid_enc_static >> simp[]) >>
  drule_all abi_scratch_decoder_static_prefix >> strip_tac >>
  mp_tac (Q.INST [`last` |-> `st.cs_next_id`, `b` |-> `s.vs_alloca_next`, `cap` |-> `0:num`]
    abi_decoder_valid_pre_prefix) >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_word_pre:
  type_to_abi_dec_info (sf:string |-> (string # vyperAST$type # num) list) ce ty = DecPrimWord clamp /\
  abi_scratch_decoder_input ce env sf ty tv bs v st src dst opc hi sb d first last b cap s /\
  abi_decoder_budget first last b cap s ==>
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp)
    (dec (vyper_to_abi_type env ty) bs) v st st.cs_next_id src dst opc hi sb d
    s.vs_alloca_next 0 (abi_decoder_prune_vars st.cs_next_var s)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_scratch_decoder_input_def] >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  `~is_dynamic (vyper_to_abi_type env ty)` by
    (qpat_assum `type_to_abi_dec_info sf ce ty = DecPrimWord clamp` (fn eq =>
       qpat_x_assum `abi_decoder_dynamic _ = _` (mp_tac o PURE_REWRITE_RULE [eq])) >>
     simp_tac (srw_ss()) [abi_decoder_dynamic_def]) >>
  drule_all abi_scratch_decoder_static_pre >> asm_simp_tac bool_ss []
QED

(* Actual word decoders preserve the precise physical scratch footprint.
   The old scalar sequence proof is reused with a derived empty reservation. *)
Theorem abi_scratch_decoder_word:
  type_to_abi_dec_info (sf:string |-> (string # vyperAST$type # num) list) ce ty = DecPrimWord clamp ==>
  abi_scratch_decoder ce env sf ty tv
Proof
  strip_tac >> simp_tac bool_ss [abi_scratch_decoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_scratch_decoder_word_pre >> strip_tac >>
  drule abi_decoder_primitive_source >> strip_tac >>
  drule_all abi_decoder_primitive_reentry_from_state >>
    disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `actual.vs_halted = initial.vs_halted` by simp[] >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
    `lo` |-> `start.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
    `next` |-> `start.cs_next_var`, `sz` |-> `32:num`] abi_scratch_leaf_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* Address-only code preserves physical ranges, actual source bytes and older operands. *)
Theorem abi_scratch_decoder_address_observations:
  abi_scratch_decoder_ranges opc hi_op src dst sb len d sz first last b cap initial /\
  abi_decoder_address_frame next initial prepared /\ fresh_vars_wrt limit_st prepared /\
  abi_decoder_budget first last b cap initial /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi_op /\ next <= new_next ==>
  abi_scratch_decoder_ranges opc hi_op src dst sb len d sz first last b cap prepared /\
  abi_decode_source opc prepared = abi_decode_source opc initial /\
  abi_decoder_budget first last b cap prepared /\
  abi_decoder_operand_live new_next src /\ abi_decoder_operand_live new_next dst /\
  abi_decoder_operand_live new_next hi_op
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_scratch_effect first last first last next limit_st d sz b cap initial prepared` by
    (irule abi_scratch_address_effect >> asm_simp_tac bool_ss []) >>
  drule_all abi_scratch_decoder_ranges_effect >> strip_tac >>
  drule_all abi_decoder_address_frame_source >> disch_then (qspec_then `opc` assume_tac) >>
  `abi_decoder_operand_live new_next src /\ abi_decoder_operand_live new_next dst /\
   abi_decoder_operand_live new_next hi_op` by
    (rpt conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `next` >> asm_simp_tac bool_ss []) >>
  fs[abi_scratch_effect_def]
QED

(* Bytes/String execution writes only its output buffer and preserves actual allocations. *)
Theorem abi_scratch_decoder_bytestring:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) ==>
  abi_scratch_decoder ce env sf ty tv
Proof
  disch_then assume_tac >> simp_tac bool_ss [abi_scratch_decoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_input_point >> strip_tac >>
  drule_all abi_decoder_valid_bytes_input >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_decoder_valid_bytes_reach >>
    disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `val_in_memory tv v d actual.vs_memory` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `actual.vs_halted = initial.vs_halted` by simp[] >>
  qpat_assum `type_memory_bytes ce ty = abi_decode_bytes_copy_size n`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th]) >>
      PURE_REWRITE_TAC [GSYM th]) >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
    `lo` |-> `start.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
    `next` |-> `start.cs_next_var`, `sz` |-> `type_memory_bytes ce ty`] abi_scratch_leaf_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* All primitive source types close the physical decoder execution contract. *)
Theorem abi_scratch_decoder_base_shape:
  !bt. (?clamp. type_to_abi_dec_info
    (sf:string |-> (string # vyperAST$type # num) list) ce (BaseT bt) = DecPrimWord clamp) \/
    (?n. bt = BytesT (Dynamic n) \/ bt = StringT n)
Proof
  Cases >> simp[type_to_abi_dec_info_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >> simp[type_to_abi_dec_info_def]
QED

Theorem abi_scratch_decoder_base:
  abi_scratch_decoder ce env sf (BaseT bt) tv
Proof
  mp_tac (Q.SPEC `bt` abi_scratch_decoder_base_shape) >>
  disch_then (DISJ_CASES_THEN2 (qx_choose_then `clamp` assume_tac)
    (qx_choose_then `n` assume_tac))
  >- (irule abi_scratch_decoder_word >> qexists_tac `clamp` >> asm_simp_tac bool_ss []) >>
  irule abi_scratch_decoder_bytestring >> qexists_tac `n` >> asm_simp_tac (srw_ss()) []
QED

Theorem abi_scratch_decoder_flag:
  abi_scratch_decoder ce env sf (FlagT nsid) tv
Proof
  irule abi_scratch_decoder_word >> simp[type_to_abi_dec_info_def]
QED

(* ===== Inputs ===== *)

(* Actual source validity supplies the emitted aggregate head-window guard. *)

Theorem abi_scratch_decoder_complex_guard_inputs:
  abi_decoder_members ce env sf tys tvs avs vs /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
  abi_scratch_decoder_ranges opc hi src dst sb
    (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) tys)) first last b cap initial ==>
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
  qpat_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_ranges_def]) >>
  asm_simp_tac bool_ss [] >> Cases_on `hi = Lit 0w` >- simp[] >>
  qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `eval_operand hi initial = SOME (n2w hb)` >>
  qexists_tac `hb` >> asm_simp_tac bool_ss [] >> decide_tac
QED

(* ===== Execute ===== *)

(* Execute a DecComplex guard and its actual noncanonical member slices.
   TOP-LEVEL: abi_scratch_decoder_complex_execute. *)

Theorem abi_scratch_decoder_complex_execute:
  LIST_REL (abi_scratch_decoder ce env sf) tys tvs /\
  compile_abi_decode_to_buf dst src opc hi (DecComplex dyn (abi_decoder_member_infos sf ce tys))
    st = ((),final) /\ fn_has_code st final func /\
  (st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_members ce env sf tys tvs
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs bs) vs /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
  abi_scratch_decoder_ranges opc hi src dst sb
    (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) tys)) first last b cap initial /\
  mem_bytes_at sb (LENGTH bs)
    (abi_decode_source opc initial) = bs /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. tuple_in_memory vs tvs d actual.vs_memory /\
    abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
      d (SUM (MAP (type_memory_bytes ce) tys)) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_complex_guard_inputs >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_complex_trace >> strip_tac >>
  rename1 `abi_decode_complex_head_guard src hi _ st = ((),middle)` >>
  drule_all abi_decoder_complex_code >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var /\ first <= middle.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`st'` |-> `middle`, `head_sz` |->
    `FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys)`]
    abi_decode_complex_head_guard_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`,
    `new_next` |-> `middle.cs_next_var`, `len` |-> `LENGTH (bs:word8 list)`,
    `sz` |-> `SUM (MAP (type_memory_bytes ce) tys)`, `hi_op` |-> `hi:operand`]
    abi_scratch_decoder_address_observations) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_scratch_decoder_members_list >> strip_tac >>
  mp_tac (SIMP_RULE bool_ss [MAP, SUM, APPEND, ADD_CLAUSES]
    (Q.INST [`st` |-> `middle`, `initial` |-> `prepared:venom_state`,
      `pretys` |-> `[]`]
      abi_scratch_decoder_members_run)) >>
  impl_tac >- asm_simp_tac (srw_ss()) [Once abi_decoder_members_def, Excl "enc_def"] >>
  strip_tac >> rename1 `tuple_in_memory vs tvs d actual.vs_memory` >>
  `abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
    d (SUM (MAP (type_memory_bytes ce) tys)) b cap initial actual` by
    (irule abi_scratch_effect_after_address >>
     qexistsl_tac [`d`, `final.cs_next_id`, `middle.cs_next_id`,
       `middle.cs_next_var`, `SUM (MAP (type_memory_bytes ce) tys)`, `prepared`] >>
     asm_simp_tac arith_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

(* ===== Inputs ===== *)

(* Recover tuple metadata from the actual valid source bytes. *)

Theorem abi_scratch_decoder_tuple_inputs:
  abi_scratch_decoder_input ce env sf (TupleT tys) (TupleTV tvs) bs v
    st src dst opc hi sb d first last b cap initial ==>
  ?vs. v = ArrayV (TupleV vs) /\
    abi_decoder_members ce env sf tys tvs
      (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs bs) vs /\
    vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
    type_memory_bytes ce (TupleT tys) = SUM (MAP (type_memory_bytes ce) tys) /\
    abi_scratch_decoder_ranges opc hi src dst sb (LENGTH bs)
      d (SUM (MAP (type_memory_bytes ce) tys)) first last b cap initial /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var hi
Proof
  simp_tac bool_ss [abi_scratch_decoder_input_def] >>
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

(* ===== Scratch Decoder Tuple ===== *)

(* Tuple decoding follows arbitrary source-valid member offsets and payloads. *)

Theorem abi_scratch_decoder_tuple:
  LIST_REL (abi_scratch_decoder ce env sf) tys tvs ==>
  abi_scratch_decoder ce env sf (TupleT tys) (TupleTV tvs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [abi_scratch_decoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_decoder_tuple_inputs >> strip_tac >>
  gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_tuple_infos]) >>
  mp_tac (Q.INST [`st` |-> `start`, `final` |-> `end_st`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields) tys`] abi_scratch_decoder_complex_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  asm_simp_tac bool_ss [val_in_memory_tuple]
QED

Theorem abi_scratch_decoder_base_tuple:
  !bts. abi_scratch_decoder ce env sf
    (TupleT (MAP BaseT bts)) (TupleTV (MAP BaseTV bts))
Proof
  gen_tac >>
  `LIST_REL (abi_scratch_decoder ce env sf) (MAP BaseT bts) (MAP BaseTV bts)` by
    (Induct_on `bts` >> simp[abi_scratch_decoder_base]) >>
  `EVERY (\ty. is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) (MAP BaseT bts)` by
    (simp_tac bool_ss [EVERY_MAP, EVERY_MEM, combinTheory.o_DEF] >>
     qx_gen_tac `bt` >> strip_tac >>
     MATCH_ACCEPT_TAC (Q.SPEC `bt` abi_decoder_valid_base_member_nonempty)) >>
  irule abi_scratch_decoder_tuple >> asm_simp_tac bool_ss []
QED
