(* The complete paired decoder contract for every coherent ABI type: the
 * scalar, empty, bytestring, bulk, dynamic-array loop, tuple, struct and
 * fixed-array cases, by induction on the coherence derivation. *)
Theory ctorDeployMemoryRunPtrPrefixCompleteCoherent
Ancestors
  ctorDeployMemoryRunPtrPrefixCompleteBulk
  ctorDeployMemoryRunPtrPrefixCompleteCopy
  ctorDeployMemoryRunPtrPrefixCompleteAggregates
  ctorDeployMemoryRunPtrPrefixCompleteArrayContract
  ctorDeployMemoryRunPtrPrefixCompleteCode
  exprLowering abiDecoderCoherence

val CshiftCode = ``\ty tv.
 !dst src st st' ctx func site initial limit_st sb d D N ids av v root_di
  G tn b sz Ddead lo PG.
 compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
   (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\
 eval_operand (Var dst) initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
   initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (!x. src = Var x \/ Var dst = Var x \/ Lit 0w = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb.
    lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 FLOOKUP G dst = SOME (b,sz) /\ b <= d /\
 d + type_memory_bytes ce ty <= b+sz /\
 op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
 lo <= initial.vs_alloca_next /\ lo <= d ==>
 ?actual H qt B.
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\ actual.vs_gas_readings = initial.vs_gas_readings /\
 (!a. a < lo ==> read_byte a actual.vs_memory = read_byte a initial.vs_memory) /\
 FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\
 DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
    val_in_memory tv v d mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
                           op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)``;

Theorem prefix_base_complete_code[local]:
  (^CshiftCode) (BaseT bt) (BaseTV bt)
Proof
  `(?clamp. type_to_abi_dec_info sf ce (BaseT bt) = DecPrimWord clamp) \/
   (?n. type_to_abi_dec_info sf ce (BaseT bt) = DecBytestring n)` by
    (Cases_on `bt` >> simp[type_to_abi_dec_info_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >> simp[type_to_abi_dec_info_def])
  >- (irule prefix_scalar_complete_code_contract >> goal_assum (drule_at Any)) >>
  irule prefix_bytestring_complete_code_contract >> goal_assum (drule_at Any)
QED

Theorem prefix_flag_complete_code[local]:
  (^CshiftCode) (FlagT nsid) (FlagTV n)
Proof
  irule prefix_scalar_complete_code_contract >> simp[Once type_to_abi_dec_info_def]
QED

Theorem prefix_dynamic_complete_code[local]:
  (^CshiftCode) ty tv ==>
  (^CshiftCode) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  strip_tac >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- (match_mp_tac prefix_dynamic_array_loop_complete_code_contract >> asm_rewrite_tac[]) >>
  match_mp_tac prefix_bulk_complete_code_contract >> asm_rewrite_tac[]
QED

Theorem prefix_array_complete_code[local]:
  (^CshiftCode) ty tv ==> (^CshiftCode) (ArrayT ty bd) (ArrayTV tv bd)
Proof
  Cases_on `bd`
  >- MATCH_ACCEPT_TAC prefix_fixed_array_complete_code_contract >>
  MATCH_ACCEPT_TAC prefix_dynamic_complete_code
QED

Theorem prefix_canonical_coherent_complete_code:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> (^CshiftCode) ty tv
Proof
  qabbrev_tac `P = \ce env sf. (^CshiftCode)` >>
  `!ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> P ce env sf ty tv` suffices_by
    simp[Abbr `P`] >>
  ho_match_mp_tac abi_decoder_coherent_ind >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >> simp_tac bool_ss [Abbr `P`] >>
      MATCH_ACCEPT_TAC (BETA_RULE prefix_base_complete_code)) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >> simp_tac bool_ss [Abbr `P`] >>
      MATCH_ACCEPT_TAC (BETA_RULE prefix_flag_complete_code)) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> unabbrev_all_tac >> BETA_TAC >> rule_assum_tac BETA_RULE >>
      match_mp_tac (BETA_RULE prefix_array_complete_code) >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> unabbrev_all_tac >> BETA_TAC >> rule_assum_tac BETA_RULE >>
      match_mp_tac (BETA_RULE prefix_tuple_complete_code_contract) >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> unabbrev_all_tac >> BETA_TAC >> rule_assum_tac BETA_RULE >>
  match_mp_tac (BETA_RULE prefix_struct_complete_code_contract) >> asm_rewrite_tac[]
QED
