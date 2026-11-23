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
  fragGasOriginPtr

val CshiftModeWithFmp = ``\checked ty tv.
 !dst src st st' ctx func site initial limit_st sb d D N ids av v root_di
  G tn b sz Ddead lo PG.
 compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
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
 allocas_from lo initial /\ (ctx_has_dalloca ctx ==> allocas_below_fmp initial /\
   initial.vs_alloca_next + pending_alloca_size func initial <= w2n initial.vs_initial_fmp) /\
 lo <= initial.vs_alloca_next /\ lo <= d /\
 (checked ==> sb + LENGTH (enc (vyper_to_abi_type env ty) av) <=
   LENGTH initial.vs_data_section /\ alloca_history func initial) ==>
 ?actual H qt B.
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 (ctx_has_dalloca ctx ==> allocas_below_fmp actual /\
   actual.vs_alloca_next + pending_alloca_size func actual <= w2n actual.vs_initial_fmp) /\
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
 (frame_fmp ==> actual.vs_fmp = initial.vs_fmp) /\
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
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial) /\
 (checked ==> !D explicit. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (initial, G, tn) [] (OK actual, H, qt)) /\
 (checked ==> gas_path_mem ctx func initial 0 (OK actual) /\ alloca_history func actual)``;

Theorem prefix_base_complete_mode_fmp[local]:
  (^CshiftModeWithFmp) checked (BaseT bt) (BaseTV bt)
Proof
  `(?clamp. type_to_abi_dec_info sf ce (BaseT bt) = DecPrimWord clamp) \/
   (?n. type_to_abi_dec_info sf ce (BaseT bt) = DecBytestring n)` by
    (Cases_on `bt` >> simp[type_to_abi_dec_info_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >> simp[type_to_abi_dec_info_def])
  >> BETA_TAC
  >- (match_mp_tac (BETA_RULE prefix_scalar_complete_mode_contract_fmp) >>
      goal_assum (drule_at Any)) >>
  match_mp_tac (BETA_RULE prefix_bytestring_complete_mode_contract_fmp) >>
  goal_assum (drule_at Any)
QED

Theorem prefix_flag_complete_mode_fmp[local]:
  (^CshiftModeWithFmp) checked (FlagT nsid) (FlagTV n)
Proof
  BETA_TAC >> mp_tac (BETA_RULE (Q.INST [`ty` |-> `FlagT nsid`, `tv` |-> `FlagTV n`,
    `clamp` |-> `if ce.ce_flag_n_members (nsid_to_string nsid) = 256 then NoClamp
                else IntClamp (ce.ce_flag_n_members (nsid_to_string nsid)) F`]
    prefix_scalar_complete_mode_contract_fmp)) >>
  (impl_tac >- simp[Once type_to_abi_dec_info_def]) >>
  disch_then ACCEPT_TAC
QED

Theorem prefix_dynamic_complete_mode_fmp[local]:
  (^CshiftModeWithFmp) checked ty tv ==>
  (^CshiftModeWithFmp) checked (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  BETA_TAC >> strip_tac >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- (match_mp_tac (BETA_RULE prefix_dynamic_array_loop_complete_mode_contract_fmp) >> asm_rewrite_tac[]) >>
  match_mp_tac (BETA_RULE prefix_bulk_complete_mode_contract_fmp) >> asm_rewrite_tac[]
QED

Theorem prefix_array_complete_mode_fmp[local]:
  (^CshiftModeWithFmp) checked ty tv ==> (^CshiftModeWithFmp) checked (ArrayT ty bd) (ArrayTV tv bd)
Proof
  BETA_TAC >> Cases_on `bd`
  >- MATCH_ACCEPT_TAC (BETA_RULE prefix_fixed_array_complete_mode_contract_fmp) >>
  MATCH_ACCEPT_TAC (BETA_RULE prefix_dynamic_complete_mode_fmp)
QED

Theorem prefix_canonical_coherent_complete_mode_fmp:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> (^CshiftModeWithFmp) checked ty tv
Proof
  qabbrev_tac `P = \ce env sf. (^CshiftModeWithFmp) checked` >>
  `!ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> P ce env sf ty tv` suffices_by
    simp_tac bool_ss [Abbr `P`] >>
  ho_match_mp_tac abi_decoder_coherent_ind >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >> simp_tac bool_ss [Abbr `P`] >>
      MATCH_ACCEPT_TAC (BETA_RULE prefix_base_complete_mode_fmp)) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >> simp_tac bool_ss [Abbr `P`] >>
      MATCH_ACCEPT_TAC (BETA_RULE prefix_flag_complete_mode_fmp)) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> unabbrev_all_tac >> BETA_TAC >> rule_assum_tac BETA_RULE >>
      match_mp_tac (BETA_RULE prefix_array_complete_mode_fmp) >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> unabbrev_all_tac >> BETA_TAC >> rule_assum_tac BETA_RULE >>
      match_mp_tac (BETA_RULE prefix_tuple_complete_mode_contract_fmp) >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> unabbrev_all_tac >> BETA_TAC >> rule_assum_tac BETA_RULE >>
  match_mp_tac (BETA_RULE prefix_struct_complete_mode_contract_fmp) >> asm_rewrite_tac[]
QED

val CshiftMode = rhs (concl (PURE_REWRITE_CONV [tautLib.TAUT `((F ==> p) /\ q) <=> q`]
  (subst [``frame_fmp:bool`` |-> ``F``] CshiftModeWithFmp)));
val CshiftCode = rhs (concl (SIMP_CONV bool_ss [] ``(^CshiftMode) F``));
val CshiftChecked = ``(^CshiftMode) T``;

Theorem prefix_canonical_coherent_complete_code:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> (^CshiftCode) ty tv
Proof
  mp_tac (Q.INST [`frame_fmp` |-> `F`, `checked` |-> `F`]
    prefix_canonical_coherent_complete_mode_fmp) >>
  simp_tac bool_ss []
QED

Theorem prefix_canonical_coherent_complete_checked:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> (^CshiftChecked) ty tv
Proof
  mp_tac (Q.INST [`frame_fmp` |-> `F`, `checked` |-> `T`]
    prefix_canonical_coherent_complete_mode_fmp) >>
  simp_tac bool_ss []
QED
