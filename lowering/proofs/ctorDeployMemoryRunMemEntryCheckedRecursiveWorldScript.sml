Theory ctorDeployMemoryRunMemEntryCheckedRecursiveWorld
Ancestors
 ctorDeployMemoryRunMemEntryArrayFiniteWorld
 ctorDeployMemoryRunMemEntryCheckedComplexWorld
 ctorDeployMemoryRunMemEntryCheckedBaseWorld
 abiDecoderCoherence exprLowering compileEnv rich_list

val Ckw = ``\ty tv.
 !k dst src hi st st' ctx func site initial limit_st sb d D N ids av v root_di.
 compile_abi_decode_to_buf dst src DLOAD hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= LENGTH initial.vs_data_section /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\ sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
 (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\ k + unit_alloca_budget ctx < dimword (:256) /\
 alloca_history func initial /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st')) [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\
 gas_path_mem ctx func initial 0 (OK actual) /\ actual.vs_gas_readings = initial.vs_gas_readings /\
 alloca_history func actual /\
 actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx /\
 actual.vs_outcomes = initial.vs_outcomes``;

Theorem ctor_checked_coherent_world_run_from:
 !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> (^Ckw) ty tv
Proof
 qabbrev_tac `P = \ce env sf. (^Ckw)` >>
 `!ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> P ce env sf ty tv` suffices_by
   simp[Abbr `P`] >>
 ho_match_mp_tac abi_decoder_coherent_ind >>
 conj_tac
 >- (rpt gen_tac >> disch_tac >> simp_tac bool_ss [Abbr `P`] >>
     MATCH_ACCEPT_TAC (BETA_RULE ctor_checked_base_world_run_from)) >>
 conj_tac
 >- (rpt gen_tac >> disch_tac >> simp_tac bool_ss [Abbr `P`] >>
     MATCH_ACCEPT_TAC (BETA_RULE ctor_checked_flag_world_run_from)) >>
 conj_tac
 >- (rpt gen_tac >> strip_tac >> FULL_SIMP_TAC bool_ss [Abbr `P`] >>
     match_mp_tac (BETA_RULE ctor_checked_array_world_run_from) >> first_assum ACCEPT_TAC) >>
 conj_tac
 >- (rpt gen_tac >> strip_tac >> FULL_SIMP_TAC bool_ss [Abbr `P`] >>
     match_mp_tac (BETA_RULE ctor_checked_tuple_world_run_from) >> first_assum ACCEPT_TAC) >>
 rpt gen_tac >> strip_tac >> FULL_SIMP_TAC bool_ss [Abbr `P`] >>
 match_mp_tac (BETA_RULE ctor_checked_struct_world_run_from) >> asm_rewrite_tac[]
QED
