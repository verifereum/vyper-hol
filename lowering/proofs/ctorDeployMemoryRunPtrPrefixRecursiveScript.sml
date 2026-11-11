(* Coherence assembly for same-witness floor-aware canonical decoding. *)
Theory ctorDeployMemoryRunPtrPrefixRecursive
Ancestors
  ctorDeployMemoryRunPtrPrefixDynamicArray ctorDeployMemoryRunPtrPrefixMembersCons
  ctorDeployMemoryRunPtrPrefixCanonicalFloor abiDecoderCoherence
  abiDecoderFixedInputs abiDecoderFixedMemory abiDecoderMemberInfos
  abiDecoderComplexExecute abiDecoderComplexHead abiDecoderMembers abiCanonicalHeadSize arithmetic
  compileEnv exprLowering rich_list valueEncoding valueEncodingProps vyperABI vyperTypeABI

val canonical_pair_floor = ``\ty tv.
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
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
 unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 FLOOKUP G dst = SOME (b,sz) /\ b <= d /\
 d + type_memory_bytes ce ty <= b+sz /\
 op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\ lo <= initial.vs_alloca_next ==>
 ?actual H qt B.
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\
 FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\ DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
   val_in_memory tv v d mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
   op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)``;

Theorem prefix_paired_fixed_array_floor:
  (^canonical_pair_floor) ty tv ==>
  (^canonical_pair_floor) (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
Proof
  strip_tac >>
  `!k. LIST_REL (^canonical_pair_floor) (REPLICATE k ty)
     (REPLICATE k tv)` by
    (gen_tac >> simp_tac bool_ss [LIST_REL_REPLICATE_same] >>
     BETA_TAC >> strip_tac >> first_assum (ACCEPT_TAC o BETA_RULE)) >>
  BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_fixed_array_values >> strip_tac >>
  gnvs[Once vyper_to_abi_type_def, canonical_array_tuple, Excl "enc_def"] >>
  qpat_assum `LENGTH vs = LENGTH avs`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th]) >> assume_tac th) >>
  `type_memory_bytes ce (ArrayT ty (Fixed (LENGTH vs))) =
     LENGTH vs * type_memory_bytes ce ty` by simp[Once type_memory_bytes_def] >>
  qpat_assum `type_memory_bytes ce (ArrayT ty (Fixed (LENGTH vs))) = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `LIST_REL (^canonical_pair_floor) (REPLICATE (LENGTH vs) ty)
     (REPLICATE (LENGTH vs) tv)` by
    (qpat_x_assum `!k. LIST_REL _ _ _`
       (qspec_then `LENGTH vs` mp_tac) >> simp[]) >>
  drule prefix_paired_members_floor >> disch_then (mk_asm "members") >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_fixed_array_infos]) >>
  drule abi_decoder_complex_trace >> strip_tac >>
  qpat_x_assum `abi_decode_complex_head_guard _ _ _ _ = _`
    (SUBST_ALL_TAC o SYM o SIMP_RULE (srw_ss())
      [abi_decode_complex_head_guard_def, comp_return_def]) >>
  asm_x "members" (mp_tac o SIMP_RULE bool_ss
    [MAP, SUM, APPEND, ADD_CLAUSES, map_replicate, SUM_REPLICATE] o
    Q.INST [`final` |-> `st'`, `pretys` |-> `[]`, `pretvs` |-> `[]`,
      `preavs` |-> `[]`, `prevs` |-> `[]`, `vs'` |-> `vs`] o SPEC_ALL o BETA_RULE) >>
  (impl_tac >- (asm_simp_tac bool_ss [Once abi_decoder_members_def] >>
    gvs[Excl "enc_def"] >> first_assum ACCEPT_TAC)) >>
  strip_tac >> qexistsl_tac [`actual`,`H`,`qt`,`B`] >>
  qpat_x_assum `LENGTH vs = LENGTH avs` (fn th => rewrite_tac[GSYM th]) >>
  asm_simp_tac bool_ss [Once type_memory_bytes_def] >>
  conj_tac >- (irule abi_decoder_fixed_array_memory >> simp[]) >>
  conj_tac >- simp[Once type_memory_bytes_def] >>
  rpt strip_tac >> irule abi_decoder_fixed_array_memory >> simp[]
QED

Theorem prefix_paired_base_floor[local]:
  (^canonical_pair_floor) (BaseT bt) (BaseTV bt)
Proof
  `(?clamp. type_to_abi_dec_info sf ce (BaseT bt) = DecPrimWord clamp) \/
   (?n. type_to_abi_dec_info sf ce (BaseT bt) = DecBytestring n)` by
    (Cases_on `bt` >> simp[type_to_abi_dec_info_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >> simp[type_to_abi_dec_info_def])
  >- (irule prefix_canonical_primitive_paired_floor >> goal_assum (drule_at Any)) >>
  irule prefix_canonical_bytestring_paired_floor >> goal_assum (drule_at Any)
QED

Theorem prefix_paired_flag_floor[local]:
  (^canonical_pair_floor) (FlagT nsid) (FlagTV n)
Proof
  irule prefix_canonical_primitive_paired_floor >> simp[Once type_to_abi_dec_info_def]
QED

Theorem prefix_paired_dynamic_floor[local]:
  (^canonical_pair_floor) ty tv ==>
  (^canonical_pair_floor) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  strip_tac >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- (match_mp_tac prefix_dynamic_array_loop_paired_floor >> asm_rewrite_tac[]) >>
  match_mp_tac prefix_canonical_bulk_paired_floor >> asm_rewrite_tac[]
QED

Theorem prefix_paired_array_floor[local]:
  (^canonical_pair_floor) ty tv ==> (^canonical_pair_floor) (ArrayT ty bd) (ArrayTV tv bd)
Proof
  Cases_on `bd`
  >- MATCH_ACCEPT_TAC prefix_paired_fixed_array_floor >>
  MATCH_ACCEPT_TAC prefix_paired_dynamic_floor
QED

Theorem prefix_canonical_coherent_paired_floor:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> (^canonical_pair_floor) ty tv
Proof
  qabbrev_tac `P = \ce env sf. (^canonical_pair_floor)` >>
  `!ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> P ce env sf ty tv` suffices_by
    simp[Abbr `P`] >>
  ho_match_mp_tac abi_decoder_coherent_ind >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >> simp_tac bool_ss [Abbr `P`] >>
      MATCH_ACCEPT_TAC (BETA_RULE prefix_paired_base_floor)) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >> simp_tac bool_ss [Abbr `P`] >>
      MATCH_ACCEPT_TAC (BETA_RULE prefix_paired_flag_floor)) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> FULL_SIMP_TAC bool_ss [Abbr `P`] >>
      match_mp_tac (BETA_RULE prefix_paired_array_floor) >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> FULL_SIMP_TAC bool_ss [Abbr `P`] >>
      match_mp_tac (BETA_RULE prefix_paired_tuple_floor) >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> FULL_SIMP_TAC bool_ss [Abbr `P`] >>
  match_mp_tac (BETA_RULE prefix_paired_struct_floor) >> asm_rewrite_tac[]
QED

val _ = export_theory();
