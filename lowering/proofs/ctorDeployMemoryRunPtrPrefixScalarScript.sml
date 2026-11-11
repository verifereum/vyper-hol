(* Canonical checked scalar consumers share the successful scalar endpoint. *)
Theory ctorDeployMemoryRunPtrPrefixScalar
Ancestors
  ctorDeployMemoryRunPtrPrefixScalarClamps ctorDeployMemoryRunPtrPrefixScalarPackage
  ctorDeployMemoryRunPtrPrefixCanonical ctorDeployMemoryRunPtrPrefixScalarBool
  abiEncoder abiDecoderContract abiDecoderClampedWord compileEnv exprLoweringProps
  venomState venomInst venomExecSemantics ptrDiscipline ptrSafeRun
  fragExec finite_map list rich_list words pred_set allocaFrontierBound

val canonical_pair = ``\ty tv.
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
 allocas_from lo initial /\ ~ctx_has_dalloca ctx ==>
 ?actual H qt B.
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
    lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\
 FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\
 DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem =
                        mem_bytes_at a 1 actual.vs_memory) ==>
    val_in_memory tv v d mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
                           op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)``;

Theorem prefix_canonical_int_paired:
  type_to_abi_dec_info sf ce ty = DecPrimWord (IntClamp bits signed) ==>
  (^canonical_pair) ty tv
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  drule_all prefix_scalar_prepare >> strip_tac >>
  `d < dimword (:256)` by
    (drule_all alloca_frontier_inv_bound >> decide_tac) >>
  `compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
    (DecPrimWord (IntClamp bits signed)) st = ((),st')` by metis_tac[] >>
  `d+32 <= b+sz` by metis_tac[] >>
  `!v. src = Var v \/ dst = v ==> not_fresh_at st v` by metis_tac[] >>
  drule_all (SRULE [] (Q.INST
    [`left` |-> `F`, `n` |-> `(n2w (if signed then bits DIV 8-1 else bits)):bytes32`,
     `clamp` |-> `IntClamp bits signed`, `m` |-> `0`]
    (SPEC_ALL prefix_scalar_checked_ghost))) >>
  disch_then (qspecl_then [`PG`,`Ddead`] strip_assume_tac) >>
  qabbrev_tac `actual = t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  rule_assum_tac (PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all prefix_scalar_transport >> strip_tac >>
  drule_all prefix_scalar_support_package >> strip_tac >>
  qexistsl [`actual`,`H`,`qt`,`range_bytes [(d,32)]`] >>
  asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  simp[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]
QED

Theorem prefix_canonical_bytes_paired:
  type_to_abi_dec_info sf ce ty = DecPrimWord (BytesMClamp m) ==>
  (^canonical_pair) ty tv
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  drule_all prefix_scalar_prepare >> strip_tac >>
  `d < dimword (:256)` by
    (drule_all alloca_frontier_inv_bound >> decide_tac) >>
  `compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
    (DecPrimWord (BytesMClamp m)) st = ((),st')` by metis_tac[] >>
  `d+32 <= b+sz` by metis_tac[] >>
  `!v. src = Var v \/ dst = v ==> not_fresh_at st v` by metis_tac[] >>
  drule_all (SRULE [] (Q.INST
    [`left` |-> `T`, `signed` |-> `F`, `n` |-> `(n2w (m*8)):bytes32`,
     `clamp` |-> `BytesMClamp m`, `bits` |-> `0`]
    (SPEC_ALL prefix_scalar_checked_ghost))) >>
  disch_then (qspecl_then [`PG`,`Ddead`] strip_assume_tac) >>
  qabbrev_tac `actual = t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  rule_assum_tac (PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all prefix_scalar_transport >> strip_tac >>
  drule_all prefix_scalar_support_package >> strip_tac >>
  qexistsl [`actual`,`H`,`qt`,`range_bytes [(d,32)]`] >>
  asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  simp[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]
QED

Theorem prefix_canonical_primitive_paired:
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
  (^canonical_pair) ty tv
Proof
  Cases_on `clamp` >> strip_tac
  >- (match_mp_tac prefix_canonical_noclamp_paired >> simp[])
  >- (irule prefix_canonical_int_paired >> goal_assum drule)
  >- (irule prefix_canonical_bytes_paired >> goal_assum drule)
  >> match_mp_tac prefix_canonical_bool_paired >> simp[]
QED

val _ = export_theory();
