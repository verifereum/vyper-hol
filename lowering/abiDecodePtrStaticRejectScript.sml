Theory abiDecodePtrStaticReject
Ancestors
  abiDecodePtrConversionReject abiDecodePtrScalarRejectFacts
  abiDecodePtrPhysicalFlatRun abiDecodePtrRejectPrefix abiDecodePtrRejectSource
  abiDecodePtrRejectChecks abiDecodePtrRejectCapacity abiDecodePtrRejectCode
  abiDecodePtrFlatLayout abiDecodePtrMemberInterface
  abiDecodePtrWord abiDecoderBytesBound abiDecoderClamp entryDecodeProps
  abiDecoderMemberInfos abiDecoderCoherence abiDecoderComplexGuard
  abiDecoderComplexHead abiDecoderComplexExecute abiDecoderRange abiDecoderContract
  abiDecoderVarSequence abiDecoderReentryPointer abiDecoderMembers abiDecodeRanges abiValidMembers vyperTypeABI supportedTypes
  vyperABI contractABI compileEnv abiEncoder exprLowering emitHelperProps
  exprLoweringProps venomState venomExecSemantics words list rich_list arithmetic pair

Theorem abi_decode_static_scalar_word:
  supported_scalar_type ty /\ ~is_dynamic (vyper_to_abi_type env ty) ==>
  supported_word_type ty
Proof
  rw[supported_scalar_type_def] >>
  Cases_on `ty` >> gvs[supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[supported_string_type_def, vyper_to_abi_type_def, is_dynamic_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[supported_string_type_def, vyper_to_abi_type_def, is_dynamic_def]
QED

Theorem abi_decode_static_scalar_conversion:
  supported_scalar_type ty /\ ~is_dynamic (vyper_to_abi_type env ty) /\
  vyper_decode_valid_enc (vyper_to_abi_type env ty) bs ==>
  ?v. abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v
Proof
  strip_tac >>
  Cases_on `abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs)` >> simp[] >>
  drule_all abi_decode_scalar_conversion_failure >> strip_tac >>
  gvs[vyper_to_abi_type_def, is_dynamic_def]
QED

Theorem abi_decode_static_members_conversion:
  !tys raw hds.
  EVERY supported_scalar_type tys /\
  EVERY (\ty. ~is_dynamic (vyper_to_abi_type env ty)) tys /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) raw hds ==>
  ?vs. abi_to_vyper_list env tys
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) raw hds) = SOME vs
Proof
  Induct >- simp[abi_decode_members_def] >>
  qx_gen_tac `ty` >> rpt gen_tac >> strip_tac >>
  `vyper_decode_valid_enc (vyper_to_abi_type env ty)
    (abi_decode_member_bytes (vyper_to_abi_type env ty) raw hds) /\
   vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) raw
    (DROP (abi_member_head_size (vyper_to_abi_type env ty)) hds)` by
    (fs[Once vyper_decode_valid_enc_def, abi_decode_member_bytes_def,
        abi_member_head_size_def] >> gvs[]) >>
  `supported_scalar_type ty /\ ~is_dynamic (vyper_to_abi_type env ty)` by fs[] >>
  drule_all abi_decode_static_scalar_conversion >> strip_tac >>
  fs[EVERY_DEF] >> first_x_assum drule_all >> strip_tac >>
  simp[abi_decode_members_def, Once abi_to_vyper_def]
QED

Theorem abi_decode_static_invalid_selection:
  EVERY (\ty. ~is_dynamic (vyper_to_abi_type env ty)) tys /\
  LENGTH tys < dimword(:256) /\
  LENGTH bs <= vyper_abi_size_bound env (TupleT tys) /\
  ~vyper_valid_enc env (TupleT tys) bs ==>
  LENGTH bs < SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) \/
  ?pre ty post.
    tys = pre ++ ty::post /\
    vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) pre) bs bs /\
    ~vyper_decode_valid_enc (vyper_to_abi_type env ty)
      (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
        (DROP (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pre))) bs))
Proof
  strip_tac >> drule_all abi_decode_static_tuple_invalid >>
  strip_tac >- simp[] >> disj2_tac >>
  gvs[MAP_EQ_APPEND, MAP_EQ_CONS] >> metis_tac[]
QED

Theorem abi_decode_complex_head_reject_witness:
  abi_decode_complex_head_guard pos hi head_sz st = ((),last) /\
  hi <> Lit 0w /\ head_sz < dimword(:256) /\ h < head_sz /\
  eval_operand pos s = SOME 0w /\ eval_operand hi s = SOME (n2w h) /\
  fresh_vars_wrt st s ==>
  ?u. abi_decode_reject_witness (emitted_insts st last) s u /\ inst_extends st last
Proof
  simp_tac bool_ss [abi_decode_complex_head_guard_def] >> strip_tac >>
  fs[comp_bind_def] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [pos; Lit (n2w head_sz)] st = (end_op,mid)` >>
  `eval_operand (Lit (n2w head_sz)) s = SOME (n2w head_sz)` by simp[eval_operand_def] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st mid) s = OK reached` >>
  `eval_operand pos reached = SOME 0w /\
   eval_operand hi reached = SOME (n2w h)` by metis_tac[] >>
  `~(w2n (0w:bytes32) <= w2n (n2w head_sz:bytes32) /\
      w2n (n2w head_sz:bytes32) <= w2n (n2w h:bytes32))` by
    (`h < dimword(:256)` by decide_tac >> simp[w2n_n2w]) >>
  drule abi_decode_range_reject_witness >>
  disch_then (qspecl_then [`reached`, `n2w head_sz`, `0w`, `n2w h`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  drule compile_abi_decode_range_check_shape >> strip_tac >>
  `inst_extends st mid` by metis_tac[inst_extends_emit_op] >>
  `inst_extends st last` by metis_tac[inst_extends_trans] >>
  qexists_tac `u` >> simp[] >>
  irule abi_decode_emit_op_reject_chain >>
  goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
  qexists_tac `reached` >> simp[abi_decoder_reentry_opcode_def]
QED

Theorem abi_decode_word_reject_witness:
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi (DecPrimWord clamp) st = ((),last) /\
  eval_operand (Var src) s = SOME b /\ eval_operand pos s = SOME p /\
  ~abi_clamp_ok clamp (abi_decode_load MLOAD (b+p) s) /\ fresh_vars_wrt st s ==>
  ?u. abi_decode_reject_witness (emitted_insts st last) s u /\ inst_extends st last
Proof
  strip_tac >> drule abi_decode_word_phases >> strip_tac >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK reached` >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) reached = OK loaded` >>
  `~abi_clamp_ok clamp (abi_decode_load MLOAD (b+p) reached)` by fs[abi_decode_load_def, mload_def] >>
  drule_all abi_decode_clamp_reject_witness >> strip_tac >>
  drule compile_abi_clamp_structure >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends c2 last /\ inst_extends c1 last /\ inst_extends st last` by
    metis_tac[inst_extends_trans] >>
  `abi_decode_reject_witness (emitted_insts c2 last) loaded u` by
    (irule abi_decode_emit_reject_suffix >> qexists_tac `c3` >> simp[]) >>
  qexists_tac `u` >> reverse conj_tac >- simp[] >>
  irule abi_decode_emit_op_reject_chain >>
  goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
  qexists_tac `reached` >> simp[abi_decoder_reentry_opcode_def] >>
  irule abi_decode_emit_op_reject_chain >>
  goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
  qexists_tac `loaded` >> simp[abi_decoder_reentry_opcode_def]
QED

Theorem abi_decode_selected_word_reject_witness:
  abi_decode_member_code dst pos src hi (DecPrimWord clamp) off q sa sb /\
  eval_operand pos s = SOME p /\ eval_operand (Var src) s = SOME b /\
  eval_operand (Var dst) s = SOME d /\
  ~abi_clamp_ok clamp (abi_decode_load MLOAD (b+(p+n2w off)) s) /\
  fresh_vars_wrt sa s ==>
  ?u. abi_decode_reject_witness (emitted_insts sa sb) s u /\ inst_extends sa sb
Proof
  strip_tac >>
  fs[abi_decode_member_code_def, dec_info_needs_offset_def,
     compile_getelemptr_abi_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK s1` >>
  `eval_operand (Var dst) s1 = SOME d /\
   eval_operand (Lit (n2w q)) s1 = SOME (n2w q)` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  qpat_assum `emit_op ADD [Var dst; _] sm = _` mp_tac >>
  disch_then (mp_then Any mp_tac emit_op_ADD_correct) >>
  disch_then (qspecl_then [`d`, `n2w q`, `s1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sn) s1 = OK s2` >>
  `eval_operand (Var src) s2 = SOME b /\ eval_operand head_ptr s2 = SOME (p+n2w off)` by metis_tac[] >>
  `s2.vs_memory = s1.vs_memory /\ s1.vs_memory = s.vs_memory` by
    (conj_tac >> simp[LIST_EQ_REWRITE] >> metis_tac[]) >>
  `~abi_clamp_ok clamp (abi_decode_load MLOAD (b+(p+n2w off)) s2)` by
    fs[abi_decode_load_def, mload_def] >>
  drule_all abi_decode_word_reject_witness >> strip_tac >>
  `inst_extends sa sm /\ inst_extends sm sn` by metis_tac[inst_extends_emit_op] >>
  `inst_extends sm sb /\ inst_extends sa sb` by metis_tac[inst_extends_trans] >>
  qexists_tac `u` >> reverse conj_tac >- simp[] >>
  irule abi_decode_emit_op_reject_chain >>
  goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
  qexists_tac `s1` >> simp[abi_decoder_reentry_opcode_def] >>
  irule abi_decode_emit_op_reject_chain >>
  goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
  qexists_tac `s2` >> simp[abi_decoder_reentry_opcode_def]
QED

Theorem abi_decode_selected_invalid_word_reject:
  supported_word_type ty /\ type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  ~is_dynamic (vyper_to_abi_type env ty) /\
  abi_decode_member_code dst (Lit 0w) src hi (DecPrimWord clamp) off q sa sb /\
  off+32 <= LENGTH bs /\ B+LENGTH bs < dimword(:256) /\
  ~vyper_decode_valid_enc (vyper_to_abi_type env ty)
    (abi_decode_member_bytes (vyper_to_abi_type env ty) bs (DROP off bs)) /\
  mem_bytes_at B (LENGTH bs) (abi_decode_source MLOAD s) = bs /\
  eval_operand (Var src) s = SOME (n2w B) /\
  eval_operand (Var dst) s = SOME d /\ fresh_vars_wrt sa s ==>
  ?u. abi_decode_reject_witness (emitted_insts sa sb) s u /\ inst_extends sa sb
Proof
  strip_tac >>
  `static_length (vyper_to_abi_type env ty) = 32` by
    (Cases_on `ty` >> fs[supported_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[supported_word_type_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
         static_length_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[supported_word_type_def, vyper_base_to_abi_type_def, static_length_def]) >>
  `mem_bytes_at (B+off) (LENGTH (TAKE 32 (DROP off bs))) (abi_decode_source MLOAD s) = TAKE 32 (DROP off bs)` by
    (drule abiCanonicalHeadSizeTheory.abi_decode_source_window >>
     disch_then (qspecl_then [`off`, `32`] mp_tac) >> simp[LENGTH_TAKE, LENGTH_DROP]) >>
  `32 <= LENGTH (TAKE 32 (DROP off bs)) /\ B+off < dimword(:256)` by
    (simp[LENGTH_TAKE, LENGTH_DROP] >> decide_tac) >>
  `~vyper_decode_valid_enc (vyper_to_abi_type env ty) (TAKE 32 (DROP off bs))` by
    (fs[abi_decode_member_bytes_def] >> gvs[]) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_physical_word_invalid_clamp >> strip_tac >>
  irule abi_decode_selected_word_reject_witness >> simp_tac bool_ss [] >>
  conj_tac >- simp[] >>
  goal_assum (drule_at (Pat `abi_decode_member_code _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`n2w B`, `d`, `0w`] >>
  simp[eval_operand_def, WORD_ADD_0, word_add_n2w]
QED
