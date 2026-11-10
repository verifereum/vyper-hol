Theory abiDecodePtrConversionReject
Ancestors
  abiDecodePtrRejectSource abiDecodePtrRejectPrefix abiDecodePtrRejectValidMember
  abiDecodePtrRejectChecks abiDecodePtrRejectCapacity abiDecodePtrRejectCode
  abiDecodePtrFlatLayout abiDecodePtrMemberInterface abiDecoderCoherence
  abiDecoderMemberInfos abiValidMember abiValidMembers abiDecoderContract
  abiDecoderComplexHead abiDecodePtrComplexHeader abiDecoderReentryPointer abiDecoderReentry
  abiDecoderAppend abiDecoderRange abiEncoder emitHelperProps exprLoweringProps
  supportedTypes vyperABI contractABI compileEnv exprLowering venomState
  venomExecSemantics words list rich_list arithmetic pair

Theorem abi_decode_flat_conversion_reject:
  EVERY supported_scalar_type tys /\
  LIST_REL (abi_decoder_coherent ce env ce.ce_struct_fields) tys tvs /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
  abi_to_vyper_list env tys
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs bs) = NONE /\
  compile_abi_decode_complex_elems (Var dst) (Lit 0w) MLOAD (Var src) hi
    (abi_decoder_member_infos ce.ce_struct_fields ce tys) 0 0 st = ((),last) /\
  mem_bytes_at B (LENGTH bs) (abi_decode_source MLOAD s) = bs /\
  B+LENGTH bs < dimword(:256) /\
  d+SUM (MAP (type_memory_bytes ce) tys) < dimword(:256) /\
  (B+LENGTH bs <= d \/ d+SUM (MAP (type_memory_bytes ce) tys) <= B) /\
  eval_operand (Var src) s = SOME (n2w B) /\
  eval_operand (Var dst) s = SOME (n2w d) /\
  eval_operand hi s = SOME (n2w (LENGTH bs)) /\ hi <> Lit 0w /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  abi_decoder_operand_live st.cs_next_var (Var src) /\
  abi_decoder_operand_live st.cs_next_var hi /\ fresh_vars_wrt st s ==>
  ?u. abi_decode_reject_witness (emitted_insts st last) s u
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decode_first_conversion_failure >> strip_tac >>
  qpat_x_assum `tys = _` SUBST_ALL_TAC >>
  `?sm sn reached.
    compile_abi_decode_complex_elems (Var dst) (Lit 0w) MLOAD (Var src) hi
      (abi_decoder_member_infos ce.ce_struct_fields ce pre) 0 0 st = ((),sm) /\
    abi_decode_member_code dst (Lit 0w) src hi (type_to_abi_dec_info ce.ce_struct_fields ce ty)
      (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pre)))
      (SUM (MAP (type_memory_bytes ce) pre)) sm sn /\
    compile_abi_decode_complex_elems (Var dst) (Lit 0w) MLOAD (Var src) hi
      (abi_decoder_member_infos ce.ce_struct_fields ce post)
      (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pre)) +
        abi_embedded_static_size ce.ce_struct_fields ty)
      (SUM (MAP (type_memory_bytes ce) pre) + type_memory_bytes ce ty) sn = ((),last) /\
    run_inst_seq (emitted_insts st sm) s = OK reached /\ inst_extends st sm /\
    fresh_vars_wrt sm reached /\
    mem_bytes_at B (LENGTH bs) (abi_decode_source MLOAD reached) = bs /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op reached = SOME w)` by suspend "prefix" >>
  `?u. abi_decode_reject_witness (emitted_insts sm sn) reached u` by suspend "selected" >>
  `abi_decode_flat_layout (abi_decoder_member_infos ce.ce_struct_fields ce (pre ++ ty::post))
    0 0 0w (LENGTH bs) (SUM (MAP (type_memory_bytes ce) (pre ++ ty::post)))` by suspend "layout" >>
  `inst_extends st last /\
   EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st last)` by
    metis_tac[abi_decode_flat_compile_shape, abi_decode_flat_reentry_code] >>
  suspend "chain"
QED

Resume abi_decode_flat_conversion_reject[prefix]:
  markerLib.RESUME_TAC >>
  `LIST_REL (abi_decoder_coherent ce env ce.ce_struct_fields) pre
    (TAKE (LENGTH pre) tvs)` by
    (drule LIST_REL_TAKE >> disch_then (qspec_then `LENGTH pre` mp_tac) >> simp[TAKE_LENGTH_APPEND]) >>
  `eval_operand (Lit 0w) s = SOME (n2w 0 : bytes32) /\
   abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    simp[eval_operand_def, abi_decoder_operand_live_def] >>
  `EVERY supported_scalar_type pre` by fs[EVERY_APPEND] >>
  `d+SUM (MAP (type_memory_bytes ce) pre) < dimword(:256)` by
    (fs[MAP_APPEND, SUM_APPEND] >> decide_tac) >>
  SUBGOAL_THEN ``B+LENGTH (bs:word8 list) <= d \/
    d+SUM (MAP (type_memory_bytes ce) pre) <= B`` assume_tac
  >- (fs[MAP_APPEND, SUM_APPEND] >> decide_tac) >>
  SUBGOAL_THEN ``hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    LENGTH (bs:word8 list) <= h /\ h < dimword(:256)`` assume_tac
  >- (disj2_tac >> qexists_tac `LENGTH bs` >> simp[] >> decide_tac) >>
  drule_all (SIMP_RULE bool_ss [ADD_CLAUSES] (Q.INST [`z` |-> `0`] abi_decode_selected_prefix_run)) >>
  strip_tac >> qexistsl_tac [`sm`, `sn`, `reached`] >> asm_simp_tac bool_ss []
QED

Resume abi_decode_flat_conversion_reject[selected]:
  markerLib.RESUME_TAC >>
  `supported_scalar_type ty` by fs[EVERY_APPEND] >>
  `vyper_decode_valid_enc_tuple
    (MAP (vyper_to_abi_type env) pre ++ vyper_to_abi_type env ty ::
      MAP (vyper_to_abi_type env) post) bs bs` by fs[MAP_APPEND] >>
  drule abi_valid_member_head >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_decode_scalar_conversion_failure >> strip_tac >>
  `n < dimword(:256)` by
    (qspec_then `n` assume_tac
       (REWRITE_RULE [contractABITheory.ceil32_def]
         (GEN_ALL contractABITheory.le_ceil32)) >>
     Cases_on `ty = BaseT (StringT n)` >>
     gvs[type_memory_bytes_def, MAP_APPEND, SUM_APPEND,
         Excl "dec_def"] >> decide_tac) >>
  `eval_operand (Var src) reached = SOME (n2w B) /\
   eval_operand (Var dst) reached = SOME (n2w d) /\
   eval_operand hi reached = SOME (n2w (LENGTH bs))` by metis_tac[] >>
  metis_tac[abi_decode_selected_valid_bytes_reject]
QED
Resume abi_decode_flat_conversion_reject[layout]:
  markerLib.RESUME_TAC >>
  qmatch_goalsub_abbrev_tac `abi_decoder_member_infos _ _ tys` >>
  `EVERY supported_scalar_type tys /\
   LIST_REL (abi_decoder_coherent ce env ce.ce_struct_fields) tys tvs /\
   vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
   d + SUM (MAP (type_memory_bytes ce) tys) < dimword(:256)` by simp[Abbr `tys`] >>
  `!ty. MEM ty tys ==> abi_member_head_size (vyper_to_abi_type env ty) = 32` by
    (qx_gen_tac `ety` >> strip_tac >>
     `supported_scalar_type ety` by metis_tac[EVERY_MEM] >>
     `type_memory_bytes ce ety <= SUM (MAP (type_memory_bytes ce) tys)` by
       metis_tac[SUM_MAP_MEM_bound] >>
     `abi_embedded_static_size ce.ce_struct_fields ety = 32` by
       (irule (cj 2 abi_decode_supported_member_layout) >>
        conj_tac >- simp[] >> conj_tac
        >- (qexistsl_tac [`SUM (MAP (type_memory_bytes ce) tys)`, `0`] >> simp[] >> decide_tac) >>
        qexistsl_tac [`32`, `0`, `0w`] >> simp[]) >>
     drule_all LIST_REL_MEM_IMP >> strip_tac >>
     drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  `SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) = 32 * LENGTH tys` by
    (qpat_x_assum `!ty. MEM ty tys ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Induct_on `tys` >> simp[DISJ_IMP_THM, FORALL_AND_THM, MULT_SUC]) >>
  drule abi_valid_members_view >> strip_tac >>
  irule abi_decode_supported_flat_layout >> simp[] >> decide_tac
QED
Resume abi_decode_flat_conversion_reject[chain]:
  markerLib.RESUME_TAC >>
  `MAP (abi_embedded_static_size ce.ce_struct_fields) pre =
   MAP abi_member_head_size (MAP (vyper_to_abi_type env) pre)` by
    (simp_tac bool_ss [MAP_MAP_o] >> irule MAP_CONG >> simp_tac bool_ss [] >>
     rpt strip_tac >>
     `LIST_REL (abi_decoder_coherent ce env ce.ce_struct_fields) pre (TAKE (LENGTH pre) tvs)` by
       (drule LIST_REL_TAKE >> disch_then (qspec_then `LENGTH pre` mp_tac) >> simp[TAKE_LENGTH_APPEND]) >>
     drule_all LIST_REL_MEM_IMP >> strip_tac >>
     drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  `!xs ys off q z h cap.
    abi_decode_flat_layout (xs ++ ys) off q z h cap ==>
    abi_decode_flat_layout ys (off + SUM (MAP (FST o SND) xs))
      (q + SUM (MAP (SND o SND) xs)) z h cap` by
    (POP_ASSUM_LIST (K ALL_TAC) >> Induct >> simp[] >>
     qx_gen_tac `entry` >> PairCases_on `entry` >>
     simp_tac bool_ss [Once abi_decode_flat_layout_def, FST, SND] >>
     rpt strip_tac >> first_x_assum drule >>
     simp_tac bool_ss [ADD_ASSOC]) >>
  `abi_decode_flat_layout (abi_decoder_member_infos ce.ce_struct_fields ce post)
      (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pre)) +
        abi_embedded_static_size ce.ce_struct_fields ty)
      (SUM (MAP (type_memory_bytes ce) pre) + type_memory_bytes ce ty)
      0w (LENGTH bs) (SUM (MAP (type_memory_bytes ce) (pre ++ ty::post)))` by
    (first_x_assum (qspecl_then [`abi_decoder_member_infos ce.ce_struct_fields ce (pre ++ [ty])`,
      `abi_decoder_member_infos ce.ce_struct_fields ce post`, `0`, `0`, `0w`, `LENGTH bs`,
      `SUM (MAP (type_memory_bytes ce) (pre ++ ty::post))`] mp_tac) >>
     asm_simp_tac bool_ss [abi_decoder_member_infos_def, MAP_APPEND, MAP,
       MAP_MAP_o, combinTheory.o_DEF, FST, SND, SUM_APPEND, SUM,
       ADD_CLAUSES, ADD_ASSOC, GSYM APPEND_ASSOC] >>
     simp_tac (bool_ss ++ ETA_ss) [] >>
     asm_simp_tac bool_ss [GSYM MAP_MAP_o] >>
     strip_tac >>
     simp_tac bool_ss [GSYM combinTheory.o_DEF, GSYM MAP_MAP_o, MAP_ID] >>
     first_x_assum irule >>
     qpat_x_assum `abi_decode_flat_layout _ 0 0 _ _ _` mp_tac >>
     simp_tac bool_ss [abi_decoder_member_infos_def, MAP_APPEND, MAP,
       APPEND, SUM_APPEND, SUM, ADD_ASSOC, GSYM APPEND_ASSOC]) >>
  `inst_extends sn last` by metis_tac[abi_decode_flat_compile_shape] >>
  `abi_decode_member_layout (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pre)))
    (SUM (MAP (type_memory_bytes ce) pre)) (type_memory_bytes ce ty)
    0w (LENGTH bs) (SUM (MAP (type_memory_bytes ce) (pre ++ ty::post)))` by
    (qpat_x_assum `!xs ys off q z h cap. _` (qspecl_then
       [`abi_decoder_member_infos ce.ce_struct_fields ce pre`,
        `abi_decoder_member_infos ce.ce_struct_fields ce (ty::post)`,
        `0`, `0`, `0w`, `LENGTH bs`,
        `SUM (MAP (type_memory_bytes ce) (pre ++ ty::post))`] mp_tac) >>
     asm_simp_tac (bool_ss ++ ETA_ss)
       [abi_decoder_member_infos_def, MAP_APPEND, MAP, MAP_MAP_o,
        combinTheory.o_DEF, FST, SND, ADD_CLAUSES] >>
     asm_simp_tac bool_ss [GSYM MAP_MAP_o] >>
     impl_tac
     >- (qpat_x_assum `abi_decode_flat_layout _ 0 0 _ _ _` mp_tac >>
         simp_tac bool_ss [abi_decoder_member_infos_def, MAP_APPEND, MAP]) >>
     simp_tac bool_ss [Once abi_decode_flat_layout_def, FST, SND] >>
     strip_tac >> simp[]) >>
  `inst_extends sm sn` by metis_tac[abi_decode_flat_member_shape] >>
  `abi_decode_reject_witness (emitted_insts sm last) reached u` by
    (drule abi_decode_reject_witness_suffix >>
     disch_then (qspec_then `emitted_insts sn last` mp_tac) >>
     metis_tac[emitted_insts_append, inst_extends_def]) >>
  qexists_tac `u` >> irule abi_decode_emit_reject_chain >>
  qexistsl_tac [`sm`, `reached`] >> simp[] >>
  `inst_extends sm last` by
    (irule inst_extends_trans >> qexists_tac `sn` >> simp[]) >>
  `emitted_insts st last = emitted_insts st sm ++ emitted_insts sm last` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  fs[EVERY_APPEND]
QED
Finalise abi_decode_flat_conversion_reject
