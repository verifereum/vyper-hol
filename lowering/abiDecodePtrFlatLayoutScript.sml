Theory abiDecodePtrFlatLayout
Ancestors
  abiDecodePtrMemberInterface abiDecodePtrSelectedMember
  abiDecoderMemberSetup abiDecoderMemberCons
  abiDecoderMemberInfos abiEncoder emitHelperProps exprLoweringProps
  compileEnv venomInst words arithmetic list pair fragExec abiDecoderAppend
  abiDecoderContract exprSimAccounts supportedTypes exprLowering contractABI

Definition abi_decode_flat_layout_def:
  (abi_decode_flat_layout [] off q z h cap <=> q <= cap) /\
  (abi_decode_flat_layout ((ei,asz,msz)::rest) off q z h cap <=>
    abi_decode_member_layout ei off q msz z h cap /\
    abi_decode_flat_layout rest (off+asz) (q+msz) z h cap)
End

Theorem abi_decode_flat_layout_capacity:
  !elems off q z h cap.
    abi_decode_flat_layout elems off q z h cap ==>
    q + SUM (MAP (SND o SND) elems) <= cap
Proof
  Induct >> simp[abi_decode_flat_layout_def] >>
  qx_gen_tac `entry` >> PairCases_on `entry` >> rpt strip_tac >>
  fs[abi_decode_flat_layout_def] >> first_x_assum drule >> simp[]
QED

Theorem abi_decode_flat_compile_cons:
  compile_abi_decode_complex_elems (Var dst) pos MLOAD (Var src) hi
    ((ei,asz,msz)::rest) off q sa = ((),sb) ==>
  ?sm. abi_decode_member_code dst pos src hi ei off q sa sm /\
    compile_abi_decode_complex_elems (Var dst) pos MLOAD (Var src) hi
      rest (off+asz) (q+msz) sm = ((),sb)
Proof
  rewrite_tac[abi_decode_complex_member_phases] >>
  simp[abi_decode_member_setup_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `compile_abi_decode_to_buf _ _ MLOAD _ _ _ _ = ((),sm)` >>
  qexists_tac `sm` >> simp[abi_decode_member_code_def] >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem abi_decode_flat_member_shape:
  abi_decode_member_code dst pos src hi ei off q sa sb /\
  abi_decode_member_layout ei off q k z h cap ==>
  inst_extends sa sb /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  same_blocks sa sb
Proof
  strip_tac >> fs[abi_decode_member_code_def] >>
  drule_all abi_decode_member_phase_shape >> strip_tac >>
  `inst_extends sm sb` by metis_tac[inst_extends_trans] >>
  conj_tac >- metis_tac[inst_extends_trans] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb /\
   emitted_insts sm sb = emitted_insts sm sn ++ emitted_insts sn sb` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  simp[]
QED

Theorem abi_decode_flat_compile_shape:
  !elems off q sa sb.
    abi_decode_flat_layout elems off q z h cap /\
    compile_abi_decode_complex_elems (Var dst) pos MLOAD (Var src) hi
      elems off q sa = ((),sb) ==>
    inst_extends sa sb /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
    same_blocks sa sb
Proof
  Induct
  >- simp[Once compile_abi_decode_to_buf_def, comp_return_def,
       inst_extends_def, emitted_insts_def, same_blocks_def] >>
  qx_gen_tac `entry` >> PairCases_on `entry` >> rpt gen_tac >> strip_tac >>
  fs[abi_decode_flat_layout_def] >>
  drule abi_decode_flat_compile_cons >> strip_tac >>
  drule_all abi_decode_flat_member_shape >> strip_tac >>
  `inst_extends sm sb /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb) /\
   same_blocks sm sb` by
    (first_x_assum irule >> goal_assum (drule_at Any) >> simp[ADD_COMM]) >>
  conj_tac >- metis_tac[inst_extends_trans] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  simp[] >> metis_tac[same_blocks_trans]
QED

Theorem abi_decode_flat_compile_cons_code:
  abi_decode_flat_layout ((ei,asz,msz)::rest) off q z h cap /\
  compile_abi_decode_complex_elems (Var dst) pos MLOAD (Var src) hi
    ((ei,asz,msz)::rest) off q sa = ((),sb) /\
  fn_has_code sa sb func ==>
  ?sm. abi_decode_member_code dst pos src hi ei off q sa sm /\
    compile_abi_decode_complex_elems (Var dst) pos MLOAD (Var src) hi
      rest (off+asz) (q+msz) sm = ((),sb) /\
    inst_extends sa sm /\ inst_extends sm sb /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm) /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)
Proof
  strip_tac >> drule abi_decode_flat_compile_cons >> strip_tac >>
  fs[abi_decode_flat_layout_def] >>
  drule_all abi_decode_flat_member_shape >> strip_tac >>
  `inst_extends sm sb /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    metis_tac[abi_decode_flat_compile_shape] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (conj_tac
     >- (fs[abi_decode_member_code_def] >>
         rename1 `compile_getelemptr_abi _ _ _ _ _ _ sa = (_,select_st)` >>
         `cs_extends sa select_st` by
           metis_tac[cs_appends_abi_member_pointer, cs_appends_def] >>
         `cs_extends select_st sn` by metis_tac[emit_op_extends_next_var] >>
         drule cs_extends_abi_decode >> strip_tac >>
         metis_tac[cs_extends_trans]) >>
     metis_tac[cs_appends_def, cj 2 cs_appends_abi_decode_mutual]) >>
  drule_all fn_has_code_split >> strip_tac >>
  qexists_tac `sm` >> simp[] >>
  metis_tac[emitted_insts_append, inst_extends_def]
QED

Theorem abi_decode_supported_member_layout:
  supported_scalar_type ty /\ q + type_memory_bytes ce ty <= cap /\
  cap < dimword(:256) /\ w2n z+off+32 <= h ==>
  abi_decode_member_layout (type_to_abi_dec_info sf ce ty)
    off q (type_memory_bytes ce ty) z h cap /\
  abi_embedded_static_size ce.ce_struct_fields ty = 32
Proof
  Cases_on `ty` >> simp[supported_scalar_type_def,
    supported_word_type_def, supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, supported_string_type_def] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >>
       simp[supported_word_type_def, supported_string_type_def]) >>
  rpt strip_tac >>
  simp[abi_decode_member_layout_def, type_to_abi_dec_info_def,
    type_memory_bytes_def, abi_embedded_static_size_def,
    is_abi_dynamic_def, abi_static_size_def, contractABITheory.ceil32_def,
    MULT_COMM] >>
  fs[type_memory_bytes_def] >>
  qspec_then `n` assume_tac
    (REWRITE_RULE [contractABITheory.ceil32_def]
      (GEN_ALL contractABITheory.le_ceil32)) >> decide_tac
QED

Theorem abi_decode_supported_flat_layout:
  !tys off q.
    EVERY supported_scalar_type tys /\
    q + SUM (MAP (type_memory_bytes ce) tys) <= cap /\
    cap < dimword(:256) /\ w2n z+off+32*LENGTH tys <= h ==>
    abi_decode_flat_layout (abi_decoder_member_infos sf ce tys) off q z h cap
Proof
  Induct >> simp[abi_decoder_member_infos_def, abi_decode_flat_layout_def] >>
  qx_gen_tac `ty` >> rpt gen_tac >> strip_tac >>
  `abi_decode_member_layout (type_to_abi_dec_info sf ce ty)
     off q (type_memory_bytes ce ty) z h cap /\
   abi_embedded_static_size ce.ce_struct_fields ty = 32` by
    (irule abi_decode_supported_member_layout >> simp[] >> decide_tac) >>
  simp[abi_decode_flat_layout_def] >>
  first_x_assum (irule o REWRITE_RULE [abi_decoder_member_infos_def]) >>
  simp[] >> decide_tac
QED
