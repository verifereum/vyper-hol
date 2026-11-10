Theory abiDecodePtrRejectPrefix
Ancestors
  abiDecodePtrPhysicalFlatRun abiDecodePtrFlatLayout abiDecodePtrMemberInterface
  abiDecoderMemberInfos abiDecoderCoherence abiValidMembers abiDecoderMemberCons
  abiEncoder compileEnv exprLowering valueEncoding fragExec
  vyperABI venomExecSemantics venomState words list rich_list arithmetic pair

Theorem abi_decode_complex_elems_append:
  !pre rest off q st last.
    compile_abi_decode_complex_elems dst pos opc src hi
      (pre ++ rest) off q st = ((),last) ==>
    ?sm. compile_abi_decode_complex_elems dst pos opc src hi pre off q st = ((),sm) /\
      compile_abi_decode_complex_elems dst pos opc src hi rest
        (off + SUM (MAP (FST o SND) pre))
        (q + SUM (MAP (SND o SND) pre)) sm = ((),last)
Proof
  Induct >- (simp[Once compile_abi_decode_to_buf_def, comp_return_def] >> metis_tac[]) >>
  qx_gen_tac `entry` >> PairCases_on `entry` >> rpt gen_tac >>
  simp_tac bool_ss [APPEND, MAP, SUM, combinTheory.o_THM, FST, SND] >>
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac (srw_ss()) [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `sm` >>
  conj_tac
  >- (pure_once_rewrite_tac[compile_abi_decode_to_buf_def] >>
      asm_simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def,
        LET_THM, ADD_COMM] >> simp[]) >>
  asm_simp_tac bool_ss [ADD_ASSOC]
QED

Theorem abi_decode_valid_members_prefix:
  !pre rest raw hds.
    vyper_decode_valid_enc_tuple (pre ++ rest) raw hds ==>
    vyper_decode_valid_enc_tuple pre raw hds
Proof
  Induct >- simp[Once vyper_decode_valid_enc_def] >>
  rpt gen_tac >> simp_tac bool_ss [APPEND] >> strip_tac >>
  Cases_on `is_dynamic h` >>
  gvs[Once vyper_decode_valid_enc_def] >>
  first_x_assum drule >> strip_tac >>
  simp[Once vyper_decode_valid_enc_def]
QED

Theorem abi_decode_selected_compile:
  compile_abi_decode_complex_elems (Var dst) pos MLOAD (Var src) hi
    (abi_decoder_member_infos ce.ce_struct_fields ce (pre ++ ty::post)) off q st = ((),last) ==>
  ?sm sn.
    compile_abi_decode_complex_elems (Var dst) pos MLOAD (Var src) hi
      (abi_decoder_member_infos ce.ce_struct_fields ce pre) off q st = ((),sm) /\
    abi_decode_member_code dst pos src hi (type_to_abi_dec_info ce.ce_struct_fields ce ty)
      (off + SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) pre))
      (q + SUM (MAP (type_memory_bytes ce) pre)) sm sn /\
    compile_abi_decode_complex_elems (Var dst) pos MLOAD (Var src) hi
      (abi_decoder_member_infos ce.ce_struct_fields ce post)
      (off + SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) pre) +
        abi_embedded_static_size ce.ce_struct_fields ty)
      (q + SUM (MAP (type_memory_bytes ce) pre) + type_memory_bytes ce ty) sn = ((),last)
Proof
  simp_tac bool_ss [abi_decoder_member_infos_def, MAP_APPEND, MAP] >> strip_tac >>
  drule abi_decode_complex_elems_append >>
  simp_tac (srw_ss()) [MAP_MAP_o, combinTheory.o_DEF] >> strip_tac >>
  drule abi_decode_flat_compile_cons >> strip_tac >>
  metis_tac[]
QED

Theorem abi_decode_selected_prefix_run:
  EVERY supported_scalar_type pre /\
  LIST_REL (abi_decoder_coherent ce env ce.ce_struct_fields) pre tvs /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) (pre ++ ty::post)) bs bs /\
  abi_to_vyper_list env pre
    (abi_decode_members (MAP (vyper_to_abi_type env) pre) bs bs) = SOME vs /\
  compile_abi_decode_complex_elems (Var dst) pos MLOAD (Var src) hi
    (abi_decoder_member_infos ce.ce_struct_fields ce (pre ++ ty::post)) 0 0 st = ((),last) /\
  mem_bytes_at (B+z) (LENGTH bs) (abi_decode_source MLOAD s) = bs /\
  B+z+LENGTH bs < dimword(:256) /\
  d+SUM (MAP (type_memory_bytes ce) pre) < dimword(:256) /\
  (B+z+LENGTH bs <= d \/ d+SUM (MAP (type_memory_bytes ce) pre) <= B+z) /\
  eval_operand (Var src) s = SOME (n2w B) /\
  eval_operand pos s = SOME (n2w z) /\ eval_operand (Var dst) s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var pos /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  abi_decoder_operand_live st.cs_next_var (Var src) /\
  abi_decoder_operand_live st.cs_next_var hi /\ fresh_vars_wrt st s /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    z+LENGTH bs <= h /\ h < dimword(:256)) ==>
  ?sm sn reached.
    compile_abi_decode_complex_elems (Var dst) pos MLOAD (Var src) hi
      (abi_decoder_member_infos ce.ce_struct_fields ce pre) 0 0 st = ((),sm) /\
    abi_decode_member_code dst pos src hi (type_to_abi_dec_info ce.ce_struct_fields ce ty)
      (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pre)))
      (SUM (MAP (type_memory_bytes ce) pre)) sm sn /\
    compile_abi_decode_complex_elems (Var dst) pos MLOAD (Var src) hi
      (abi_decoder_member_infos ce.ce_struct_fields ce post)
      (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pre)) +
        abi_embedded_static_size ce.ce_struct_fields ty)
      (SUM (MAP (type_memory_bytes ce) pre) + type_memory_bytes ce ty) sn = ((),last) /\
    run_inst_seq (emitted_insts st sm) s = OK reached /\ inst_extends st sm /\
    tuple_in_memory vs tvs d reached.vs_memory /\
    abi_decode_frame d (SUM (MAP (type_memory_bytes ce) pre)) s reached /\
    fresh_vars_wrt sm reached /\
    reached.vs_allocas = s.vs_allocas /\ reached.vs_alloca_next = s.vs_alloca_next /\
    mem_bytes_at (B+z) (LENGTH bs) (abi_decode_source MLOAD reached) = bs /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op reached = SOME w)
Proof
  strip_tac >>
  `MAP (abi_embedded_static_size ce.ce_struct_fields) pre =
    MAP abi_member_head_size (MAP (vyper_to_abi_type env) pre)` by
    (simp_tac bool_ss [MAP_MAP_o] >> irule MAP_CONG >> simp_tac bool_ss [] >>
     rpt strip_tac >> drule_all LIST_REL_MEM_IMP >> strip_tac >>
     drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  drule abi_decode_selected_compile >> simp_tac bool_ss [ADD_CLAUSES] >> strip_tac >>
  `vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) pre) bs bs` by
    (irule abi_decode_valid_members_prefix >>
     qexists_tac `MAP (vyper_to_abi_type env) (ty::post)` >> fs[MAP_APPEND]) >>
  mp_tac (Q.SPECL [`pre`, `tvs`, `vs`, `[]`, `0`, `st`, `sm`, `s`]
    abi_decode_physical_flat_sequence) >>
  simp_tac bool_ss [APPEND, MAP, SUM, DROP_0, ADD_CLAUSES] >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> metis_tac[])) >> strip_tac >>
  qexistsl_tac [`sm`, `sn`, `t`] >> gvs[]
QED
