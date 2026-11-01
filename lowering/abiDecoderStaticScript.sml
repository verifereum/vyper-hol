Theory abiDecoderStatic
Ancestors
  abiDecoderStaticSingleton abiDecoderWordTyped abiDecoderLayout abiDecoderTypedContract
  abiDecoderTypedCompose abiDecoderCoherence abiDecoderDynamic abiDecodeRanges
  abiDecoderReservation abiDecoderContract exprLowering compileEnv emitHelperProps valueEncoding
  vyperABI contractABI venomExecSemantics venomState venomInst words list
  abiDecoderSingletonFragment abiDecoderPointed abiDecoderAppend fragExec exprLoweringProps
  emitHelper instIdxIndep combin abiDecoderPrimitiveCaller abiDecoderClampedWord abiDecoderBytesTyped
  abiDecoderGuards abiEncoder rich_list

(* ===== Singleton Typed ===== *)

(* Typed static singleton setup, including the wrapped uint256 path. *)

Theorem abi_decoder_pre_operands:
  abi_decoder_pre ce env ty tv di av v st last src dst opc hi sb d b cap s /\
  eval_operand child_src s = SOME (n2w sb) /\
  eval_operand child_dst s = SOME (n2w d) ==>
  abi_decoder_pre ce env ty tv di av v st last child_src child_dst opc hi sb d b cap s
Proof
  rw[abi_decoder_pre_def, abi_decoder_ranges_def]
QED

Theorem abi_decoder_static_singleton_child:
  abi_decoder_recursive_pre ce env sf (TupleT [ty]) (TupleTV [tv])
    (DecComplex F [(di,head_sz,mem_sz)])
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap s ==>
  abi_decoder_recursive_pre ce env sf ty tv di av v
    st last src dst opc hi sb d b cap s /\
  type_memory_bytes ce ty = mem_sz /\
  LENGTH (enc (vyper_to_abi_type env ty) av) = head_sz /\
  head_sz = mem_sz /\ ~abi_decoder_dynamic di
Proof
  strip_tac >>
  qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def]) >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_tuple_iff] >>
  `type_to_abi_dec_info sf ce ty = di /\
   ~is_abi_dynamic ce.ce_struct_fields ty /\
   abi_embedded_static_size ce.ce_struct_fields ty = head_sz /\
   type_memory_bytes ce ty = mem_sz` by
    (qpat_x_assum `DecComplex F _ = type_to_abi_dec_info sf ce (TupleT [ty])` mp_tac >>
     simp[Once type_to_abi_dec_info_def] >> metis_tac[]) >>
  `abi_decoder_header ce env ty tv` by
    (qpat_assum `abi_decoder_coherent ce env sf ty tv`
      (mp_tac o MATCH_MP abi_decoder_coherent_header) >> simp[]) >>
  `~is_dynamic (vyper_to_abi_type env ty)` by fs[abi_decoder_header_def] >>
  `head_sz = mem_sz` by gvs[abi_decoder_header_def, abi_member_head_size_def] >>
  `~abi_decoder_dynamic di` by
    (qpat_assum `abi_decoder_coherent ce env sf ty tv`
       (mp_tac o MATCH_MP abi_decoder_coherent_dynamic) >> asm_simp_tac bool_ss []) >>
  drule_all abi_decoder_static_singleton_pre_child >> strip_tac >>
  `abi_decoder_metadata ce env ty tv
     (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v` by fs[abi_decoder_pre_def] >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) = head_sz` by
    (drule_all abi_decoder_descended_encoding_length >> simp[]) >>
  simp[abi_decoder_recursive_pre_def]
QED

Theorem abi_decoder_static_singleton_setup:
  abi_decode_static_singleton_setup dst src hi head_sz st = ((child_src,child_dst),st') /\
  abi_decoder_recursive_pre ce env sf (TupleT [ty]) (TupleTV [tv])
    (DecComplex F [(di,head_sz,mem_sz)])
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_recursive_pre ce env sf ty tv di av v
      st' last child_src child_dst opc hi sb d b cap t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  strip_tac >> drule_all abi_decoder_static_singleton_child >> strip_tac >>
  `abi_decode_static_singleton_setup_pre st src dst hi head_sz sb d s` by
    (qpat_assum `abi_decoder_recursive_pre ce env sf ty tv di
       av v st last src dst opc hi sb d b cap s` mp_tac >>
     pure_rewrite_tac [abi_decode_static_singleton_setup_pre_def,
       abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
     asm_simp_tac bool_ss [] >> metis_tac[]) >>
  drule_all abi_decode_static_singleton_setup_sequence >> strip_tac >>
  drule_all abi_decode_static_singleton_setup_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
     (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  `abi_decoder_pre ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
     av v st last src dst opc hi sb d b cap s` by fs[abi_decoder_recursive_pre_def] >>
  drule_all abi_decoder_pre_pure_transport >> strip_tac >>
  drule_all abi_decoder_pre_operands >> strip_tac >>
  qexists_tac `t` >> gvs[abi_decoder_recursive_pre_def]
QED

Theorem abi_decoder_static_singleton_word_child =
  SIMP_RULE bool_ss [abi_decoder_dynamic_def]
    (Q.INST [`di` |-> `DecPrimWord NoClamp`, `head_sz` |-> `32`, `mem_sz` |-> `32`]
      abi_decoder_static_singleton_child);

Theorem abi_decoder_static_singleton_word_setup =
  Q.INST [`di` |-> `DecPrimWord NoClamp`, `head_sz` |-> `32`, `mem_sz` |-> `32`]
    abi_decoder_static_singleton_setup;

(* ===== Singleton Compose ===== *)

(* Static singleton composition is independent of the child's decoder body. *)

Theorem abi_decoder_static_singleton_setup_fragment:
  abi_decode_static_singleton_setup dst src hi head_sz st =
    ((child_src,child_dst),middle) /\
  abi_decoder_recursive_pre ce env sf (TupleT [ty]) (TupleTV [tv])
    (DecComplex F [(di,head_sz,mem_sz)])
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap initial ==>
  frag_exec ctx st middle (\s. s = initial)
    (\mid. abi_decoder_recursive_pre ce env sf ty tv di av v
       middle last child_src child_dst opc hi sb d b cap mid /\
       abi_decoder_pure_prefix initial mid) (K F)
Proof
  strip_tac >> drule_all abi_decode_static_singleton_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st middle)` by fs[EVERY_CONJ] >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_static_singleton_setup >> strip_tac >>
  qexists_tac `t` >>
  simp[abi_decoder_recursive_pre_inst_idx, abi_decoder_pure_prefix_def,
       eval_op_inst_idx]
QED

Theorem abi_decoder_static_singleton_fragment:
  compile_abi_decode_to_buf dst src opc hi
    (DecComplex F [(di,head_sz,mem_sz)]) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf (TupleT [ty]) (TupleTV [tv])
    (DecComplex F [(di,head_sz,mem_sz)])
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap initial /\
  (!child_src child_dst middle mid.
    abi_decode_static_singleton_setup dst src hi head_sz st =
      ((child_src,child_dst),middle) /\
    abi_decoder_recursive_pre ce env sf ty tv di av v
      middle last child_src child_dst opc hi sb d b cap mid ==>
    frag_exec ctx middle st' (\s. s = mid)
      (abi_decoder_post tv v st' d (type_memory_bytes ce ty) b cap mid) (K F)) ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_decoder_post (TupleTV [tv]) (ArrayV (TupleV [v]))
       st' d (type_memory_bytes ce ty) b cap initial) (K F)
Proof
  strip_tac >>
  `~abi_decoder_dynamic di` by
    (drule_all abi_decoder_static_singleton_child >> strip_tac >> simp[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_static_singleton_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >>
  rename1 `abi_decode_static_singleton_setup dst src hi head_sz st = (child_ops,middle)` >>
  PairCases_on `child_ops` >> gvs[] >>
  rename1 `abi_decode_static_singleton_setup dst src hi head_sz st =
    ((child_src,child_dst),middle)` >>
  `compile_abi_decode_to_buf child_dst child_src opc hi di middle = ((),st')` by
    (qpat_x_assum `_ = ((),st')` mp_tac >> asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF]) >>
  drule_all abi_decoder_static_singleton_setup_fragment >> strip_tac >>
  drule_all abi_decode_static_singleton_setup_shape >> strip_tac >>
  `cs_extends st middle` by (irule cs_extends_same_block >> simp[]) >>
  `cs_extends middle st'` by (drule_all cs_extends_abi_decode >> simp[]) >>
  irule frag_exec_initial_seq >>
  qexistsl_tac [`\mid. abi_decoder_recursive_pre ce env sf ty tv di av v
     middle last child_src child_dst opc hi sb d b cap mid /\
     abi_decoder_pure_prefix initial mid`, `middle`] >>
  simp[] >> rpt strip_tac >>
  irule abi_decoder_singleton_child_fragment >> conj_tac
  >- (first_x_assum irule >> simp[]) >> simp[]
QED

Theorem abi_decoder_static_singleton_unwrapped_fragment =
  SIMP_RULE bool_ss [abi_decoder_singleton_post_function]
    abi_decoder_static_singleton_fragment;

(* ===== Singleton Fragment ===== *)

(* Actual static singleton execution and its unwrapped memory result. *)

Theorem abi_decoder_static_wrapped_word_sequence:
  compile_abi_decode_to_buf dst src opc hi
    (DecComplex F [(DecPrimWord clamp,32,32)]) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf (TupleT [ty]) (TupleTV [tv])
    (DecComplex F [(DecPrimWord clamp,32,32)])
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_post (TupleTV [tv]) (ArrayV (TupleV [v])) st' d 32 b cap s t
Proof
  strip_tac >>
  `~abi_decoder_dynamic (DecPrimWord clamp)` by simp[abi_decoder_dynamic_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_static_singleton_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >>
  rename1 `abi_decode_static_singleton_setup dst src hi 32 st = (child_ops,c1)` >>
  PairCases_on `child_ops` >> gvs[] >>
  rename1 `abi_decode_static_singleton_setup dst src hi 32 st = ((child_src,child_dst),c1)` >>
  `compile_abi_decode_to_buf child_dst child_src opc hi (DecPrimWord clamp) c1 =
     ((),st')` by
    (qpat_x_assum `_ = ((),st')` mp_tac >> asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF]) >>
  drule_all abi_decoder_static_singleton_setup >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK mid` >>
  drule_all abi_decoder_typed_primitive_word_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') mid = OK t` >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `inst_extends c1 st'` by
    (irule abi_decoder_inst_extends_prefix >> first_assum ACCEPT_TAC) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  `abi_decoder_post (TupleTV [tv]) (ArrayV (TupleV [v])) st' d 32 b cap s t` by
    (simp_tac bool_ss [abi_decoder_singleton_post] >>
     drule_all abi_decoder_post_pure_prefix >> simp[]) >>
  qexists_tac `t` >> simp[]
QED

Theorem abi_decoder_static_unwrapped_word_sequence =
  SIMP_RULE bool_ss [abi_decoder_singleton_post] abi_decoder_static_wrapped_word_sequence;

Theorem abi_decoder_static_wrapped_word_shape:
  compile_abi_decode_to_buf dst src opc hi
    (DecComplex F [(DecPrimWord clamp,32,32)]) st = ((),st') /\
  abi_decode_source_opcode opc ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  strip_tac >>
  `~abi_decoder_dynamic (DecPrimWord clamp)` by simp[abi_decoder_dynamic_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_static_singleton_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >>
  rename1 `abi_decode_static_singleton_setup dst src hi 32 st = (child_ops,c1)` >>
  PairCases_on `child_ops` >> gvs[] >>
  rename1 `abi_decode_static_singleton_setup dst src hi 32 st = ((child_src,child_dst),c1)` >>
  `compile_abi_decode_to_buf child_dst child_src opc hi (DecPrimWord clamp) c1 =
     ((),st')` by
    (qpat_x_assum `_ = ((),st')` mp_tac >> asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF]) >>
  drule_all abi_decode_static_singleton_setup_shape >> strip_tac >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `inst_extends st c1 /\ inst_extends c1 st'` by
    (conj_tac >> irule abi_decoder_inst_extends_prefix >> first_assum ACCEPT_TAC) >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  gvs[EVERY_CONJ] >> irule IS_PREFIX_TRANS >> qexists_tac `c1.cs_current_insts` >> simp[]
QED

Theorem abi_decoder_static_wrapped_word_from_state:
  compile_abi_decode_to_buf dst src opc hi
    (DecComplex F [(DecPrimWord clamp,32,32)]) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf (TupleT [ty]) (TupleTV [tv])
    (DecComplex F [(DecPrimWord clamp,32,32)])
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_decoder_post (TupleTV [tv]) (ArrayV (TupleV [v])) st' d 32 b cap initial) (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decoder_static_wrapped_word_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_static_wrapped_word_sequence >> strip_tac >>
  qexists_tac `t` >> simp[abi_decoder_post_inst_idx]
QED

Theorem abi_decoder_static_unwrapped_word_from_state =
  SIMP_RULE bool_ss [abi_decoder_singleton_post_function]
    abi_decoder_static_wrapped_word_from_state;
