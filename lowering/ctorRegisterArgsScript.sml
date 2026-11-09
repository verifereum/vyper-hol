Theory ctorRegisterArgs
Ancestors
  ctorArgDecode ctorAbiActualRecursive ctorAbiActualFrame ctorAbiActualSites ctorAbiActualMemory
  abiDecoderCoherence abiDecoderTypedContract exprLowering
  abiDecoderAppend abiDecoderCounters abiDecoderCode abiDecoderContract abiDecoderPhi abiEncoder emitHelper emitHelperProps context fragExec
  abiEncoderRegisteredEffect abiEncoderProps actualAllocCredit actualAllocExec
  entryArgPtrs localPtrsProps compileEnv compileVyper moduleLowering moduleLoweringProps allocLimitsProps
  allocaFrontierBound allocaBudgetProps valueEncoding vyperABI vyperCompiler
  venomExecSemantics venomState venomInst venomMemDefs
  words list finite_map pred_set arithmetic
  ctorAbiActualArrayRun loweringHalt abiDecoderLoop exprLoweringProps
  abiDecoderReentryAddress abiDecoderMemberSlice abiDecoderMemberBody rich_list abiDecoderMembers

Theorem ctor_type_memory_bytes_vars[simp]:
  !ce ty vars. type_memory_bytes (ce with ce_vars := vars) ty =
    type_memory_bytes ce ty
Proof
  rpt gen_tac >> irule type_memory_bytes_struct_fields >> simp[]
QED

Theorem ctor_dec_info_vars[simp]:
  !sf ce ty vars. type_to_abi_dec_info sf (ce with ce_vars := vars) ty =
    type_to_abi_dec_info sf ce ty
Proof
  recInduct type_to_abi_dec_info_ind >>
  simp[type_to_abi_dec_info_def] >> rpt strip_tac
  >- (irule LIST_EQ >> simp[EL_GENLIST] >> metis_tac[])
  >- (irule MAP_CONG >> simp[])
  >> Cases_on `FLOOKUP sfields (nsid_to_string nsid)` >> simp[] >>
  irule MAP_CONG >> simp[] >>
  rpt strip_tac >> pairarg_tac >> gvs[] >> metis_tac[]
QED

Theorem ctor_positional_arg_vars[simp]:
  build_positional_arg (ce with ce_vars := vars) arg =
    build_positional_arg ce arg
Proof
  PairCases_on `arg` >> simp[build_positional_arg_def]
QED

Theorem ctor_positional_args_vars[simp]:
  build_positional_args (ce with ce_vars := vars) args =
    build_positional_args ce args
Proof
  simp[build_positional_args_def] >> irule MAP_CONG >> simp[]
QED

Theorem ctor_decoder_header_vars[simp]:
  abi_decoder_header (ce with ce_vars := vars) env ty tv <=>
    abi_decoder_header ce env ty tv
Proof
  simp[abi_decoder_header_def]
QED

Theorem ctor_decoder_metadata_vars[simp]:
  abi_decoder_metadata (ce with ce_vars := vars) env ty tv di av v <=>
    abi_decoder_metadata ce env ty tv di av v
Proof
  simp[abi_decoder_metadata_def]
QED

Theorem ctor_decoder_coherent_vars_forward:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
    !vars. abi_decoder_coherent (ce with ce_vars := vars) env sf ty tv
Proof
  ho_match_mp_tac abi_decoder_coherent_ind >>
  rpt strip_tac >> simp[Once abi_decoder_coherent_cases] >>
  gvs[ctor_decoder_header_vars] >>
  gvs[LIST_REL_EL_EQN] >> metis_tac[]
QED

Theorem ctor_decoder_coherent_vars[simp]:
  abi_decoder_coherent (ce with ce_vars := vars) env sf ty tv <=>
    abi_decoder_coherent ce env sf ty tv
Proof
  eq_tac >- (strip_tac >> drule ctor_decoder_coherent_vars_forward >>
    disch_then (qspec_then `ce.ce_vars` mp_tac) >> simp[]) >>
  metis_tac[ctor_decoder_coherent_vars_forward]
QED

Theorem ctor_remaining_lookup_update:
  ALL_DISTINCT (MAP FST (arg::rest)) /\
  EVERY (\a. ?off. FLOOKUP ce.ce_vars (FST a) =
    SOME (MemLoc off (type_memory_bytes ce (SND a)))) rest ==>
  EVERY (\a. ?off. FLOOKUP
    (ce with ce_vars := ce.ce_vars |+ (FST arg,loc)).ce_vars (FST a) =
    SOME (MemLoc off (type_memory_bytes ce (SND a)))) rest
Proof
  simp[EVERY_MEM, MEM_MAP, FLOOKUP_UPDATE] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  `FST a <> FST arg` by metis_tac[] >> simp[]
QED

Theorem ctor_canonical_offset_step:
  !atys i. i < LENGTH atys ==>
  SUM (MAP abi_member_head_size (TAKE (SUC i) atys)) =
    SUM (MAP abi_member_head_size (TAKE i atys)) +
    abi_member_head_size (EL i atys)
Proof
  Induct >- simp[] >> gen_tac >> Cases_on `i`
  >- simp[NoAsms] >> strip_tac >>
  `n < LENGTH atys` by gvs[] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  asm_rewrite_tac [] >> disch_tac >>
  simp[NoAsms] >>
  first_x_assum SUBST1_TAC >> decide_tac
QED

Theorem ctor_coherent_head_size:
  abi_decoder_coherent ce env sf ty tv ==>
  abi_embedded_static_size ce.ce_struct_fields ty =
    abi_member_head_size (vyper_to_abi_type env ty)
Proof
  strip_tac >> drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]
QED

Theorem ctor_register_nil:
  compile_register_constructor_args ce (build_positional_args ce [])
    off data_size st = (ce,st)
Proof
  simp[build_positional_args_def, compile_register_constructor_args_def,
       comp_return_def]
QED

Theorem ctor_register_cons:
  FLOOKUP ce.ce_vars name = SOME (MemLoc old (type_memory_bytes ce ty)) ==>
  compile_register_constructor_args ce
    (build_positional_args ce ((name,ty)::rest)) off data_size st =
  (do buf <- compile_alloc_buffer (type_memory_bytes ce ty);
      compile_decode_args
        (ce with ce_vars := ce.ce_vars |+
          (name, PtrVar buf.buf_operand (type_memory_bytes ce ty)))
        [build_positional_arg ce (name,ty)]
        off DLOAD (Lit (n2w data_size)) 0;
      compile_register_constructor_args
        (ce with ce_vars := ce.ce_vars |+
          (name, PtrVar buf.buf_operand (type_memory_bytes ce ty)))
        (build_positional_args ce rest)
        (off + abi_embedded_static_size ce.ce_struct_fields ty) data_size
   od) st
Proof
  strip_tac >>
  simp_tac (srw_ss()) [LET_THM, build_positional_args_def, build_positional_arg_def,
       Once compile_register_constructor_args_def,
       var_location_memory_size_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >>
  `!buf. (ce with ce_vars updated_by
      (\m. m |+ (name, PtrVar buf.buf_operand (type_memory_bytes ce ty)))) =
    (ce with ce_vars := ce.ce_vars |+
      (name, PtrVar buf.buf_operand (type_memory_bytes ce ty)))`
    by simp[compile_env_component_equality] >>
  asm_simp_tac (srw_ss()) [LET_THM, var_location_memory_size_def,
    comp_bind_def, comp_return_def, comp_ignore_bind_def]
QED

Theorem ctor_registration_appends:
  !args ce off data_size.
    cs_appends (compile_register_constructor_args ce args off data_size)
Proof
  Induct >- simp[compile_register_constructor_args_def, cs_appends_return] >>
  PairCases >> rpt gen_tac >> simp[Once compile_register_constructor_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  Cases_on `var_location_memory_size x` >> simp[] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_abi_alloc_buffer] >> gen_tac >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_return] >> gen_tac >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- simp[cs_appends_decode_args] >> simp[]
QED

Theorem ctor_registration_extends:
  compile_register_constructor_args ce args off data_size st = (ce',st') ==>
    cs_extends st st'
Proof
  metis_tac[ctor_registration_appends, cs_appends_def]
QED


Theorem ctor_decode_args_vars_mono:
  !args ce off opc hi adj.
    abi_decoder_vars_mono (compile_decode_args ce args off opc hi adj)
Proof
  Induct >- simp[compile_decode_args_def, abi_decoder_vars_mono_return] >>
  PairCases >> rpt gen_tac >> simp[Once compile_decode_args_def] >>
  rpt (IF_CASES_TAC >> simp[])
  >- (ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac
      >- simp[abi_decoder_vars_mono_prims] >> gen_tac >>
      ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac
      >- simp[abi_decoder_vars_mono_prims] >> gen_tac >>
      irule abi_decoder_vars_mono_ignore_bind >> conj_tac
      >- simp[abi_decoder_vars_mono_abi_clamp] >>
      irule abi_decoder_vars_mono_ignore_bind >> conj_tac
      >- (Cases_on `FLOOKUP ce.ce_vars h0` >> simp[abi_decoder_vars_mono_return] >>
          Cases_on `var_location_decode_operand x` >>
          simp[abi_decoder_vars_mono_return, abi_decoder_vars_mono_prims]) >> simp[]) >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  Cases_on `var_location_decode_operand x` >> simp[] >>
  rpt (ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac
        >- simp[abi_decoder_vars_mono_prims] >> gen_tac) >>
  (ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac
   >- simp[cj 1 abi_decoder_vars_mono_mutual] >> simp[])
QED

Theorem ctor_registration_vars_mono:
  !args ce off data_size.
    abi_decoder_vars_mono (compile_register_constructor_args ce args off data_size)
Proof
  Induct >- simp[compile_register_constructor_args_def, abi_decoder_vars_mono_return] >>
  PairCases >> rpt gen_tac >> simp[Once compile_register_constructor_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  Cases_on `var_location_memory_size x` >> simp[] >>
  ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac
  >- simp[abi_decoder_vars_mono_abi_alloc_buffer] >> gen_tac >>
  ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac
  >- simp[abi_decoder_vars_mono_return] >> gen_tac >>
  ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac
  >- simp[ctor_decode_args_vars_mono] >> simp[]
QED

Theorem ctor_registration_next_var:
  compile_register_constructor_args ce args off data_size st = (ce',st') ==>
    st.cs_next_var <= st'.cs_next_var
Proof
  metis_tac[ctor_registration_vars_mono, abi_decoder_vars_mono_def, pairTheory.SND]
QED

Theorem ctor_id_bind[local]:
  (!st. st.cs_next_id <= (SND (f st)).cs_next_id) /\
  (!v st. st.cs_next_id <= (SND (g v st)).cs_next_id) ==>
  !st. st.cs_next_id <= (SND (comp_bind f g st)).cs_next_id
Proof
  rw[comp_bind_def] >> pairarg_tac >> simp[] >>
  metis_tac[LESS_EQ_TRANS, pairTheory.SND]
QED

Theorem ctor_id_ignore_bind[local]:
  (!st. st.cs_next_id <= (SND (f st)).cs_next_id) /\
  (!st. st.cs_next_id <= (SND (g st)).cs_next_id) ==>
  !st. st.cs_next_id <= (SND (comp_ignore_bind f g st)).cs_next_id
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule ctor_id_bind >> simp[]
QED

Theorem ctor_id_prims[local]:
  (!v st. st.cs_next_id <= (SND (comp_return v st)).cs_next_id) /\
  (!opc ops st. st.cs_next_id <= (SND (emit_op opc ops st)).cs_next_id) /\
  (!opc ops st. st.cs_next_id <= (SND (emit_void opc ops st)).cs_next_id) /\
  (!n st. st.cs_next_id <= (SND (compile_alloc_buffer n st)).cs_next_id) /\
  (!c v st. st.cs_next_id <=
    (SND (compile_abi_clamp_basetype v c st)).cs_next_id)
Proof
  rpt conj_tac
  >- simp[comp_return_def]
  >- simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_var_def, fresh_id_def, emit_def]
  >- simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, emit_def]
  >- simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  metis_tac[abi_decoder_code_clamp, abi_decoder_code_def]
QED

Theorem ctor_decode_args_next_id:
  !args ce off hi adj st.
    st.cs_next_id <=
      (SND (compile_decode_args ce args off DLOAD hi adj st)).cs_next_id
Proof
  Induct >- simp[compile_decode_args_def, ctor_id_prims] >>
  PairCases >> rpt gen_tac >> simp[Once compile_decode_args_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> qid_spec_tac `st`
  >- (ho_match_mp_tac ctor_id_bind >> conj_tac
      >- simp[ctor_id_prims] >> gen_tac >>
      ho_match_mp_tac ctor_id_bind >> conj_tac
      >- simp[ctor_id_prims] >> gen_tac >>
      ho_match_mp_tac ctor_id_ignore_bind >> conj_tac
      >- simp[ctor_id_prims] >>
      ho_match_mp_tac ctor_id_ignore_bind >> conj_tac
      >- (Cases_on `FLOOKUP ce.ce_vars h0` >> simp[ctor_id_prims] >>
          Cases_on `var_location_decode_operand x` >> simp[ctor_id_prims]) >> simp[]) >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  Cases_on `var_location_decode_operand x` >> simp[] >>
  rpt (ho_match_mp_tac ctor_id_bind >> conj_tac
        >- simp[ctor_id_prims] >> gen_tac) >>
  (ho_match_mp_tac ctor_id_ignore_bind >> conj_tac
   >- (gen_tac >>
       mp_tac (cj 1 abi_decoder_code_mutual) >>
       simp[abi_decoder_code_def] >> metis_tac[]) >> simp[])
QED

Theorem ctor_registration_id_mono:
  !args ce off data_size st.
    st.cs_next_id <=
      (SND (compile_register_constructor_args ce args off data_size st)).cs_next_id
Proof
  Induct >- simp[compile_register_constructor_args_def, ctor_id_prims] >>
  PairCases >> rpt gen_tac >> simp[Once compile_register_constructor_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  Cases_on `var_location_memory_size x` >> simp[] >> qid_spec_tac `st` >>
  ho_match_mp_tac ctor_id_bind >> conj_tac
  >- simp[ctor_id_prims] >> gen_tac >>
  ho_match_mp_tac ctor_id_bind >> conj_tac
  >- simp[ctor_id_prims] >> gen_tac >>
  ho_match_mp_tac ctor_id_ignore_bind >> conj_tac
  >- simp[ctor_decode_args_next_id] >> simp[]
QED

Theorem ctor_registration_next_id:
  compile_register_constructor_args ce args off data_size st = (ce',st') ==>
    st.cs_next_id <= st'.cs_next_id
Proof
  metis_tac[ctor_registration_id_mono, pairTheory.SND]
QED

Theorem ctor_registration_code_phases:
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_decode_args ce args off DLOAD hi 0 allocated = ((),decoded) /\
  compile_register_constructor_args ce rest next_off data_size decoded = (ce',last) /\
  fn_has_code st last func ==>
  fn_has_code st allocated func /\
  fn_has_code allocated decoded func /\
  fn_has_code decoded last func /\
  frag_ids st allocated SUBSET frag_ids st last /\
  frag_ids allocated decoded SUBSET frag_ids st last /\
  frag_ids decoded last SUBSET frag_ids st last
Proof
  strip_tac >>
  `cs_extends st allocated` by
    metis_tac[cs_appends_abi_alloc_buffer, cs_appends_def] >>
  `cs_extends allocated decoded` by
    metis_tac[cs_appends_decode_args, cs_appends_def] >>
  `cs_extends decoded last` by metis_tac[ctor_registration_extends] >>
  `cs_extends allocated last` by metis_tac[cs_extends_trans] >>
  `fn_has_code st allocated func /\ fn_has_code allocated last func` by
    (irule fn_has_code_split >> simp[] >> metis_tac[]) >>
  `fn_has_code allocated decoded func /\ fn_has_code decoded last func` by
    (irule fn_has_code_split >> simp[] >> metis_tac[]) >>
  `st.cs_next_id <= allocated.cs_next_id` by
    metis_tac[ctor_id_prims, pairTheory.SND] >>
  `allocated.cs_next_id <= decoded.cs_next_id` by
    metis_tac[ctor_decode_args_next_id, pairTheory.SND] >>
  `decoded.cs_next_id <= last.cs_next_id` by
    metis_tac[ctor_registration_next_id] >>
  simp[frag_ids_def, SUBSET_DEF] >> decide_tac
QED

Theorem ctor_decode_args_phi:
  !args ce off hi adj st.
    abi_decoder_phi st
      (SND (compile_decode_args ce args off DLOAD hi adj st))
Proof
  Induct >- simp[compile_decode_args_def, abi_decoder_phi_return] >>
  PairCases >> rpt gen_tac >> simp[Once compile_decode_args_def] >>
  rpt (IF_CASES_TAC >> simp[])
  >- (ho_match_mp_tac abi_decoder_phi_bind >> conj_tac
      >- simp[abi_decoder_phi_emit_op] >> rpt gen_tac >>
      ho_match_mp_tac abi_decoder_phi_bind >> conj_tac
      >- simp[abi_decoder_phi_emit_op] >> rpt gen_tac >>
      ho_match_mp_tac abi_decoder_phi_ignore_bind >> conj_tac
      >- simp[abi_decoder_phi_clamp] >> rpt gen_tac >>
      ho_match_mp_tac abi_decoder_phi_ignore_bind >> conj_tac
      >- (rpt gen_tac >> Cases_on `FLOOKUP ce.ce_vars h0` >>
          simp[abi_decoder_phi_return] >>
          Cases_on `var_location_decode_operand x` >>
          simp[abi_decoder_phi_return, abi_decoder_phi_emit_void]) >> simp[]) >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  Cases_on `var_location_decode_operand x` >> simp[] >>
  rpt (ho_match_mp_tac abi_decoder_phi_bind >> conj_tac
        >- simp[abi_decoder_phi_emit_op] >> rpt gen_tac) >>
  (ho_match_mp_tac abi_decoder_phi_ignore_bind >> conj_tac
   >- simp[cj 1 abi_decoder_phi_mutual] >> simp[])
QED

Theorem ctor_alloc_buffer_phi[local]:
  !n st. abi_decoder_phi st (SND (compile_alloc_buffer n st))
Proof
  simp[compile_alloc_buffer_def] >> rpt gen_tac >>
  ho_match_mp_tac abi_decoder_phi_bind >> conj_tac
  >- simp[abi_decoder_phi_emit_op] >> simp[abi_decoder_phi_return]
QED

Theorem ctor_registration_phi:
  !args ce off data_size st.
    abi_decoder_phi st
      (SND (compile_register_constructor_args ce args off data_size st))
Proof
  Induct >- simp[compile_register_constructor_args_def, abi_decoder_phi_return] >>
  PairCases >> rpt gen_tac >> simp[Once compile_register_constructor_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  Cases_on `var_location_memory_size x` >> simp[] >>
  ho_match_mp_tac abi_decoder_phi_bind >> conj_tac
  >- simp[ctor_alloc_buffer_phi] >> rpt gen_tac >>
  ho_match_mp_tac abi_decoder_phi_bind >> conj_tac
  >- simp[abi_decoder_phi_return] >> rpt gen_tac >>
  ho_match_mp_tac abi_decoder_phi_ignore_bind >> conj_tac
  >- simp[ctor_decode_args_phi] >> simp[]
QED

Theorem ctor_phi_at_phase_start[local]:
  cs_extends st last /\ abi_decoder_phi st last /\
  phi_prefix_length st.cs_current_insts = 0 /\ fn_has_code st last func /\
  (!bb. lookup_block last.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  !bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  `abi_decoder_phi_safe st.cs_blocks st` by
    (simp[abi_decoder_phi_safe_def] >> qexists `[]` >> simp[]) >>
  `abi_decoder_phi_safe st.cs_blocks last` by
    metis_tac[abi_decoder_phi_def] >>
  gvs[cs_extends_def, abi_decoder_phi_safe_def] >>
  Cases_on `new = []` >> gvs[] >>
  `emitted_blocks st last = new` by
    (irule emitted_blocks_append >> simp[]) >>
  gvs[fn_has_code_def, EVERY_MEM] >> rpt strip_tac >>
  `MEM (LAST (emitted_blocks st last)) (emitted_blocks st last)` by
    simp[rich_listTheory.MEM_LAST_NOT_NIL] >>
  metis_tac[optionTheory.SOME_11]
QED

Theorem ctor_phase_blocks_between[local]:
  cs_extends first middle /\ cs_extends middle last /\
  first.cs_blocks = last.cs_blocks ==>
  middle.cs_blocks = last.cs_blocks
Proof
  rw[cs_extends_def] >>
  `LENGTH first.cs_blocks = LENGTH new' + (LENGTH new + LENGTH first.cs_blocks)` by
    metis_tac[LENGTH_APPEND] >>
  `LENGTH new = 0 /\ LENGTH new' = 0` by decide_tac >> gvs[]
QED

Theorem ctor_registration_phi_phases:
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_decode_args ce args off DLOAD hi 0 allocated = ((),decoded) /\
  compile_register_constructor_args ce rest next_off data_size decoded = (ce',last) /\
  fn_has_code st last func /\
  (st.cs_blocks = last.cs_blocks \/
    !bb. lookup_block last.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  (allocated.cs_blocks = decoded.cs_blocks \/
    !bb. lookup_block decoded.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  (decoded.cs_blocks = last.cs_blocks \/
    !bb. lookup_block last.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >>
  `cs_extends st allocated` by
    metis_tac[cs_appends_abi_alloc_buffer, cs_appends_def] >>
  `cs_extends allocated decoded` by
    metis_tac[cs_appends_decode_args, cs_appends_def] >>
  `cs_extends decoded last` by metis_tac[ctor_registration_extends] >>
  `cs_extends st decoded` by metis_tac[cs_extends_trans] >>
  `st.cs_blocks = allocated.cs_blocks` by
    gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
        comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  `fn_has_code decoded last func` by
    metis_tac[ctor_registration_code_phases] >>
  `abi_decoder_phi allocated decoded` by
    metis_tac[ctor_decode_args_phi, pairTheory.SND] >>
  `abi_decoder_phi decoded last` by
    metis_tac[ctor_registration_phi, pairTheory.SND] >>
  reverse conj_tac
  >- metis_tac[ctor_phase_blocks_between] >>
  Cases_on `allocated.cs_blocks = decoded.cs_blocks` >> simp[] >>
  rpt strip_tac >> irule ctor_phi_at_phase_start >>
  qexistsl [`func`, `last`, `decoded`] >>
  simp[] >>
  metis_tac[abi_decoder_phi_def, ctor_phase_blocks_between]
QED

Theorem ctor_decode_buffer_old_prefix:
  !dst src hi ce env ty tv av v st st' ctx func site initial sb d.
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) st = ((),st') /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  abi_decoder_metadata ce env ty tv
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\
  sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
    initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
  (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
  fresh_vars_wrt st initial /\ fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  (st.cs_blocks = st'.cs_blocks \/
    !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
  (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual.
    val_in_memory tv v d actual.vs_memory /\
    abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
      [(d,type_memory_bytes ce ty)] initial actual /\
    ctor_actual_scratch func (frag_ids st st') 0 initial.vs_alloca_next actual /\
    initial.vs_alloca_next <= actual.vs_alloca_next /\
    alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
    fresh_vars_wrt st' actual /\
    actual.vs_data_section = initial.vs_data_section /\
    actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
    (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
      lookup_var x actual = SOME w) /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial actual
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `st.cs_next_var <= st'.cs_next_var` by
    (drule abi_decoder_variable_counter >> simp[]) >>
  `fresh_vars_wrt st' initial` by
    (irule fresh_vars_wrt_mono >> qexists `st` >> simp[GREATER_EQ]) >>
  `ctor_actual_scratch func (frag_ids st st') 0 initial.vs_alloca_next initial` by
    (simp_tac bool_ss [ctor_actual_scratch_def, frag_ids_def, GSPECIFICATION] >>
     rpt strip_tac >> res_tac >> gvs[]) >>
  drule (BETA_RULE ctor_actual_coherent_run) >>
  disch_then (drule_at Any) >>
  disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dst initial = _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  simp_tac bool_ss [LESS_EQ_REFL, SUBSET_REFL] >>
  disch_then (qspecl_then [`ctx`, `site`, `d`] mp_tac) >>
  simp_tac bool_ss [ADD, ZERO_LESS_EQ, LESS_EQ_REFL] >>
  disch_then drule_all >> strip_tac >>
  qexists `actual` >> asm_rewrite_tac[]
QED

Theorem ctor_scratch_new_allocations:
  abi_encoder_registered_effect (ctor_actual_sites func ids) outs initial actual /\
  ctor_actual_scratch func ids 0 initial.vs_alloca_next actual /\
  FLOOKUP actual.vs_allocas aid = SOME (b,sz) /\
  FLOOKUP initial.vs_allocas aid = NONE ==>
  initial.vs_alloca_next <= b
Proof
  strip_tac >>
  `aid IN ctor_actual_sites func ids` by
    (gvs[abi_encoder_registered_effect_def] >>
     spose_not_then assume_tac >> res_tac >> gvs[]) >>
  drule_all ctor_actual_sites_scratch >> simp[regions_disjoint_def]
QED

Theorem ctor_scratch_old_window:
  abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,n)] initial actual /\
  ctor_actual_scratch func ids 0 initial.vs_alloca_next actual /\
  p+k <= initial.vs_alloca_next /\ regions_disjoint (p,k) (d,n) ==>
  mem_bytes_at p k actual.vs_memory = mem_bytes_at p k initial.vs_memory
Proof
  strip_tac >> irule ctor_actual_registered_window >>
  qexistsl [`ctor_actual_sites func ids`, `[(d,n)]`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all ctor_actual_sites_scratch >> strip_tac >>
      irule ctor_actual_region_contained >>
      qexistsl [`0`, `initial.vs_alloca_next`] >> simp[]) >>
  rpt strip_tac >> gvs[regions_disjoint_def] >> decide_tac
QED

Theorem ctor_live_region_bound[local]:
  local_ptrs_rel func ce scopes initial /\
  local_region ce scopes initial name b sz ==>
  b+sz <= initial.vs_alloca_next
Proof
  rw[local_region_def, local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[]
QED

Theorem ctor_scratch_local_ptrs_frame:
  local_ptrs_rel func ce scopes initial /\
  (!name entry p sz.
    lookup_scopes name scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p actual = lookup_var p initial) /\
  abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,n)] initial actual /\
  ctor_actual_scratch func ids 0 initial.vs_alloca_next actual /\
  initial.vs_alloca_next <= actual.vs_alloca_next /\
  (!name b sz. local_region ce scopes initial name b sz ==>
    regions_disjoint (b,sz) (d,n)) ==>
  local_ptrs_rel func ce scopes actual
Proof
  strip_tac >> irule local_ptrs_rel_mem_agree >> qexists `initial` >> simp[] >>
  rpt conj_tac
  >- (rpt strip_tac >> irule EQ_SYM >> irule ctor_scratch_old_window >>
      conj_tac >- metis_tac[ctor_live_region_bound] >>
      qexistsl [`d`, `func`, `ids`, `n`] >> simp[] >> metis_tac[])
  >- metis_tac[]
  >- (rpt strip_tac >> drule_all ctor_scratch_new_allocations >> simp[]) >>
  rpt strip_tac >> drule_all abi_encoder_registered_effect_allocated >> simp[]
QED

Theorem ctor_alloc_buffer_credit:
  compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
  n < dimword (:256) /\ alloca_frontier_inv ctx func site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP initial.vs_allocas st.cs_next_id = NONE ==>
  initial.vs_alloca_next + n < dimword (:256)
Proof
  strip_tac >> drule_all entry_alloc_buffer_inst >> strip_tac >>
  drule_at (Pat `MEM _ _`) actual_alloca_frontier_credit >>
  simp[mk_inst_def, FLOOKUP_DEF, alloca_size_def, w2n_n2w] >>
  disch_then (qspecl_then [`ctx`, `site`, `initial`] mp_tac) >>
  gvs[FLOOKUP_DEF] >> decide_tac
QED

Theorem ctor_alloc_buffer_run:
  compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
  n < dimword (:256) /\ alloca_inv initial /\
  alloca_frontier_inv ctx func site initial /\ fn_inst_ids_distinct func /\
  unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?a. a = (update_var (STRING #"%" (toString st.cs_next_var))
      (n2w initial.vs_alloca_next)
      (initial with <| vs_allocas := initial.vs_allocas |+
        (st.cs_next_id,(initial.vs_alloca_next,n));
        vs_alloca_next := initial.vs_alloca_next+n |>))
      with vs_inst_idx := LENGTH sa.cs_current_insts /\
    alloca_inv a /\ alloca_frontier_inv ctx func site a /\
    initial.vs_alloca_next+n < dimword (:256) /\
    ~a.vs_halted /\ a.vs_current_bb = sa.cs_current_bb /\
    abi_decode_sim ctx func initial a
Proof
  strip_tac >>
  `initial.vs_alloca_next+n < dimword (:256)` by
    (irule ctor_alloc_buffer_credit >> metis_tac[]) >>
  qabbrev_tac `raw = update_var (STRING #"%" (toString st.cs_next_var))
    (n2w initial.vs_alloca_next)
    (initial with <| vs_allocas := initial.vs_allocas |+
      (st.cs_next_id,(initial.vs_alloca_next,n));
      vs_alloca_next := initial.vs_alloca_next+n |>)` >>
  `exec_alloca (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
     [STRING #"%" (toString st.cs_next_var)]) initial (n2w n : bytes32) = OK raw` by
    simp[exec_alloca_def, mk_inst_def, w2n_n2w, Abbr `raw`] >>
  `alloca_inv raw` by metis_tac[alloca_inv_exec_alloca] >>
  `alloca_frontier_inv ctx func site raw` by
    (irule actual_alloca_frontier_preserved >>
     conj_tac >- metis_tac[ctor_actual_function_ids] >>
     qexistsl [`mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString st.cs_next_var)]`, `initial`, `site`] >>
     drule_all entry_alloc_buffer_inst >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
                      combinTheory.K_THM, opcode_case_def] >>
     fs[mk_inst_def]) >>
  `frag_exec ctx st sa (\u. u = initial)
     (\u. u = raw with vs_inst_idx := LENGTH sa.cs_current_insts) (\r. F)` by
    (irule compile_alloc_buffer_fresh_frag >> qexistsl [`buf`, `n`] >>
     simp[Abbr `raw`]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  simp[] >> strip_tac >>
  simp[abi_decode_sim_def] >> metis_tac[]
QED

Theorem ctor_alloc_buffer_state_props[local]:
  compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
  n < dimword (:256) /\ initial.vs_alloca_next < dimword (:256) /\
  local_ptrs_rel func ce scopes initial /\ fresh_vars_wrt st initial /\
  (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
  a = (update_var (STRING #"%" (toString st.cs_next_var))
      (n2w initial.vs_alloca_next)
      (initial with <| vs_allocas := initial.vs_allocas |+
        (st.cs_next_id,(initial.vs_alloca_next,n));
        vs_alloca_next := initial.vs_alloca_next+n |>))
      with vs_inst_idx := LENGTH sa.cs_current_insts ==>
  buf.buf_operand = Var (STRING #"%" (toString st.cs_next_var)) /\
  local_ptrs_rel func ce scopes a /\
  local_backed func (STRING #"%" (toString st.cs_next_var)) a initial.vs_alloca_next n /\
  fresh_vars_wrt sa a /\ not_fresh_at sa (STRING #"%" (toString st.cs_next_var)) /\
  (!aid. sa.cs_next_id <= aid ==> FLOOKUP a.vs_allocas aid = NONE) /\
  (!name b sz. local_region ce scopes a name b sz ==>
    compileEnv$regions_disjoint initial.vs_alloca_next n b sz) /\
  (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
    lookup_var x a = SOME w) /\
  abi_encoder_registered_effect (frag_ids st sa) [] initial a
Proof
  strip_tac >>
  `not_scope_ptr ce scopes (STRING #"%" (toString st.cs_next_var))` by
    (irule local_ptrs_rel_fresh_not_scope_ptr >>
     qexistsl [`func`, `initial`, `st`] >> simp[GREATER_EQ]) >>
  `exec_alloca (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
     [STRING #"%" (toString st.cs_next_var)]) initial (n2w n : bytes32) =
     OK (a with vs_inst_idx := initial.vs_inst_idx)` by
    gvs[exec_alloca_def, mk_inst_def, update_var_def, w2n_n2w,
        venom_state_component_equality] >>
  drule local_ptrs_rel_exec_alloca_fresh >> simp[mk_inst_def] >>
  disch_then (qspecl_then [`func`, `ce`, `scopes`] mp_tac) >>
  simp[local_ptrs_rel_inst_idx] >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >> simp[] >>
  conj_tac
  >- (simp[local_backed_def] >> disj1_tac >>
      qexists `mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString st.cs_next_var)]` >>
      drule_all entry_alloc_buffer_inst >> gvs[mk_inst_def]) >>
  conj_tac
  >- (fs[fresh_vars_wrt_def, update_var_def, GREATER_EQ] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac
  >- (simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
      IF_CASES_TAC >> gvs[] >> first_x_assum irule >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!name b sz. local_region _ _ _ _ _ _ ==> _` mp_tac >>
      fs[local_region_def, lookup_var_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      IF_CASES_TAC >> gvs[lookup_var_def]) >>
  simp[abi_encoder_registered_effect_def, frag_ids_def, GSPECIFICATION,
       update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[] >>
  `FLOOKUP initial.vs_allocas st.cs_next_id = NONE` by simp[] >> gvs[]
QED

Theorem ctor_alloc_buffer_actual:
  compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
  n < dimword (:256) /\ local_ptrs_rel func ce scopes initial /\
  fresh_vars_wrt st initial /\ alloca_inv initial /\
  alloca_frontier_inv ctx func site initial /\ fn_inst_ids_distinct func /\
  unit_alloca_budget ctx < dimword (:256) /\
  (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?a. buf.buf_operand = Var (STRING #"%" (toString st.cs_next_var)) /\
    local_ptrs_rel func ce scopes a /\
    lookup_var (STRING #"%" (toString st.cs_next_var)) a =
      SOME (n2w initial.vs_alloca_next) /\
    local_backed func (STRING #"%" (toString st.cs_next_var)) a initial.vs_alloca_next n /\
    FLOOKUP a.vs_allocas st.cs_next_id = SOME (initial.vs_alloca_next,n) /\
    a.vs_alloca_next = initial.vs_alloca_next+n /\
    a.vs_alloca_next < dimword (:256) /\
    alloca_inv a /\ alloca_frontier_inv ctx func site a /\
    fresh_vars_wrt sa a /\ not_fresh_at sa (STRING #"%" (toString st.cs_next_var)) /\
    (!aid. sa.cs_next_id <= aid ==> FLOOKUP a.vs_allocas aid = NONE) /\
    (!name b sz. local_region ce scopes a name b sz ==>
      compileEnv$regions_disjoint initial.vs_alloca_next n b sz) /\
    a.vs_memory = initial.vs_memory /\
    a.vs_data_section = initial.vs_data_section /\
    a.vs_call_ctx = initial.vs_call_ctx /\ a.vs_labels = initial.vs_labels /\
    (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
      lookup_var x a = SOME w) /\
    abi_encoder_registered_effect (frag_ids st sa) [] initial a /\
    ~a.vs_halted /\ a.vs_current_bb = sa.cs_current_bb /\
    a.vs_inst_idx = LENGTH sa.cs_current_insts /\
    abi_decode_sim ctx func initial a
Proof
  strip_tac >>
  `FLOOKUP initial.vs_allocas st.cs_next_id = NONE` by simp[] >>
  drule_all ctor_alloc_buffer_run >> strip_tac >>
  `initial.vs_alloca_next < dimword (:256)` by decide_tac >>
  drule_all ctor_alloc_buffer_state_props >> strip_tac >>
  qexists `a` >> asm_rewrite_tac[] >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem ctor_registered_output_absorb:
  abi_encoder_registered_effect ids [(d,n)] initial actual /\
  ids SUBSET larger /\ aid IN larger /\
  FLOOKUP actual.vs_allocas aid = SOME (d,n) ==>
  abi_encoder_registered_effect larger [] initial actual
Proof
  simp_tac (srw_ss()) [abi_encoder_registered_effect_def, SUBSET_DEF, EVERY_DEF] >>
  strip_tac >> asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >> conj_tac >> metis_tac[]
QED

Theorem ctor_singleton_decode_code:
  !ptr. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ptr) (type_memory_bytes ce ty)) ==>
  compile_decode_args ce [build_positional_arg ce (name,ty)] off
      DLOAD (Lit (n2w data_size)) 0 =
  do static_src <- emit_op ADD [Lit 0w; Lit (n2w off)];
     src <- (if ~is_word_type ty /\ is_abi_dynamic ce.ce_struct_fields ty then
       do offset_val <- emit_op DLOAD [static_src];
          emit_op ADD [Lit 0w; offset_val]
       od else comp_return static_src);
     compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit 0w) (Lit (n2w data_size))
       (type_to_abi_dec_info ce.ce_struct_fields ce ty)
  od
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_word_type ty`
  >- (`?clamp. type_to_abi_dec_info ce.ce_struct_fields ce ty = DecPrimWord clamp` by
        metis_tac[ctor_arg_word_descriptor] >>
      simp[build_positional_arg_def, compile_decode_args_def,
        var_location_decode_operand_def, compile_abi_decode_to_buf_def,
        compile_abi_decode_static_def,
        abiDecoderRangeTheory.compile_abi_dec_addr_zero,
        compile_abi_decode_range_check_def, FUN_EQ_THM,
        comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
      pairarg_tac >> simp[] >> pairarg_tac >> simp[]) >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty` >>
  simp[build_positional_arg_def, compile_decode_args_def,
    var_location_decode_operand_def, FUN_EQ_THM,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem ctor_singleton_decode_phases:
  !ptr. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ptr) (type_memory_bytes ce ty)) /\
  compile_decode_args ce [build_positional_arg ce (name,ty)] off
    DLOAD (Lit (n2w data_size)) 0 st = ((),last) ==>
  ?static_src first src middle.
    emit_op ADD [Lit 0w; Lit (n2w off)] st = (static_src,first) /\
    ((~(~is_word_type ty /\ is_abi_dynamic ce.ce_struct_fields ty) /\
       src = static_src /\ middle = first) \/
     (?offset_val second. ~is_word_type ty /\ is_abi_dynamic ce.ce_struct_fields ty /\
       emit_op DLOAD [static_src] first = (offset_val,second) /\
       emit_op ADD [Lit 0w; offset_val] second = (src,middle))) /\
    compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit 0w) (Lit (n2w data_size))
      (type_to_abi_dec_info ce.ce_struct_fields ce ty) middle = ((),last)
Proof
  rpt gen_tac >> strip_tac >> drule ctor_singleton_decode_code >>
  disch_then (fn th => fs[th, comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  pairarg_tac >> gvs[] >>
  Cases_on `~is_word_type ty /\ is_abi_dynamic ce.ce_struct_fields ty` >> gvs[] >>
  fs[comp_bind_def, comp_return_def] >> rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem ctor_emit_prefix_shape[local]:
  emit_op opc ops st = (out,middle) ==>
  cs_extends st middle /\ middle.cs_blocks = st.cs_blocks /\
  middle.cs_current_bb = st.cs_current_bb /\
  middle.cs_next_id = st.cs_next_id+1 /\ middle.cs_next_var = st.cs_next_var+1
Proof
  strip_tac >>
  `isPREFIX st.cs_current_insts middle.cs_current_insts` by
    metis_tac[emit_op_prefix] >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
      fresh_var_def, fresh_id_def, comp_return_def, emit_def] >>
  irule cs_extends_same_block >> simp[]
QED

Theorem ctor_prefix_sequence_reach[local]:
  inst_extends st middle /\ middle.cs_blocks = st.cs_blocks /\
  middle.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st middle) /\
  run_inst_seq (emitted_insts st middle) initial = OK raw /\
  fn_has_code st middle func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_decode_sim ctx func initial (raw with vs_inst_idx := LENGTH middle.cs_current_insts)
Proof
  strip_tac >>
  `frag_exec ctx st middle (\s. s = initial)
    (\t. t = raw with vs_inst_idx := LENGTH middle.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >>
     fs[inst_extends_def] >> rpt strip_tac >> simp[] >>
     qexists `raw` >> simp[]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[]
QED

Theorem ctor_register_prefix_finish[local]:
  emit_op opc ops st = (out,middle) /\ opc <> INVOKE /\ ~is_terminator opc /\
  run_inst_seq (emitted_insts st middle) initial =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) w initial) /\
  fresh_vars_wrt st initial /\ fn_has_code st middle func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared.
    eval_operand out prepared = SOME w /\ fresh_vars_wrt middle prepared /\
    prepared with <| vs_vars := initial.vs_vars; vs_inst_idx := initial.vs_inst_idx |> = initial /\
    abi_encoder_registered_effect {} [] initial prepared /\
    (!x v. not_fresh_at st x /\ lookup_var x initial = SOME v ==>
      lookup_var x prepared = SOME v) /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
    abi_decode_sim ctx func initial prepared
Proof
  strip_tac >> drule ctor_emit_prefix_shape >> strip_tac >>
  `inst_extends st middle` by metis_tac[inst_extends_emit_op] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st middle)` by
    (drule emitted_insts_emit_op >> simp[mk_inst_def]) >>
  drule_all ctor_prefix_sequence_reach >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexists `update_var (STRING #"%" (toString st.cs_next_var)) w initial
    with vs_inst_idx := LENGTH middle.cs_current_insts` >>
  asm_rewrite_tac[] >>
  `out = Var (STRING #"%" (toString st.cs_next_var))` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
      fresh_var_def, fresh_id_def, comp_return_def, emit_def] >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       venom_state_component_equality, abi_encoder_registered_effect_def] >>
  conj_tac
  >- (fs[fresh_vars_wrt_def, GREATER_EQ] >> rpt strip_tac >>
      first_x_assum irule >> decide_tac) >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[not_fresh_at_def]
QED

Theorem ctor_add_prefix_actual[local]:
  emit_op ADD [lhs;rhs] st = (out,middle) /\
  eval_operand lhs initial = SOME a /\ eval_operand rhs initial = SOME b /\
  fresh_vars_wrt st initial /\ fn_has_code st middle func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared.
    eval_operand out prepared = SOME (a+b) /\ fresh_vars_wrt middle prepared /\
    prepared with <| vs_vars := initial.vs_vars; vs_inst_idx := initial.vs_inst_idx |> = initial /\
    abi_encoder_registered_effect {} [] initial prepared /\
    (!x v. not_fresh_at st x /\ lookup_var x initial = SOME v ==>
      lookup_var x prepared = SOME v) /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
    abi_decode_sim ctx func initial prepared
Proof
  strip_tac >> drule ctor_emit_prefix_shape >> strip_tac >>
  `fresh_vars_wrt middle initial` by
    (irule fresh_vars_wrt_mono >> qexists `st` >> simp[GREATER_EQ]) >>
  drule abi_decoder_binary_reentry >>
  disch_then (qspecl_then [`initial`, `middle`] mp_tac) >>
  simp[] >> strip_tac >>
  drule ctor_register_prefix_finish >>
  simp[is_terminator_def] >> disch_then irule >> simp[]
QED

Theorem ctor_dload_prefix_actual[local]:
  emit_op DLOAD [src] st = (out,middle) /\
  eval_operand src initial = SOME p /\
  fresh_vars_wrt st initial /\ fn_has_code st middle func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared.
    eval_operand out prepared = SOME (abi_decode_load DLOAD p initial) /\
    fresh_vars_wrt middle prepared /\
    prepared with <| vs_vars := initial.vs_vars; vs_inst_idx := initial.vs_inst_idx |> = initial /\
    abi_encoder_registered_effect {} [] initial prepared /\
    (!x v. not_fresh_at st x /\ lookup_var x initial = SOME v ==>
      lookup_var x prepared = SOME v) /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
    abi_decode_sim ctx func initial prepared
Proof
  strip_tac >> drule ctor_emit_prefix_shape >> strip_tac >>
  `fresh_vars_wrt middle initial` by
    (irule fresh_vars_wrt_mono >> qexists `st` >> simp[GREATER_EQ]) >>
  drule abi_decoder_read_reentry >>
  disch_then (qspecl_then [`initial`, `p`, `middle`] mp_tac) >>
  simp[abi_decode_source_opcode_def] >> strip_tac >>
  drule ctor_register_prefix_finish >>
  simp[is_terminator_def] >> disch_then irule >> simp[]
QED

Theorem ctor_prefix_decoder_code_phase[local]:
  cs_extends st middle /\ middle.cs_blocks = st.cs_blocks /\
  abi_decode_source_opcode opc /\ st.cs_next_id <= middle.cs_next_id /\
  compile_abi_decode_to_buf dst src opc (Lit 0w) hi di middle = ((),end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  fn_has_code st middle func /\ fn_has_code middle end_st func /\
  middle.cs_next_var <= end_st.cs_next_var /\
  middle.cs_next_id <= end_st.cs_next_id /\
  frag_ids middle end_st SUBSET frag_ids st end_st /\
  (middle.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >>
  drule cs_extends_abi_decode >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule abi_decoder_variable_counter >> strip_tac >>
  drule abi_decoder_to_buf_code >>
  simp_tac bool_ss [abi_decoder_code_def] >> strip_tac >>
  simp[frag_ids_def, SUBSET_DEF] >> decide_tac
QED

Theorem ctor_canonical_member_split[local]:
  atys = pre ++ aty::post /\ avs = pvs ++ av::rest /\ i = LENGTH pre /\
  LENGTH pre = LENGTH pvs /\ has_types atys avs /\
  encoded = enc (Tuple atys) (ListV avs) /\
  mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
  LENGTH encoded < dimword (:256) ==>
  has_type (EL i atys) (EL i avs) /\
  mem_bytes_at (abi_tuple_child_offset atys avs i)
    (LENGTH (enc (EL i atys) (EL i avs))) initial.vs_data_section =
      enc (EL i atys) (EL i avs) /\
  abi_tuple_child_offset atys avs i + LENGTH (enc (EL i atys) (EL i avs)) <= LENGTH encoded /\
  (is_dynamic (EL i atys) ==>
    abi_decode_load DLOAD (n2w (SUM (MAP abi_member_head_size (TAKE i atys))) : bytes32) initial =
      n2w (abi_tuple_child_offset atys avs i)) /\
  (~is_dynamic (EL i atys) ==>
    abi_tuple_child_offset atys avs i = SUM (MAP abi_member_head_size (TAKE i atys)))
Proof
  strip_tac >>
  `mem_bytes_at 0 (LENGTH encoded) (abi_decode_source DLOAD initial) = encoded` by
    gvs[abi_decode_source_def, Excl "enc_def"] >>
  qpat_x_assum `atys = _` SUBST_ALL_TAC >>
  qpat_x_assum `avs = _` SUBST_ALL_TAC >>
  qpat_x_assum `encoded = _` SUBST_ALL_TAC >>
  qpat_x_assum `i = _` SUBST_ALL_TAC >>
  drule_all abi_tuple_child_offset_source >>
  simp_tac bool_ss [ADD_CLAUSES] >> strip_tac >>
  drule_all abi_tuple_child_offset_ranges >> strip_tac >>
  drule abi_decoder_canonical_member_inputs >>
  disch_then (qspecl_then [`0`, `initial`, `DLOAD`] mp_tac) >>
  asm_simp_tac bool_ss [ADD_CLAUSES] >> strip_tac >>
  `EL (LENGTH pre) (pre ++ aty::post) = aty /\
   EL (LENGTH pre) (pvs ++ av::rest) = av /\
   TAKE (LENGTH pre) (pre ++ aty::post) = pre` by
    (conj_tac >- simp_tac (srw_ss()) [EL_LENGTH_APPEND] >>
     conj_tac >- (qpat_assum `LENGTH pre = LENGTH pvs`
       (fn th => pure_rewrite_tac[th]) >> simp_tac (srw_ss()) [EL_LENGTH_APPEND]) >>
     pure_rewrite_tac [TAKE_LENGTH_APPEND] >> REFL_TAC) >>
  qpat_assum `LENGTH pre = LENGTH pvs`
    (fn th => pure_rewrite_tac [GSYM th] >>
      rule_assum_tac (PURE_REWRITE_RULE [GSYM th])) >>
  pure_asm_rewrite_tac [] >>
  Cases_on `is_dynamic aty` >>
  fs[abi_decode_source_def, Excl "enc_def", Excl "APPEND_ASSOC"] >>
  metis_tac[APPEND, APPEND_ASSOC]
QED

Theorem ctor_canonical_member_source[local]:
  i < LENGTH atys /\ LENGTH avs = LENGTH atys /\ has_types atys avs /\
  encoded = enc (Tuple atys) (ListV avs) /\
  mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
  LENGTH encoded < dimword (:256) ==>
  has_type (EL i atys) (EL i avs) /\
  mem_bytes_at (abi_tuple_child_offset atys avs i)
    (LENGTH (enc (EL i atys) (EL i avs))) initial.vs_data_section =
      enc (EL i atys) (EL i avs) /\
  abi_tuple_child_offset atys avs i + LENGTH (enc (EL i atys) (EL i avs)) <= LENGTH encoded /\
  (is_dynamic (EL i atys) ==>
    abi_decode_load DLOAD (n2w (SUM (MAP abi_member_head_size (TAKE i atys))) : bytes32) initial =
      n2w (abi_tuple_child_offset atys avs i)) /\
  (~is_dynamic (EL i atys) ==>
    abi_tuple_child_offset atys avs i = SUM (MAP abi_member_head_size (TAKE i atys)))
Proof
  strip_tac >> irule ctor_canonical_member_split >>
  asm_rewrite_tac[] >>
  qexistsl [`EL i atys`, `EL i avs`, `DROP (SUC i) atys`,
    `TAKE i atys`, `TAKE i avs`, `DROP (SUC i) avs`] >>
  conj_tac
  >- (mp_tac (Q.ISPEC `avs:abi_value list` (Q.SPEC `i:num` TAKE_DROP_SUC)) >>
      asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  conj_tac
  >- (mp_tac (Q.ISPEC `atys:abi_type list` (Q.SPEC `i:num` TAKE_DROP_SUC)) >>
      asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  simp[]
QED

Theorem ctor_prefix_reset_trans[local]:
  t with <| vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx |> = s /\
  u with <| vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx |> = t ==>
  u with <| vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx |> = s
Proof
  simp[venom_state_component_equality]
QED

Theorem ctor_prefix_reset_load[local]:
  t with <| vs_vars := s.vs_vars; vs_inst_idx := k |> = s ==>
  abi_decode_load DLOAD p t = abi_decode_load DLOAD p s
Proof
  simp[venom_state_component_equality, abi_decode_load_def, abi_decode_source_def]
QED

Theorem ctor_dynamic_address_prefix[local]:
  emit_op ADD [Lit 0w; Lit (n2w off)] st = (head,first) /\
  emit_op DLOAD [head] first = (offset_val,second) /\
  emit_op ADD [Lit 0w; offset_val] second = (src,middle) /\
  fn_has_code st middle func /\ fresh_vars_wrt st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared.
    eval_operand src prepared = SOME (abi_decode_load DLOAD (n2w off : bytes32) initial) /\
    fresh_vars_wrt middle prepared /\
    prepared with <| vs_vars := initial.vs_vars; vs_inst_idx := initial.vs_inst_idx |> = initial /\
    abi_encoder_registered_effect {} [] initial prepared /\
    (!x v. not_fresh_at st x /\ lookup_var x initial = SOME v ==>
      lookup_var x prepared = SOME v) /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
    abi_decode_sim ctx func initial prepared
Proof
  strip_tac >>
  `cs_extends st first /\ cs_extends first second /\ cs_extends second middle /\
   first.cs_next_var = st.cs_next_var+1 /\
   second.cs_next_var = first.cs_next_var+1` by
    metis_tac[ctor_emit_prefix_shape] >>
  `cs_extends first middle` by metis_tac[cs_extends_trans] >>
  `fn_has_code st first func /\ fn_has_code first second func /\
   fn_has_code second middle func` by metis_tac[fn_has_code_split] >>
  qpat_assum `emit_op ADD _ st = _`
    (mp_then Any mp_tac ctor_add_prefix_actual) >>
  disch_then (qspecl_then [`initial`, `func`, `ctx`] mp_tac) >>
  simp[eval_operand_def] >> strip_tac >>
  rename1 `eval_operand head p1 = _` >>
  `eval_operand head p1 = SOME (n2w off)` by fs[] >>
  drule_all ctor_dload_prefix_actual >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `eval_operand offset_val p2 = _` >>
  qpat_assum `emit_op ADD _ second = _`
    (mp_then Any mp_tac ctor_add_prefix_actual) >>
  disch_then (qspecl_then [`p2`, `func`, `ctx`] mp_tac) >>
  simp[eval_operand_def] >> strip_tac >>
  rename1 `eval_operand src p3 = _` >>
  `abi_decode_load DLOAD (n2w off : bytes32) p1 = abi_decode_load DLOAD (n2w off : bytes32) initial` by
    (irule ctor_prefix_reset_load >> goal_assum (drule_at Any)) >>
  qexists `p3` >> simp[] >>
  conj_tac
  >- (metis_tac[ctor_prefix_reset_trans]) >>
  conj_tac
  >- metis_tac[abi_encoder_registered_effect_trans] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at first x /\ not_fresh_at second x` by
        (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
      metis_tac[]) >>
  metis_tac[abi_decode_sim_trans]
QED

Theorem ctor_singleton_address_prefix[local]:
  !ptr. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ptr) (type_memory_bytes ce ty)) /\
  compile_decode_args ce [build_positional_arg ce (name,ty)] off
    DLOAD (Lit (n2w data_size)) 0 st = ((),last) /\
  fresh_vars_wrt st initial /\ fn_has_code st last func /\
  (st.cs_blocks = last.cs_blocks \/
    !bb. lookup_block last.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?src middle prepared.
    compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit 0w) (Lit (n2w data_size))
      (type_to_abi_dec_info ce.ce_struct_fields ce ty) middle = ((),last) /\
    eval_operand src prepared = SOME
      (if ~is_word_type ty /\ is_abi_dynamic ce.ce_struct_fields ty
       then abi_decode_load DLOAD (n2w off : bytes32) initial else n2w off) /\
    fresh_vars_wrt middle prepared /\ cs_extends st middle /\
    middle.cs_blocks = st.cs_blocks /\
    st.cs_next_var <= middle.cs_next_var /\ st.cs_next_id <= middle.cs_next_id /\
    fn_has_code middle last func /\
    (middle.cs_blocks = last.cs_blocks \/
      !bb. lookup_block last.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    frag_ids middle last SUBSET frag_ids st last /\
    prepared with <| vs_vars := initial.vs_vars; vs_inst_idx := initial.vs_inst_idx |> = initial /\
    abi_encoder_registered_effect {} [] initial prepared /\
    (!x v. not_fresh_at st x /\ lookup_var x initial = SOME v ==>
      lookup_var x prepared = SOME v) /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
    abi_decode_sim ctx func initial prepared
Proof
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all ctor_singleton_decode_phases >> strip_tac
  >- (qpat_x_assum `src = static_src` SUBST_ALL_TAC >>
      qpat_x_assum `middle = first` SUBST_ALL_TAC >>
      drule ctor_emit_prefix_shape >> strip_tac >>
      `st.cs_next_id <= first.cs_next_id` by decide_tac >>
      drule_all ctor_prefix_decoder_code_phase >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      drule ctor_add_prefix_actual >>
      disch_then (qspecl_then [`initial`, `func`, `ctx`] mp_tac) >>
      simp[eval_operand_def] >> strip_tac >>
      qexistsl [`static_src`, `first`, `prepared`] >> simp[]) >>
  `cs_extends st middle /\ middle.cs_blocks = st.cs_blocks /\
   st.cs_next_var <= middle.cs_next_var /\ st.cs_next_id <= middle.cs_next_id` by
    (imp_res_tac ctor_emit_prefix_shape >>
     conj_tac >- metis_tac[cs_extends_trans] >> simp[]) >>
  drule_all ctor_prefix_decoder_code_phase >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ctor_dynamic_address_prefix >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl [`src`, `middle`, `prepared`] >> simp[]
QED

Theorem ctor_word_type_static[local]:
  is_word_type ty ==> ~is_abi_dynamic sf ty
Proof
  Cases_on `ty` >> simp[is_word_type_def, is_abi_dynamic_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_word_type_def, is_abi_dynamic_def] >>
  rename1 `BytesT b` >> Cases_on `b` >> simp[is_word_type_def, is_abi_dynamic_def]
QED

Theorem ctor_eval_operand_not_fresh[local]:
  eval_operand op s = SOME w /\ fresh_vars_wrt st s ==>
  !x. op = Var x ==> not_fresh_at st x
Proof
  simp[eval_operand_def, not_fresh_at_def, fresh_vars_wrt_def] >>
  rpt strip_tac >> fs[eval_operand_def, lookup_var_def, GREATER_EQ, FLOOKUP_DEF] >>
  metis_tac[]
QED

Theorem ctor_canonical_singleton_prefix[local]:
  !ptr. i < LENGTH atys /\ LENGTH avs = LENGTH atys /\
  EL i atys = vyper_to_abi_type env ty /\ has_types atys avs /\
  encoded = enc (Tuple atys) (ListV avs) /\
  mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
  LENGTH encoded < dimword (:256) /\
  (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
  off = SUM (MAP abi_member_head_size (TAKE i atys)) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ptr) (type_memory_bytes ce ty)) /\
  lookup_var ptr initial = SOME (n2w d) /\ not_fresh_at st ptr /\
  compile_decode_args ce [build_positional_arg ce (name,ty)] off
    DLOAD (Lit (n2w data_size)) 0 st = ((),last) /\
  fresh_vars_wrt st initial /\ fn_has_code st last func /\
  (st.cs_blocks = last.cs_blocks \/
    !bb. lookup_block last.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?src middle prepared sb.
    compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit 0w) (Lit (n2w data_size))
      (type_to_abi_dec_info ce.ce_struct_fields ce ty) middle = ((),last) /\
    eval_operand src prepared = SOME (n2w sb) /\
    eval_operand (Var ptr) prepared = SOME (n2w d) /\
    (!x. src = Var x \/ Var ptr = Var x \/ Lit (n2w data_size) = Var x ==>
      not_fresh_at middle x) /\
    mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)))
      prepared.vs_data_section = enc (vyper_to_abi_type env ty) (EL i avs) /\
    sb + LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) < dimword (:256) /\
    (data_size <> 0 ==> sb + LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) <= data_size /\
      data_size < dimword (:256)) /\
    fresh_vars_wrt middle prepared /\ cs_extends st middle /\
    middle.cs_blocks = st.cs_blocks /\
    st.cs_next_var <= middle.cs_next_var /\ st.cs_next_id <= middle.cs_next_id /\
    fn_has_code middle last func /\
    (middle.cs_blocks = last.cs_blocks \/
      !bb. lookup_block last.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    frag_ids middle last SUBSET frag_ids st last /\
    prepared.vs_memory = initial.vs_memory /\ prepared.vs_allocas = initial.vs_allocas /\
    prepared.vs_alloca_next = initial.vs_alloca_next /\
    prepared.vs_data_section = initial.vs_data_section /\
    prepared.vs_call_ctx = initial.vs_call_ctx /\ prepared.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect {} [] initial prepared /\
    (!x v. not_fresh_at st x /\ lookup_var x initial = SOME v ==>
      lookup_var x prepared = SOME v) /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
    abi_decode_sim ctx func initial prepared
Proof
  qx_gen_tac `pvar` >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ctor_canonical_member_source >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  drule_all ctor_singleton_address_prefix >>
  disch_then (qspec_then `ctx`
    (qx_choose_then `src` (qx_choose_then `middle`
      (qx_choose_then `prepared` (map_every assume_tac o CONJUNCTS))))) >>
  `eval_operand (Var pvar) prepared = SOME (n2w d)` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  `prepared.vs_memory = initial.vs_memory /\ prepared.vs_allocas = initial.vs_allocas /\
   prepared.vs_alloca_next = initial.vs_alloca_next /\
   prepared.vs_data_section = initial.vs_data_section /\
   prepared.vs_call_ctx = initial.vs_call_ctx /\ prepared.vs_labels = initial.vs_labels` by
    (qpat_x_assum `_ with <| vs_vars := _; vs_inst_idx := _ |> = initial` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexistsl [`src`, `middle`, `prepared`, `abi_tuple_child_offset atys avs i`] >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (Cases_on `is_abi_dynamic ce.ce_struct_fields ty` >>
      fs[ctor_word_type_static] >> metis_tac[ctor_word_type_static]) >>
  conj_tac
  >- metis_tac[ctor_eval_operand_not_fresh, operand_distinct] >>
  qpat_assum `EL i atys = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
  asm_rewrite_tac[] >>
  metis_tac[LESS_EQ_LESS_TRANS, LESS_EQ_TRANS]
QED

Theorem ctor_effect_scratch_extend[local]:
  abi_encoder_registered_effect (ctor_actual_sites fn child) outs s t /\
  ctor_actual_scratch fn child d n t /\
  (!i. i IN full /\ i NOTIN child ==> FLOOKUP s.vs_allocas i = NONE) ==>
  ctor_actual_scratch fn full d n t
Proof
  simp_tac bool_ss [ctor_actual_scratch_def, abi_encoder_registered_effect_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `inst.inst_id IN child`
  >- metis_tac[] >>
  `inst.inst_id NOTIN ctor_actual_sites fn child` by simp[ctor_actual_sites_def] >>
  metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem ctor_effect_future_absent[local]:
  abi_encoder_registered_effect ids outs s t /\
  (!i. k <= i ==> FLOOKUP s.vs_allocas i = NONE) /\
  (!i. k <= i ==> i NOTIN ids) ==>
  !i. k <= i ==> FLOOKUP t.vs_allocas i = NONE
Proof
  simp_tac bool_ss [abi_encoder_registered_effect_def] >> metis_tac[]
QED

Theorem ctor_decode_constructor_arg_old_prefix:
  !ce env fargs avs atys encoded i name ty tv v off data_size
   pvar d st st' ctx func site initial.
    i < LENGTH fargs /\ LENGTH avs = LENGTH fargs /\
    EL i fargs = (name,ty) /\
    atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
    encoded = enc (Tuple atys) (ListV avs) /\
    off = SUM (MAP abi_member_head_size (TAKE i atys)) /\
    LENGTH encoded < dimword (:256) /\
    mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
    (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
    compile_decode_args ce [build_positional_arg ce (name,ty)] off
      DLOAD (Lit (n2w data_size)) 0 st = ((),st') /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var pvar) (type_memory_bytes ce ty)) /\
    lookup_var pvar initial = SOME (n2w d) /\ not_fresh_at st pvar /\
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    abi_decoder_metadata ce env ty tv
      (type_to_abi_dec_info ce.ce_struct_fields ce ty) (EL i avs) v /\
    fresh_vars_wrt st initial /\ fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    (st.cs_blocks = st'.cs_blocks \/
      !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
    unit_alloca_budget ctx < dimword (:256) /\
    d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
    (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
    ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?actual.
      val_in_memory tv v d actual.vs_memory /\
      abi_encoder_registered_effect (frag_ids st st')
        [(d,type_memory_bytes ce ty)] initial actual /\
      abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
        [(d,type_memory_bytes ce ty)] initial actual /\
      ctor_actual_scratch func (frag_ids st st') 0 initial.vs_alloca_next actual /\
      initial.vs_alloca_next <= actual.vs_alloca_next /\
      alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
      d + type_memory_bytes ce ty <= actual.vs_alloca_next /\
      fresh_vars_wrt st' actual /\
      (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
      actual.vs_data_section = initial.vs_data_section /\
      actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
      (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
        lookup_var x actual = SOME w) /\
      ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
      actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
      abi_decode_sim ctx func initial actual
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH atys = LENGTH fargs /\ EL i atys = vyper_to_abi_type env ty` by
    simp[vyper_to_abi_types_MAP, MAP_COMPOSE, EL_MAP] >>
  `i < LENGTH atys /\ LENGTH avs = LENGTH atys` by metis_tac[] >>
  drule_all ctor_canonical_singleton_prefix >>
  disch_then (qspec_then `ctx`
    (qx_choose_then `src` (qx_choose_then `middle`
      (qx_choose_then `prepared` (qx_choose_then `sb` (map_every assume_tac o CONJUNCTS)))))) >>
  `alloca_inv prepared /\ alloca_frontier_inv ctx func site prepared` by
    (qpat_assum `alloca_inv initial` mp_tac >>
     qpat_assum `alloca_frontier_inv _ _ _ initial` mp_tac >>
     pure_rewrite_tac [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_frontier_inv_def, remaining_alloca_budget_def] >>
     asm_simp_tac bool_ss []) >>
  `!aid. middle.cs_next_id <= aid ==> FLOOKUP prepared.vs_allocas aid = NONE` by
    metis_tac[LESS_EQ_TRANS] >>
  `d + type_memory_bytes ce ty <= prepared.vs_alloca_next` by metis_tac[] >>
  drule ctor_decode_buffer_old_prefix >>
  disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand src prepared = _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ prepared`)) >>
  disch_then (qspec_then `sb` mp_tac) >>
  `mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) (EL i avs))) initial.vs_data_section =
    enc (vyper_to_abi_type env ty) (EL i avs)` by metis_tac[] >>
  asm_rewrite_tac[] >>
  (impl_tac
   >- (Cases_on `data_size = 0` >- simp[] >>
       disj2_tac >> qexists `data_size` >>
       `data_size < dimword (:256)` by metis_tac[] >>
       simp[eval_operand_def, w2n_n2w])) >>
  disch_then (qx_choose_then `actual` (map_every assume_tac o CONJUNCTS)) >>
  `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids middle st'))
     [(d,type_memory_bytes ce ty)] initial prepared` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`{}:num set`, `[]:(num#num) list`] >> simp[]) >>
  `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids middle st'))
     [(d,type_memory_bytes ce ty)] initial actual` by
    metis_tac[abi_encoder_registered_effect_trans] >>
  `ctor_actual_sites func (frag_ids middle st') SUBSET ctor_actual_sites func (frag_ids st st')` by
    metis_tac[ctor_actual_sites_mono] >>
  `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
     [(d,type_memory_bytes ce ty)] initial actual` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`ctor_actual_sites func (frag_ids middle st')`, `[(d,type_memory_bytes ce ty)]`] >> simp[]) >>
  `abi_encoder_registered_effect (frag_ids st st')
     [(d,type_memory_bytes ce ty)] initial actual` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`ctor_actual_sites func (frag_ids st st')`, `[(d,type_memory_bytes ce ty)]`] >>
     simp[ctor_actual_sites_subset]) >>
  `ctor_actual_scratch func (frag_ids st st') 0 initial.vs_alloca_next actual` by
    (irule ctor_effect_scratch_extend >>
     qexistsl [`frag_ids middle st'`, `[(d,type_memory_bytes ce ty)]`, `initial`] >>
     asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
     `st.cs_next_id <= i'` by fs[frag_ids_def] >> metis_tac[]) >>
  `middle.cs_next_id <= st'.cs_next_id` by
    (drule abi_decoder_to_buf_code >> simp[abi_decode_source_opcode_def, abi_decoder_code_def]) >>
  `!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE` by
    (gen_tac >> strip_tac >> irule ctor_effect_future_absent >>
     qexistsl [`ctor_actual_sites func (frag_ids middle st')`, `st'.cs_next_id`, `[(d,type_memory_bytes ce ty)]`, `initial`] >>
     asm_rewrite_tac[] >> conj_tac
     >- simp[ctor_actual_sites_def, frag_ids_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  qexists `actual` >> asm_rewrite_tac[] >>
  conj_tac >- decide_tac >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at middle x` by
        (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
      metis_tac[]) >>
  metis_tac[abi_decode_sim_trans]
QED

Theorem ctor_scratch_decode_bind_ptr:
  local_ptrs_rel func ce scopes s /\ fresh_vars_wrt st s /\
  (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w) /\
  abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,n)] s t /\
  ctor_actual_scratch func ids 0 s.vs_alloca_next t /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  lookup_scopes name scopes = SOME entry /\
  (!q sq. FLOOKUP ce.ce_vars name <> SOME (PtrVar (Var q) sq)) /\
  lookup_var p s = SOME w /\ not_fresh_at st p /\ w2n w = d /\
  local_backed func p s d n /\ d+n <= s.vs_alloca_next /\
  type_memory_size entry.type <= n /\ val_wf entry.type entry.value /\
  val_in_memory entry.type entry.value d t.vs_memory /\
  (!nm b sz. local_region ce scopes s nm b sz ==> compileEnv$regions_disjoint d n b sz) ==>
  local_ptrs_rel func (ce with ce_vars := ce.ce_vars |+ (name,PtrVar (Var p) n)) scopes t
Proof
  strip_tac >>
  `!nm ent q sz. lookup_scopes nm scopes = SOME ent /\
    FLOOKUP ce.ce_vars nm = SOME (PtrVar (Var q) sz) ==>
    lookup_var q t = lookup_var q s` by
    (rpt strip_tac >>
     `not_fresh_at st q` by (irule entry_live_ptrs_not_fresh >> metis_tac[]) >>
     qpat_assum `local_ptrs_rel func ce scopes s` mp_tac >>
     pure_rewrite_tac[local_ptrs_rel_def] >> strip_tac >>
     first_x_assum drule_all >> strip_tac >> metis_tac[]) >>
  `!nm b sz. local_region ce scopes t nm b sz ==> local_region ce scopes s nm b sz` by
    (rw[local_region_def] >> metis_tac[]) >>
  `local_ptrs_rel func ce scopes t` by
    (irule ctor_scratch_local_ptrs_frame >>
     qexistsl [`d`, `ids`, `s`, `n`] >> simp[] >>
     fs[compileEnvTheory.regions_disjoint_def, venomMemDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  `local_backed func p t d n` by
    (irule local_backed_frame >> qexists `s` >> simp[] >> conj_tac
     >- (rpt strip_tac >> drule_all ctor_scratch_new_allocations >> simp[]) >>
     rpt strip_tac >> drule_all abi_encoder_registered_effect_allocated >> simp[]) >>
  `lookup_var p t = SOME w` by metis_tac[] >>
  `d+n <= t.vs_alloca_next` by decide_tac >>
  `ce with ce_vars := ce.ce_vars |+ (name,PtrVar (Var p) n) =
   ce with ce_vars updated_by (\m. m |+ (name,PtrVar (Var p) n))` by
    simp[compile_env_component_equality] >>
  pop_assum SUBST1_TAC >> irule intCallCalleeTheory.local_ptrs_rel_bind_ptr >>
  asm_rewrite_tac[] >> qexistsl [`entry`, `w`] >> simp[] >> metis_tac[]
QED

Theorem ctor_registered_alloc_decode_effect:
  abi_encoder_registered_effect alloc_ids [] s a /\
  abi_encoder_registered_effect decode_ids [(d,n)] a t /\
  alloc_ids SUBSET ids /\ decode_ids SUBSET ids /\ aid IN ids /\
  FLOOKUP a.vs_allocas aid = SOME (d,n) ==>
  abi_encoder_registered_effect ids [] s t
Proof
  strip_tac >>
  `FLOOKUP t.vs_allocas aid = SOME (d,n)` by
    (drule_all abi_encoder_registered_effect_allocated >> simp[]) >>
  `abi_encoder_registered_effect ids [] a t` by
    (irule ctor_registered_output_absorb >>
     qexistsl [`aid`, `d`, `decode_ids`, `n`] >> simp[]) >>
  `abi_encoder_registered_effect ids [] s a` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`alloc_ids`, `[]:(num#num) list`] >> simp[]) >>
  metis_tac[abi_encoder_registered_effect_trans]
QED

Theorem ctor_register_one_actual:
  !ce env fargs avs atys encoded i name ty entry off data_size old
   buf sa ce' st st' ctx func site initial.
    i < LENGTH fargs /\ LENGTH avs = LENGTH fargs /\
    EL i fargs = (name,ty) /\
    atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
    encoded = enc (Tuple atys) (ListV avs) /\
    off = SUM (MAP abi_member_head_size (TAKE i atys)) /\
    LENGTH encoded < dimword (:256) /\
    mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
    (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
    FLOOKUP ce.ce_vars name = SOME (MemLoc old (type_memory_bytes ce ty)) /\
    lookup_scopes name [scope] = SOME entry /\
    val_wf entry.type entry.value /\
    type_memory_size entry.type <= type_memory_bytes ce ty /\
    abi_decoder_coherent ce env ce.ce_struct_fields ty entry.type /\
    abi_decoder_metadata ce env ty entry.type
      (type_to_abi_dec_info ce.ce_struct_fields ce ty) (EL i avs) entry.value /\
    type_memory_bytes ce ty < dimword (:256) /\
    compile_alloc_buffer (type_memory_bytes ce ty) st = (buf,sa) /\
    ce' = (ce with ce_vars := ce.ce_vars |+
      (name,PtrVar buf.buf_operand (type_memory_bytes ce ty))) /\
    compile_decode_args ce' [build_positional_arg ce (name,ty)] off
      DLOAD (Lit (n2w data_size)) 0 sa = ((),st') /\
    local_ptrs_rel func ce [scope] initial /\ fresh_vars_wrt st initial /\
    fn_has_code st sa func /\ fn_has_code sa st' func /\ fn_inst_ids_distinct func /\
    (sa.cs_blocks = st'.cs_blocks \/
      !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
    unit_alloca_budget ctx < dimword (:256) /\
    (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
    ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?actual.
      local_ptrs_rel func ce' [scope] actual /\
      abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
      alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
      fresh_vars_wrt st' actual /\
      (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
      actual.vs_data_section = initial.vs_data_section /\
      actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
      (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
        lookup_var x actual = SOME w) /\
      ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
      actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
      abi_decode_sim ctx func initial actual
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ctor_alloc_buffer_actual >>
  disch_then (qx_choose_then `a` (map_every assume_tac o CONJUNCTS)) >>
  `ce' = ce with ce_vars := ce.ce_vars |+
    (name,PtrVar (Var (STRING #"%" (toString st.cs_next_var))) (type_memory_bytes ce ty))` by simp[] >>
  `abi_decoder_coherent ce' env ce'.ce_struct_fields ty entry.type /\
   abi_decoder_metadata ce' env ty entry.type
     (type_to_abi_dec_info ce'.ce_struct_fields ce' ty) (EL i avs) entry.value` by simp[] >>
  `compile_decode_args ce' [build_positional_arg ce' (name,ty)] off
      DLOAD (Lit (n2w data_size)) 0 sa = ((),st')` by
    gnvs[] >>
  `FLOOKUP ce'.ce_vars name = SOME (PtrVar
    (Var (STRING #"%" (toString st.cs_next_var))) (type_memory_bytes ce' ty))` by simp[FLOOKUP_UPDATE] >>
  `initial.vs_alloca_next + type_memory_bytes ce' ty <= a.vs_alloca_next` by simp[] >>
  `mem_bytes_at 0 (LENGTH encoded) a.vs_data_section = encoded` by
    (qpat_assum `a.vs_data_section = _` (fn th => pure_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  drule_all ctor_decode_constructor_arg_old_prefix >>
  disch_then (qx_choose_then `actual` (map_every assume_tac o CONJUNCTS)) >>
  `type_memory_bytes ce' ty = type_memory_bytes ce ty` by simp[] >>
  ntac 10 (pop_last_assum kall_tac) >>
  qpat_x_assum `abi_decoder_coherent ce _ _ _ _` kall_tac >>
  qpat_x_assum `abi_decoder_metadata ce _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `abi_decoder_coherent ce' _ _ _ _` kall_tac >>
  qpat_x_assum `abi_decoder_metadata ce' _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `mem_bytes_at _ _ a.vs_data_section = _` kall_tac >>
  suspend "finish"
QED

Resume ctor_register_one_actual[finish]:
  drule compile_alloc_buffer_parts >> strip_tac >>
  `st.cs_next_id <= sa.cs_next_id /\ st.cs_next_var <= sa.cs_next_var` by decide_tac >>
  `sa.cs_next_id <= st'.cs_next_id` by
    (qpat_assum `compile_decode_args ce' [build_positional_arg ce' _] _ _ _ _ _ = _` mp_tac >>
     metis_tac[ctor_decode_args_next_id, pairTheory.SND]) >>
  qexists `actual` >> asm_rewrite_tac[] >>
  conj_tac >- suspend "locals" >>
  conj_tac >- suspend "effect" >>
  conj_tac >- suspend "registers" >>
  metis_tac[abi_decode_sim_trans]
QED

Resume ctor_register_one_actual[locals]:
  qpat_assum `ce' = ce with ce_vars := ce.ce_vars |+ (name,PtrVar (Var _) _)`
    (fn th => pure_once_rewrite_tac[th]) >>
  irule ctor_scratch_decode_bind_ptr >>
  conj_tac >- simp[] >>
  qexistsl [`initial.vs_alloca_next`, `entry`, `frag_ids sa st'`, `a`, `sa`,
    `n2w initial.vs_alloca_next : bytes32`] >>
  asm_rewrite_tac[] >>
  `initial.vs_alloca_next < dimword (:256)` by decide_tac >>
  simp[w2n_n2w] >> gnvs[]
QED

Resume ctor_register_one_actual[effect]:
  irule ctor_registered_alloc_decode_effect >>
  qexistsl [`a`, `st.cs_next_id`, `frag_ids st sa`, `initial.vs_alloca_next`,
    `frag_ids sa st'`, `type_memory_bytes ce' ty`] >>
  asm_rewrite_tac[] >> simp[frag_ids_def, SUBSET_DEF] >> decide_tac
QED

Resume ctor_register_one_actual[registers]:
  rpt strip_tac >>
  `not_fresh_at sa x` by
    (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  metis_tac[]
QED

Finalise ctor_register_one_actual

Theorem ctor_register_suffix_actual:
  !rest ce0 vars env fargs avs atys encoded scope i data_size st ce st' ctx func site initial.
    rest = DROP i fargs /\ i <= LENGTH fargs /\
    ALL_DISTINCT (MAP FST rest) /\ LENGTH avs = LENGTH fargs /\
    atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
    encoded = enc (Tuple atys) (ListV avs) /\
    LENGTH encoded < dimword (:256) /\
    mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
    (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
    EVERY (\a. ?off. FLOOKUP vars (FST a) =
      SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) rest /\
    EVERY (\a. type_memory_bytes ce0 (SND a) < dimword (:256)) rest /\
    (!j. j < LENGTH fargs ==>
      ?entry. lookup_scopes (FST (EL j fargs)) [scope] = SOME entry /\
        val_wf entry.type entry.value /\
        type_memory_size entry.type <= type_memory_bytes ce0 (SND (EL j fargs)) /\
        abi_decoder_coherent ce0 env ce0.ce_struct_fields
          (SND (EL j fargs)) entry.type /\
        abi_decoder_metadata ce0 env (SND (EL j fargs)) entry.type
          (type_to_abi_dec_info ce0.ce_struct_fields ce0 (SND (EL j fargs)))
          (EL j avs) entry.value) /\
    compile_register_constructor_args (ce0 with ce_vars := vars)
      (build_positional_args ce0 rest)
      (SUM (MAP abi_member_head_size (TAKE i atys))) data_size st = (ce,st') /\
    local_ptrs_rel func (ce0 with ce_vars := vars) [scope] initial /\ fresh_vars_wrt st initial /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    (st.cs_blocks = st'.cs_blocks \/
      !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
    unit_alloca_budget ctx < dimword (:256) /\
    (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
    ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?actual.
      local_ptrs_rel func ce [scope] actual /\
      abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
      alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
      fresh_vars_wrt st' actual /\
      (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
      actual.vs_data_section = initial.vs_data_section /\
      actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
      (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
        lookup_var x actual = SOME w) /\
      ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
      actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
      abi_decode_sim ctx func initial actual
Proof
  Induct >- (rpt gen_tac >> strip_tac >>
    gvs[build_positional_args_def, compile_register_constructor_args_def, comp_return_def] >>
    qexists `initial` >> simp[abi_encoder_registered_effect_refl, abi_decode_sim_refl]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  PairCases_on `h` >>
  `i < LENGTH fargs` by
    (`LENGTH ((h0,h1)::rest) = LENGTH (DROP i fargs)` by metis_tac[] >>
     fs[LENGTH_DROP] >> decide_tac) >>
  `EL i fargs = (h0,h1) /\ rest = DROP (SUC i) fargs` by
    (qspecl_then [`fargs`, `i`] mp_tac DROP_EL_CONS >>
     (impl_tac >- simp[]) >>
     pure_rewrite_tac[GSYM ADD1] >>
     disch_then (fn th => qpat_assum `_::rest = DROP i fargs`
       (mp_tac o REWRITE_RULE [th])) >> simp[]) >>
  qpat_assum `!j. j < LENGTH fargs ==> _` (qspec_then `i` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `entry` (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `!ce0 vars env fargs avs atys encoded scope i data_size st ce st' ctx func site initial. _`
    (mk_asm "suffix_ih") >>
  qpat_x_assum `EVERY (\a. ?off. _) (_::rest)` mp_tac >>
  SIMP_TAC pure_ss [EVERY_DEF, pairTheory.FST, pairTheory.SND] >> strip_tac >>
  qpat_x_assum `EVERY _ (_::rest)` mp_tac >>
  SIMP_TAC pure_ss [EVERY_DEF, pairTheory.FST, pairTheory.SND] >> strip_tac >>
  `FLOOKUP (ce0 with ce_vars := vars).ce_vars h0 =
     SOME (MemLoc off (type_memory_bytes (ce0 with ce_vars := vars) h1))` by simp[] >>
  drule ctor_register_cons >>
  disch_then (fn th => qpat_x_assum `compile_register_constructor_args _ _ _ _ st = _`
    (mp_tac o PURE_REWRITE_RULE [SRULE[] th])) >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce0 h1) st` >>
  rename1 `compile_alloc_buffer _ st = (buf,sa)` >>
  simp[IgnAsm `atys = _`, IgnAsm `rest = _`, comp_bind_def, comp_ignore_bind_def] >>
  qmatch_goalsub_abbrev_tac `compile_decode_args next _ _ _ _ _` >>
  Cases_on `compile_decode_args next [build_positional_arg ce0 (h0,h1)]
    (SUM (MAP abi_member_head_size (TAKE i atys))) DLOAD (Lit (n2w data_size)) 0 sa` >>
  rename1 `compile_decode_args _ _ _ _ _ _ sa = (u,sd)` >>
  Cases_on `u` >>
  simp[IgnAsm `atys = _`, IgnAsm `rest = _`, comp_bind_def, comp_ignore_bind_def] >>
  strip_tac >>
  drule_all ctor_registration_code_phases >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ctor_registration_phi_phases >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_alloc_buffer (type_memory_bytes (ce0 with ce_vars := vars) h1) st = (buf,sa)` by simp[] >>
  `next = ((ce0 with ce_vars := vars) with ce_vars :=
      ((ce0 with ce_vars := vars).ce_vars |+
      (h0,PtrVar buf.buf_operand (type_memory_bytes (ce0 with ce_vars := vars) h1))))` by
    simp[Abbr `next`] >>
  `lookup_scopes h0 [scope] = SOME entry /\
   type_memory_size entry.type <= type_memory_bytes (ce0 with ce_vars := vars) h1 /\
   abi_decoder_coherent (ce0 with ce_vars := vars) env
     (ce0 with ce_vars := vars).ce_struct_fields h1 entry.type /\
   abi_decoder_metadata (ce0 with ce_vars := vars) env h1 entry.type
     (type_to_abi_dec_info (ce0 with ce_vars := vars).ce_struct_fields
       (ce0 with ce_vars := vars) h1) (EL i avs) entry.value` by
    (qpat_assum `EL i fargs = _` (fn th => fs[th])) >>
  `compile_decode_args next [build_positional_arg (ce0 with ce_vars := vars) (h0,h1)]
    (SUM (MAP abi_member_head_size (TAKE i atys))) DLOAD (Lit (n2w data_size)) 0 sa = ((),sd)` by
    (pure_rewrite_tac[ctor_positional_arg_vars] >> first_assum ACCEPT_TAC) >>
  drule_at (Pat `compile_decode_args _ _ _ _ _ _ _ = _`) ctor_register_one_actual >>
  disch_then (drule_at (Pat `EL _ _ = _`)) >>
  disch_then (drule_at (Pat `_ = enc _ _`)) >>
  disch_then (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_scopes _ _ = _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ _`)) >>
  disch_then (qspecl_then [`env`, `off`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
  disch_then (qx_choose_then `middle` (map_every assume_tac o CONJUNCTS)) >>
  suspend "recurse"
QED

Resume ctor_register_suffix_actual[recurse]:
  `LENGTH atys = LENGTH fargs /\ EL i atys = vyper_to_abi_type env h1` by
    simp[vyper_to_abi_types_MAP, MAP_COMPOSE, EL_MAP] >>
  `abi_embedded_static_size ce0.ce_struct_fields h1 = abi_member_head_size (EL i atys)` by
    (drule ctor_coherent_head_size >> simp[]) >>
  `SUM (MAP abi_member_head_size (TAKE (SUC i) atys)) =
    SUM (MAP abi_member_head_size (TAKE i atys)) +
    abi_embedded_static_size ce0.ce_struct_fields h1` by
    (irule EQ_TRANS >> irule_at Any ctor_canonical_offset_step >> simp[]) >>
  `EVERY (\a. ?off. FLOOKUP
     (vars |+ (h0,PtrVar buf.buf_operand (type_memory_bytes ce0 h1))) (FST a) =
     SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) rest` by
    (qpat_assum `EVERY (\a. ?off. _) rest` mp_tac >>
     qpat_assum `ALL_DISTINCT (MAP FST (_::rest))` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[EVERY_MEM, MEM_MAP, FLOOKUP_UPDATE] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >>
     `FST a <> h0` by metis_tac[] >> simp[]) >>
  `compile_register_constructor_args
    (ce0 with ce_vars := vars |+ (h0,PtrVar buf.buf_operand (type_memory_bytes ce0 h1)))
    (build_positional_args ce0 rest)
    (SUM (MAP abi_member_head_size (TAKE (SUC i) atys))) data_size sd = (ce,st')` by
    (qpat_assum `compile_register_constructor_args next _ _ _ sd = _` mp_tac >>
     qpat_assum `SUM (MAP abi_member_head_size (TAKE (SUC i) atys)) = _`
       (fn th => pure_rewrite_tac[th]) >>
     simp[Abbr `next`, NoAsms]) >>
  `local_ptrs_rel func
    (ce0 with ce_vars := vars |+ (h0,PtrVar buf.buf_operand (type_memory_bytes ce0 h1)))
    [scope] middle` by
    (qpat_assum `local_ptrs_rel func next _ middle` mp_tac >> simp[Abbr `next`, NoAsms]) >>
  `mem_bytes_at 0 (LENGTH encoded) middle.vs_data_section = encoded` by
    (qpat_assum `middle.vs_data_section = _` (fn th => pure_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `ALL_DISTINCT (MAP FST rest)` by
    (qpat_assum `ALL_DISTINCT (MAP FST (_::rest))` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[MAP, ALL_DISTINCT]) >>
  asm "suffix_ih" (drule_at (Pat `compile_register_constructor_args _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `_ = DROP _ _`)) >>
  disch_then (drule_at (Pat `_ = enc _ _`)) >>
  disch_then (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
  disch_then (qx_choose_then `actual` (map_every assume_tac o CONJUNCTS)) >>
  asm_x "suffix_ih" kall_tac >>
  qexists `actual` >> asm_rewrite_tac[] >>
  conj_tac >- suspend "suffix_effect" >>
  conj_tac >- suspend "suffix_registers" >>
  metis_tac[abi_decode_sim_trans]
QED

Resume ctor_register_suffix_actual[suffix_effect]:
  `st.cs_next_id <= sd.cs_next_id` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     `sa.cs_next_id <= sd.cs_next_id` by
       metis_tac[ctor_decode_args_next_id, pairTheory.SND] >> decide_tac) >>
  `sd.cs_next_id <= st'.cs_next_id` by
    metis_tac[ctor_registration_next_id] >>
  `frag_ids st sd SUBSET frag_ids st st'` by
    (simp[frag_ids_def, SUBSET_DEF] >> decide_tac) >>
  irule abi_encoder_registered_effect_trans >> qexists `middle` >> conj_tac
  >- (irule abi_encoder_registered_effect_enlarge >>
      qexistsl [`frag_ids st sd`, `[]:(num#num) list`] >> simp[]) >>
  irule abi_encoder_registered_effect_enlarge >>
  qexistsl [`frag_ids sd st'`, `[]:(num#num) list`] >> simp[]
QED

Resume ctor_register_suffix_actual[suffix_registers]:
  `st.cs_next_var <= sd.cs_next_var` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     `sa.cs_next_var <= sd.cs_next_var` by
       metis_tac[ctor_decode_args_vars_mono, abi_decoder_vars_mono_def, pairTheory.SND] >>
     decide_tac) >>
  rpt strip_tac >>
  `not_fresh_at sd x` by
    (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  metis_tac[]
QED

Finalise ctor_register_suffix_actual

(* The metadata premises describe the already bound source argument scope.
   They are local registration inputs, to be supplied from the checked
   constructor environment and canonical source arguments. *)
Theorem compile_register_constructor_args_actual:
  !ce0 env fargs avs atys encoded scope data_size st ce st' ctx func site initial.
    ALL_DISTINCT (MAP FST fargs) /\ LENGTH avs = LENGTH fargs /\
    atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
    encoded = enc (Tuple atys) (ListV avs) /\
    LENGTH encoded < dimword (:256) /\
    mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
    (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
    EVERY (\a. ?off. FLOOKUP ce0.ce_vars (FST a) =
      SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) fargs /\
    EVERY (\a. type_memory_bytes ce0 (SND a) < dimword (:256)) fargs /\
    (!i. i < LENGTH fargs ==>
      ?entry. lookup_scopes (FST (EL i fargs)) [scope] = SOME entry /\
        val_wf entry.type entry.value /\
        type_memory_size entry.type <= type_memory_bytes ce0 (SND (EL i fargs)) /\
        abi_decoder_coherent ce0 env ce0.ce_struct_fields
          (SND (EL i fargs)) entry.type /\
        abi_decoder_metadata ce0 env (SND (EL i fargs)) entry.type
          (type_to_abi_dec_info ce0.ce_struct_fields ce0 (SND (EL i fargs)))
          (EL i avs) entry.value) /\
    compile_register_constructor_args ce0 (build_positional_args ce0 fargs)
      0 data_size st = (ce,st') /\
    local_ptrs_rel func ce0 [scope] initial /\ fresh_vars_wrt st initial /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    (st.cs_blocks = st'.cs_blocks \/
      !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
    unit_alloca_budget ctx < dimword (:256) /\
    (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
    ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?actual.
      local_ptrs_rel func ce [scope] actual /\
      abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
      alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
      fresh_vars_wrt st' actual /\
      (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
      actual.vs_data_section = initial.vs_data_section /\
      actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
      (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
        lookup_var x actual = SOME w) /\
      ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
      actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
      abi_decode_sim ctx func initial actual
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule ctor_register_suffix_actual >> asm_rewrite_tac[] >>
  qexistsl [`atys`, `avs`, `ce0`, `data_size`, `encoded`, `env`, `fargs`, `0`, `fargs`,
    `ce0.ce_vars`] >>
  simp[]
QED
