(* Decode a constructor tuple member into its allocated argument buffer. *)
Theory ctorArgDecode
Ancestors
  ctorAbiActual ctorAbiActualRecursive ctorAbiActualFrame
  abiDecoderMemberBody abiDecoderTypedContract abiDecoderCoherence abiDecoderContract
  actualAllocCredit actualAllocExec moduleLowering compileVyper
  entryArgPtrs emitHelperProps abiEncoderProps abiEncoderRegisteredEffect
  allocaFrontierBound allocaBudgetProps valueEncoding contractABI vyperABI
  venomExecSemantics venomState venomInst venomMemDefs
  words list rich_list finite_map pred_set arithmetic abiDecoderMemberSlice
  exprLowering compileEnv abiEncoder context emitHelper fragExec
  abiDecoderAppend abiDecoderCounters abiDecoderCode exprLoweringProps
  ctorAbiActualSites abiDecoderReentryAddress abiDecoderReentry
  abiDecoderLoop instIdxIndep ctorAbiActualMemory
Libs
  monadsyntax

Theorem ctor_arg_abi_types_map[local]:
  !tys. vyper_to_abi_types env tys = MAP (vyper_to_abi_type env) tys
Proof
  Induct >> simp[vyper_to_abi_type_def]
QED

Theorem ctor_arg_selected_type[local]:
  i < LENGTH fargs /\ EL i fargs = (name,ty) /\
  atys = vyper_to_abi_types env (MAP SND fargs) ==>
  LENGTH atys = LENGTH fargs /\ EL i atys = vyper_to_abi_type env ty
Proof
  simp[ctor_arg_abi_types_map, MAP_COMPOSE, EL_MAP]
QED

Theorem ctor_arg_tuple_member[local]:
  i < LENGTH atys /\ LENGTH avs = LENGTH atys /\ has_types atys avs /\
  mem_bytes_at 0 (LENGTH (enc (Tuple atys) (ListV avs)))
    (abi_decode_source DLOAD initial) = enc (Tuple atys) (ListV avs) /\
  LENGTH (enc (Tuple atys) (ListV avs)) < dimword (:256) ==>
  has_type (EL i atys) (EL i avs) /\
  mem_bytes_at (abi_tuple_child_offset atys avs i)
    (LENGTH (enc (EL i atys) (EL i avs))) (abi_decode_source DLOAD initial) =
      enc (EL i atys) (EL i avs) /\
  abi_tuple_child_offset atys avs i + LENGTH (enc (EL i atys) (EL i avs)) <=
    LENGTH (enc (Tuple atys) (ListV avs)) /\
  (is_dynamic (EL i atys) ==>
    abi_decode_load DLOAD (n2w (SUM (MAP abi_member_head_size (TAKE i atys))) : bytes32) initial =
      n2w (abi_tuple_child_offset atys avs i) /\
    abi_tuple_child_offset atys avs i < dimword (:256)) /\
  (~is_dynamic (EL i atys) ==>
    abi_tuple_child_offset atys avs i = SUM (MAP abi_member_head_size (TAKE i atys)))
Proof
  strip_tac >>
  `TAKE i atys ++ EL i atys::DROP (SUC i) atys = atys` by
    (mp_tac (Q.ISPEC `atys:abi_type list` (Q.SPEC `i:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `TAKE i avs ++ EL i avs::DROP (SUC i) avs = avs` by
    (mp_tac (Q.ISPEC `avs:abi_value list` (Q.SPEC `i:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `LENGTH (TAKE i atys) = i /\ LENGTH (TAKE i avs) = i` by simp[] >>
  mp_tac (Q.INST [`pre` |-> `TAKE i atys`, `ty` |-> `EL i atys`,
    `post` |-> `DROP (SUC i) atys`, `pvs` |-> `TAKE i avs`,
    `v` |-> `EL i avs`, `rest` |-> `DROP (SUC i) avs`,
    `sb` |-> `0`, `opc` |-> `DLOAD`, `s` |-> `initial`]
    abi_tuple_child_offset_source) >>
  asm_simp_tac bool_ss [ADD_CLAUSES] >> strip_tac >>
  mp_tac (Q.INST [`pre` |-> `TAKE i atys`, `ty` |-> `EL i atys`,
    `post` |-> `DROP (SUC i) atys`, `pvs` |-> `TAKE i avs`,
    `v` |-> `EL i avs`, `rest` |-> `DROP (SUC i) avs`]
    abi_tuple_child_offset_ranges) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`pre` |-> `TAKE i atys`, `aty` |-> `EL i atys`,
    `post` |-> `DROP (SUC i) atys`, `pvs` |-> `TAKE i avs`,
    `av` |-> `EL i avs`, `avs` |-> `DROP (SUC i) avs`,
    `sb` |-> `0`, `opc` |-> `DLOAD`, `s` |-> `initial`]
    abi_decoder_canonical_member_inputs) >>
  asm_simp_tac bool_ss [ADD_CLAUSES] >>
  Cases_on `is_dynamic (EL i atys)` >> simp[] >> strip_tac >> gvs[]
QED

Theorem ctor_arg_member_source[local]:
  i < LENGTH fargs /\ LENGTH avs = LENGTH fargs /\
  EL i fargs = (name,ty) /\
  atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
  encoded = enc (Tuple atys) (ListV avs) /\
  off = SUM (MAP abi_member_head_size (TAKE i atys)) /\
  LENGTH encoded < dimword (:256) /\
  mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv ==>
  has_type (vyper_to_abi_type env ty) (EL i avs) /\
  mem_bytes_at (abi_tuple_child_offset atys avs i)
    (LENGTH (enc (vyper_to_abi_type env ty) (EL i avs))) initial.vs_data_section =
      enc (vyper_to_abi_type env ty) (EL i avs) /\
  abi_tuple_child_offset atys avs i +
    LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) <= LENGTH encoded /\
  abi_tuple_child_offset atys avs i +
    LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) < dimword (:256) /\
  (is_abi_dynamic ce.ce_struct_fields ty ==>
    abi_decode_load DLOAD (n2w off : bytes32) initial =
      n2w (abi_tuple_child_offset atys avs i)) /\
  (~is_abi_dynamic ce.ce_struct_fields ty ==>
    abi_tuple_child_offset atys avs i = off)
Proof
  strip_tac >>
  drule_all ctor_arg_selected_type >> strip_tac >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `i < LENGTH atys /\ LENGTH avs = LENGTH atys` by simp[] >>
  `mem_bytes_at 0 (LENGTH (enc (Tuple atys) (ListV avs)))
      (abi_decode_source DLOAD initial) = enc (Tuple atys) (ListV avs)` by
    gvs[abi_decode_source_def, Excl "enc_def"] >>
  `LENGTH (enc (Tuple atys) (ListV avs)) < dimword (:256)` by metis_tac[] >>
  drule_all ctor_arg_tuple_member >>
  gvs[abi_decode_source_def, Excl "enc_def"]
QED

Theorem ctor_arg_word_descriptor[local]:
  is_word_type ty ==>
  ?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp
Proof
  Cases_on `ty` >> simp[is_word_type_def, type_to_abi_dec_info_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[is_word_type_def, type_to_abi_dec_info_def] >>
  rename1 `BytesT b` >> Cases_on `b` >>
  simp[is_word_type_def, type_to_abi_dec_info_def]
QED

Theorem ctor_arg_static_code[local]:
  !ptr. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var (ptr:string)) (type_memory_bytes ce ty)) /\
  ~is_word_type ty /\ ~is_abi_dynamic ce.ce_struct_fields ty ==>
  compile_decode_args ce [build_positional_arg ce (name,ty)] off
      DLOAD (Lit (n2w data_size)) 0 =
  do src <- emit_op ADD [Lit 0w; Lit (n2w off)];
     compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit (n2w data_size))
       (type_to_abi_dec_info ce.ce_struct_fields ce ty)
  od
Proof
  rpt strip_tac >>
  simp[build_positional_arg_def, compile_decode_args_def,
       var_location_decode_operand_def, FUN_EQ_THM,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem ctor_arg_dynamic_code[local]:
  !ptr. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ptr) (type_memory_bytes ce ty)) /\
  ~is_word_type ty /\ is_abi_dynamic ce.ce_struct_fields ty ==>
  compile_decode_args ce [build_positional_arg ce (name,ty)] off
      DLOAD (Lit (n2w data_size)) 0 =
  do static_src <- emit_op ADD [Lit 0w; Lit (n2w off)];
     offset_val <- emit_op DLOAD [static_src];
     src <- emit_op ADD [Lit 0w; offset_val];
     compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit (n2w data_size))
       (type_to_abi_dec_info ce.ce_struct_fields ce ty)
  od
Proof
  rpt strip_tac >>
  simp[build_positional_arg_def, compile_decode_args_def,
       compile_abi_arg_ptr_guard_def,
       var_location_decode_operand_def, FUN_EQ_THM,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem ctor_arg_primitive_code[local]:
  !ptr. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ptr) (type_memory_bytes ce ty)) /\
  is_word_type ty ==>
  compile_decode_args ce [build_positional_arg ce (name,ty)] off
      DLOAD (Lit (n2w data_size)) 0 =
  do src <- emit_op ADD [Lit 0w; Lit (n2w off)];
     compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit (n2w data_size))
       (type_to_abi_dec_info ce.ce_struct_fields ce ty)
  od
Proof
  rpt strip_tac >>
  `?clamp. type_to_abi_dec_info ce.ce_struct_fields ce ty = DecPrimWord clamp` by
    metis_tac[ctor_arg_word_descriptor] >>
  simp[build_positional_arg_def, compile_decode_args_def,
       var_location_decode_operand_def, compile_abi_decode_to_buf_def,
       compile_abi_decode_static_def, FUN_EQ_THM,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem ctor_arg_emit_shape[local]:
  emit_op opc ops st = (src,middle) ==>
  cs_extends st middle /\ middle.cs_blocks = st.cs_blocks /\
  middle.cs_current_bb = st.cs_current_bb /\
  middle.cs_next_id = st.cs_next_id + 1 /\
  middle.cs_next_var = st.cs_next_var + 1
Proof
  strip_tac >>
  `isPREFIX st.cs_current_insts middle.cs_current_insts` by
    metis_tac[emit_op_prefix] >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
      fresh_var_def, fresh_id_def, comp_return_def, emit_def] >>
  irule cs_extends_same_block >> simp[]
QED

Theorem ctor_arg_decoder_code_phase[local]:
  cs_extends st middle /\ middle.cs_blocks = st.cs_blocks /\
  abi_decode_source_opcode opc /\ st.cs_next_id <= middle.cs_next_id /\
  compile_abi_decode_to_buf dst src opc hi di middle = ((),end_st) /\
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

Theorem ctor_arg_decoder_actual[local]:
  !dst src hi ce env ty tv av v st st' ctx func site initial sb d.
    compile_abi_decode_to_buf dst src DLOAD hi
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
    fresh_vars_wrt st initial /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
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
      alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
      d + type_memory_bytes ce ty <= actual.vs_alloca_next /\
      fresh_vars_wrt st' actual /\
      (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
      actual.vs_data_section = initial.vs_data_section /\
      actual.vs_call_ctx = initial.vs_call_ctx /\
      actual.vs_labels = initial.vs_labels /\
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
  `ctor_actual_scratch func (frag_ids st st') d (type_memory_bytes ce ty) initial` by
    (simp_tac bool_ss [ctor_actual_scratch_def, frag_ids_def, GSPECIFICATION] >>
     rpt strip_tac >> res_tac >> gvs[]) >>
  drule (BETA_RULE ctor_actual_coherent_run) >>
  disch_then (drule_at Any) >>
  disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dst initial = _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  simp_tac bool_ss [LESS_EQ_REFL, SUBSET_REFL] >>
  disch_then (qspecl_then [`ctx`, `site`, `d`] mp_tac) >>
  simp_tac bool_ss [LESS_EQ_REFL] >>
  disch_then drule_all >> strip_tac >>
  `abi_encoder_registered_effect (frag_ids st st')
    [(d,type_memory_bytes ce ty)] initial actual` by
    (irule abi_encoder_registered_effect_enlarge >>
     goal_assum (drule_at Any) >> simp[ctor_actual_sites_subset]) >>
  qexists `actual` >> asm_rewrite_tac[] >>
  fs[abi_encoder_registered_effect_def, frag_ids_def] >>
  rpt strip_tac >>
  `st.cs_next_id <= st'.cs_next_id` by
    (drule abi_decoder_to_buf_code >> simp[abi_decode_source_opcode_def, abi_decoder_code_def]) >>
  metis_tac[LESS_EQ_TRANS, NOT_LESS_EQUAL]
QED

Theorem ctor_arg_sequence_reach[local]:
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
  drule abi_decode_sim_from_fragment >>
  disch_then drule >> simp[]
QED

Theorem ctor_arg_add_reach[local]:
  emit_op ADD [lhs;rhs] st = (out,middle) /\
  eval_operand lhs initial = SOME a /\ eval_operand rhs initial = SOME b /\
  fresh_vars_wrt st initial /\ fn_has_code st middle func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared.
    eval_operand out prepared = SOME (a+b) /\ fresh_vars_wrt middle prepared /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op prepared = eval_operand op initial) /\
    prepared = (update_var (STRING #"%" (toString st.cs_next_var)) (a+b) initial
      with vs_inst_idx := LENGTH middle.cs_current_insts) /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
    abi_decode_sim ctx func initial prepared
Proof
  strip_tac >> drule ctor_arg_emit_shape >> strip_tac >>
  `fresh_vars_wrt middle initial` by
    (irule fresh_vars_wrt_mono >> qexists `st` >> simp[GREATER_EQ]) >>
  drule abi_decoder_binary_reentry >> simp_tac bool_ss [] >>
  disch_then drule >> disch_then drule >>
  disch_then (qspec_then `middle` mp_tac) >> simp[] >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st middle)` by
    (drule emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def]) >>
  drule_all ctor_arg_sequence_reach >> disch_then (qspec_then `ctx` assume_tac) >>
  gvs[eval_op_inst_idx, fresh_vars_wrt_def, update_var_def]
QED

Theorem ctor_arg_read_reach[local]:
  emit_op DLOAD [src] st = (out,middle) /\
  eval_operand src initial = SOME p /\
  fresh_vars_wrt st initial /\ fn_has_code st middle func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared.
    eval_operand out prepared = SOME (abi_decode_load DLOAD p initial) /\
    fresh_vars_wrt middle prepared /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op prepared = eval_operand op initial) /\
    prepared = (update_var (STRING #"%" (toString st.cs_next_var))
      (abi_decode_load DLOAD p initial) initial
      with vs_inst_idx := LENGTH middle.cs_current_insts) /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
    abi_decode_sim ctx func initial prepared
Proof
  strip_tac >> drule ctor_arg_emit_shape >> strip_tac >>
  `fresh_vars_wrt middle initial` by
    (irule fresh_vars_wrt_mono >> qexists `st` >> simp[GREATER_EQ]) >>
  drule abi_decoder_read_reentry >> simp_tac bool_ss [abi_decode_source_opcode_def] >>
  disch_then drule >>
  disch_then (qspec_then `middle` mp_tac) >> simp[] >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st middle)` by
    (drule emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def]) >>
  drule_all ctor_arg_sequence_reach >> disch_then (qspec_then `ctx` assume_tac) >>
  gvs[eval_op_inst_idx, fresh_vars_wrt_def, update_var_def]
QED

Theorem ctor_arg_register_observations[local]:
  (alloca_inv (update_var x w s) <=> alloca_inv s) /\
  (alloca_inv (s with vs_inst_idx := ix) <=> alloca_inv s) /\
  (abi_encoder_registered_effect ids outs (update_var x w s) t <=>
    abi_encoder_registered_effect ids outs s t) /\
  (abi_encoder_registered_effect ids outs (s with vs_inst_idx := ix) t <=>
    abi_encoder_registered_effect ids outs s t)
Proof
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       abi_encoder_registered_effect_def, update_var_def]
QED

Theorem ctor_arg_setup_decode_actual[local]:
  !pvar sb st src middle ce ty data_size st' env tv av v initial prepared d func ctx site.
  cs_extends st middle /\ middle.cs_blocks = st.cs_blocks /\
  st.cs_next_id <= middle.cs_next_id /\ st.cs_next_var <= middle.cs_next_var /\
  abi_decode_sim ctx func initial prepared /\
  eval_operand src prepared = SOME (n2w sb) /\
  abi_decoder_operand_live middle.cs_next_var src /\
  fresh_vars_wrt middle prepared /\ alloca_inv prepared /\
  alloca_frontier_inv ctx func site prepared /\
  prepared.vs_allocas = initial.vs_allocas /\
  prepared.vs_alloca_next = initial.vs_alloca_next /\
  prepared.vs_data_section = initial.vs_data_section /\
  prepared.vs_call_ctx = initial.vs_call_ctx /\ prepared.vs_labels = initial.vs_labels /\
  abi_encoder_registered_effect {} [] initial prepared /\
  (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
    lookup_var x prepared = SOME w) /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
  compile_abi_decode_to_buf (Var pvar) src DLOAD (Lit (n2w data_size))
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) middle = ((),st') /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  abi_decoder_metadata ce env ty tv
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
  lookup_var pvar initial = SOME (n2w d) /\ not_fresh_at st pvar /\
  sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
    initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  (data_size = 0 \/ sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= data_size /\
    data_size < dimword (:256)) /\
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
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `!x w. not_fresh_at st x /\ _ ==> lookup_var x prepared = _`
    (mk_asm "prefixvars") >>
  `eval_operand (Var pvar) prepared = SOME (n2w d)` by
    (simp[eval_operand_def] >> asm "prefixvars" irule >> asm_rewrite_tac[]) >>
  `!x. src = Var x \/ Var pvar = Var x \/ Lit (n2w data_size) = Var x ==>
    not_fresh_at middle x` by
    (qpat_x_assum `abi_decoder_operand_live _ src` mp_tac >>
     qpat_x_assum `not_fresh_at st pvar` mp_tac >>
     qpat_x_assum `st.cs_next_var <= middle.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `src` >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_TRANS]) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  `st.cs_blocks = middle.cs_blocks` by asm_rewrite_tac[] >>
  drule_all ctor_arg_decoder_code_phase >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!aid. middle.cs_next_id <= aid ==> FLOOKUP prepared.vs_allocas aid = NONE` by
    (asm_rewrite_tac[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  Cases_on `data_size = 0` >>
  qpat_assum `eval_operand src prepared = _` assume_tac >>
  drule ctor_arg_decoder_actual >>
  disch_then (drule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand src prepared = _`)) >>
  disch_then (qspecl_then [`ctx`, `func`, `site`, `d`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> disj2_tac >> qexists `data_size` >>
    fs[eval_operand_def])) >>
  disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  all_tac >>
  `abi_encoder_registered_effect (frag_ids st st')
    [(d,type_memory_bytes ce ty)] initial prepared` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`{}`, `[]`] >> asm_rewrite_tac[EMPTY_SUBSET, EVERY_DEF]) >>
  `abi_encoder_registered_effect (frag_ids st st')
    [(d,type_memory_bytes ce ty)] prepared actual` by
    (irule abi_encoder_registered_effect_enlarge >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  `abi_encoder_registered_effect (frag_ids st st')
    [(d,type_memory_bytes ce ty)] initial actual` by
    (irule abi_encoder_registered_effect_trans >> qexists `prepared` >> asm_rewrite_tac[]) >>
  `abi_decode_sim ctx func initial actual` by
    (irule abi_decode_sim_trans >> qexists `prepared` >> asm_rewrite_tac[]) >>
  qexists `actual` >> asm_rewrite_tac[] >>
  rpt gen_tac >> strip_tac >>
  `not_fresh_at middle x` by
    (qpat_x_assum `not_fresh_at st x` mp_tac >>
     qpat_x_assum `st.cs_next_var <= middle.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `lookup_var x prepared = SOME w` by
    (asm "prefixvars" (qspecl_then [`x`, `w`] mp_tac) >>
     qpat_assum `not_fresh_at st x` mp_tac >>
     qpat_assum `lookup_var x initial = SOME w` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  qpat_x_assum `!x w. not_fresh_at middle x /\ _ ==> _`
    (qspecl_then [`x`, `w`] mp_tac) >> asm_rewrite_tac[]
QED


Theorem ctor_arg_add_decode_actual[local]:
  !ptr sb st src middle ce ty data_size st' env tv av v initial d func ctx site.
  emit_op ADD [Lit 0w; Lit (n2w sb)] st = (src,middle) /\
  compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit (n2w data_size))
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) middle = ((),st') /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  abi_decoder_metadata ce env ty tv
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
  lookup_var ptr initial = SOME (n2w d) /\ not_fresh_at st ptr /\
  sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
    initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  (data_size = 0 \/ sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= data_size /\
    data_size < dimword (:256)) /\
  fresh_vars_wrt st initial /\ fn_has_code st st' func /\
  fn_inst_ids_distinct func /\
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
    alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
    d + type_memory_bytes ce ty <= actual.vs_alloca_next /\
    fresh_vars_wrt st' actual /\
    (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
    actual.vs_data_section = initial.vs_data_section /\
    actual.vs_call_ctx = initial.vs_call_ctx /\
    actual.vs_labels = initial.vs_labels /\
    (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
      lookup_var x actual = SOME w) /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial actual
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  rename1 `lookup_var pvar initial = SOME (n2w d)` >>
  drule ctor_arg_emit_shape >> strip_tac >>
  `st.cs_blocks = middle.cs_blocks` by simp[] >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  `st.cs_next_id <= middle.cs_next_id` by simp[] >>
  drule_all ctor_arg_decoder_code_phase >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule ctor_arg_add_reach >> simp_tac (srw_ss()) [eval_operand_def] >>
  disch_then drule_all >>
  disch_then (qspec_then `ctx` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qmatch_asmsub_abbrev_tac `abi_decode_sim ctx func initial prepared` >>
  `!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
    lookup_var x prepared = SOME w` by
    (rpt strip_tac >>
     qpat_x_assum `!op. abi_decoder_operand_live _ op ==> _`
       (qspec_then `Var x` mp_tac) >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
        not_fresh_at_def, eval_operand_def]) >>
  `abi_decoder_operand_live middle.cs_next_var src` by
    (irule abi_decoder_operand_live_fresh >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  `eval_operand src prepared = SOME (n2w sb)` by fs[] >>
  `sb < dimword (:256)` by decide_tac >>
  qpat_x_assum `st.cs_blocks = middle.cs_blocks` kall_tac >>
  irule ctor_arg_setup_decode_actual >> asm_rewrite_tac[] >>
  goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `abi_decode_sim _ _ _ _`)) >>
  asm_rewrite_tac[] >>
  simp[Abbr `prepared`, ctor_arg_register_observations,
       alloca_frontier_inv_def, abi_encoder_registered_effect_def, update_var_def] >>
  qexistsl [`av`, `env`, `sb`] >> simp[] >>
  Cases_on `data_size = 0` >> fs[]
QED

Theorem ctor_arg_dynamic_decode_actual[local]:
  !pvar sb off st head m1 rel m2 src middle ce ty data_size st' env tv av v initial d func ctx site.
  emit_op ADD [Lit 0w; Lit (n2w off)] st = (head,m1) /\
  emit_op DLOAD [head] m1 = (rel,m2) /\
  emit_op ADD [Lit 0w; rel] m2 = (src,middle) /\
  abi_decode_load DLOAD (n2w off : bytes32) initial = n2w sb /\
  compile_abi_decode_to_buf (Var pvar) src DLOAD (Lit (n2w data_size))
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) middle = ((),st') /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  abi_decoder_metadata ce env ty tv
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
  lookup_var pvar initial = SOME (n2w d) /\ not_fresh_at st pvar /\
  sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
    initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  (data_size = 0 \/ sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= data_size /\
    data_size < dimword (:256)) /\
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
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `cs_extends st m1 /\ cs_extends m1 m2 /\ cs_extends m2 middle /\
   m1.cs_blocks = st.cs_blocks /\ m2.cs_blocks = st.cs_blocks /\
   middle.cs_blocks = st.cs_blocks /\
   st.cs_next_id <= middle.cs_next_id /\ st.cs_next_var <= middle.cs_next_var` by
    (imp_res_tac ctor_arg_emit_shape >> simp[] >> decide_tac) >>
  `cs_extends st m2 /\ cs_extends st middle` by metis_tac[cs_extends_trans] >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all ctor_arg_decoder_code_phase >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `fn_has_code st m1 func /\ fn_has_code m1 m2 func /\ fn_has_code m2 middle func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  qpat_assum `emit_op ADD [Lit 0w; Lit (n2w off)] st = _`
    (mp_then Any mp_tac ctor_arg_add_reach) >>
  simp_tac (srw_ss()) [eval_operand_def] >> disch_then drule_all >>
  disch_then (qspec_then `ctx` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qmatch_asmsub_abbrev_tac `abi_decode_sim ctx func initial s1` >>
  `eval_operand head s1 = SOME (n2w off) /\ ~s1.vs_halted /\
   s1.vs_current_bb = m1.cs_current_bb /\ s1.vs_inst_idx = LENGTH m1.cs_current_insts` by
    fs[Abbr `s1`, update_var_def] >>
  drule ctor_arg_read_reach >> disch_then drule_all >>
  disch_then (qspec_then `ctx` (qx_choose_then `s2` (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `abi_decode_load DLOAD (n2w off : bytes32) s1 = n2w sb` by
    fs[abi_decode_load_def, abi_decode_source_def, Abbr `s1`, update_var_def] >>
  `eval_operand rel s2 = SOME (n2w sb) /\ s2.vs_inst_idx = LENGTH m2.cs_current_insts` by
    (conj_tac >- (qpat_assum `eval_operand rel s2 = _` (fn th => rewrite_tac[th]) >>
       simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `s2 = _` (fn th => simp[th])) >>
  `eval_operand (Lit 0w) s2 = SOME 0w` by simp[eval_operand_def] >>
  qpat_assum `emit_op ADD [Lit 0w; rel] m2 = _`
    (mp_then Any mp_tac ctor_arg_add_reach) >>
  disch_then drule_all >>
  disch_then (qspec_then `ctx` (qx_choose_then `prepared` (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `st.cs_next_var <= m1.cs_next_var /\ st.cs_next_var <= m2.cs_next_var` by
    (imp_res_tac ctor_arg_emit_shape >> decide_tac) >>
  `!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
    lookup_var x prepared = SOME w` by
    (rpt strip_tac >>
     `abi_decoder_operand_live st.cs_next_var (Var x) /\
      abi_decoder_operand_live m1.cs_next_var (Var x) /\
      abi_decoder_operand_live m2.cs_next_var (Var x)` by
       (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
        metis_tac[LESS_EQ_TRANS]) >>
     qpat_x_assum `!op. abi_decoder_operand_live m2.cs_next_var op ==> _`
       (qspec_then `Var x` mp_tac) >>
     qpat_x_assum `!op. abi_decoder_operand_live m1.cs_next_var op ==> _`
       (qspec_then `Var x` mp_tac) >>
     qpat_x_assum `!op. abi_decoder_operand_live st.cs_next_var op ==> _`
       (qspec_then `Var x` mp_tac) >>
     asm_rewrite_tac[eval_operand_def] >> metis_tac[]) >>
  `abi_decode_sim ctx func initial prepared` by
    metis_tac[abi_decode_sim_trans] >>
  `abi_decoder_operand_live middle.cs_next_var src` by
    (irule abi_decoder_operand_live_fresh >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  `eval_operand src prepared = SOME (n2w sb)` by
    (qpat_assum `eval_operand src prepared = _` mp_tac >>
     simp_tac (srw_ss()) [WORD_ADD_0]) >>
  irule ctor_arg_setup_decode_actual >> asm_rewrite_tac[] >>
  goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `abi_decode_sim _ _ initial prepared`)) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `prepared = _` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `s2 = _` (fn th => rewrite_tac[th]) >>
  simp[Abbr `s1`, ctor_arg_register_observations, alloca_frontier_inv_def,
       abi_encoder_registered_effect_def, update_var_def] >>
  qexistsl [`av`, `env`, `sb`] >> simp[] >>
  Cases_on `data_size = 0` >> fs[]
QED

Theorem compile_decode_constructor_arg_actual:
  !ce env fargs avs atys encoded i name ty tv v off data_size
   ptr d st st' ctx func site initial.
    i < LENGTH fargs /\ LENGTH avs = LENGTH fargs /\
    EL i fargs = (name,ty) /\
    atys = vyper_to_abi_types env (MAP SND fargs) /\
    has_types atys avs /\
    encoded = enc (Tuple atys) (ListV avs) /\
    off = SUM (MAP abi_member_head_size (TAKE i atys)) /\
    LENGTH encoded < dimword (:256) /\
    mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
    (data_size = 0 \/
      LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
    compile_decode_args ce [build_positional_arg ce (name,ty)] off
      DLOAD (Lit (n2w data_size)) 0 st = ((),st') /\
    FLOOKUP ce.ce_vars name =
      SOME (PtrVar (Var ptr) (type_memory_bytes ce ty)) /\
    lookup_var ptr initial = SOME (n2w d) /\ not_fresh_at st ptr /\
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    abi_decoder_metadata ce env ty tv
      (type_to_abi_dec_info ce.ce_struct_fields ce ty) (EL i avs) v /\
    fresh_vars_wrt st initial /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    (st.cs_blocks = st'.cs_blocks \/
      !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
    unit_alloca_budget ctx < dimword (:256) /\
    d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
    (!aid. st.cs_next_id <= aid ==>
      FLOOKUP initial.vs_allocas aid = NONE) /\
    ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts
    ==>
    ?actual.
      val_in_memory tv v d actual.vs_memory /\
      abi_encoder_registered_effect (frag_ids st st')
        [(d,type_memory_bytes ce ty)] initial actual /\
      alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
      d + type_memory_bytes ce ty <= actual.vs_alloca_next /\
      fresh_vars_wrt st' actual /\
      (!aid. st'.cs_next_id <= aid ==>
        FLOOKUP actual.vs_allocas aid = NONE) /\
      actual.vs_data_section = initial.vs_data_section /\
      actual.vs_call_ctx = initial.vs_call_ctx /\
      actual.vs_labels = initial.vs_labels /\
      (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
        lookup_var x actual = SOME w) /\
      ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
      actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
      abi_decode_sim ctx func initial actual
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all ctor_arg_member_source >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  rename1 `lookup_var pvar initial = SOME (n2w d)` >>
  `data_size <> 0 ==> abi_tuple_child_offset atys avs i +
     LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) <= data_size /\
     data_size < dimword (:256)` by metis_tac[LESS_EQ_TRANS] >>
  Cases_on `is_word_type ty`
  >- (`~is_abi_dynamic ce.ce_struct_fields ty` by
        (Cases_on `ty` >> fs[is_word_type_def, is_abi_dynamic_def] >>
         rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_word_type_def, is_abi_dynamic_def] >>
         rename1 `BytesT b` >> Cases_on `b` >> fs[is_word_type_def, is_abi_dynamic_def]) >>
      drule_all ctor_arg_primitive_code >> strip_tac >>
      qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _` mp_tac >>
      asm_rewrite_tac[] >> simp_tac (srw_ss()) [comp_bind_def, LET_THM] >>
      pairarg_tac >> asm_simp_tac (srw_ss()) [] >> strip_tac >>
      irule ctor_arg_add_decode_actual >> asm_rewrite_tac[] >>
      goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
      asm_rewrite_tac[] >> qexistsl [`EL i avs`, `env`] >> gvs[Excl "enc_def"]) >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty`
  >- (drule_all ctor_arg_dynamic_code >> strip_tac >>
      qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _` mp_tac >>
      asm_rewrite_tac[] >> simp_tac (srw_ss()) [comp_bind_def, LET_THM] >>
      pairarg_tac >> asm_simp_tac (srw_ss()) [] >>
      pairarg_tac >> asm_simp_tac (srw_ss()) [] >>
      pairarg_tac >> asm_simp_tac (srw_ss()) [] >> strip_tac >>
      irule ctor_arg_dynamic_decode_actual >> asm_rewrite_tac[] >>
      goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `emit_op ADD [Lit 0w; _] _ = _`)) >>
      goal_assum (drule_at (Pat `emit_op DLOAD _ _ = _`)) >>
      goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
      asm_rewrite_tac[] >> qexistsl [`EL i avs`, `env`, `abi_tuple_child_offset atys avs i`] >>
      gvs[Excl "enc_def"]) >>
  drule_all ctor_arg_static_code >> strip_tac >>
  qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [comp_bind_def, LET_THM] >>
  pairarg_tac >> asm_simp_tac (srw_ss()) [] >> strip_tac >>
  irule ctor_arg_add_decode_actual >> asm_rewrite_tac[] >>
  goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
  asm_rewrite_tac[] >> qexistsl [`EL i avs`, `env`] >> gvs[Excl "enc_def"]
QED
