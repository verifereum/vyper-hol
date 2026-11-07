(* Register-only constructor argument address preparation. *)
Theory ctorDeployLoweringEntryAddress
Ancestors
 abiDecoderAppend abiDecoderCounters abiDecoderCode
 ctorRegisterArgs abiDecoderReentryAddress abiDecoderReentry abiDecoderContract
 abiDecoderVarSequence abiDecoderLoop abiDecoderCoherence abiEncoderRegisteredEffect abiEncoderProps
 compileEnv exprLoweringProps emitHelper emitHelperProps context fragExec
 instIdxIndep venomExecSemantics venomState venomInst
 words list finite_map pred_set arithmetic

Theorem deploy_ctor_emit_prefix_shape:
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

Theorem deploy_ctor_prefix_sequence_reach[local]:
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

Theorem deploy_ctor_register_prefix_finish[local]:
 emit_op opc ops st = (out,middle) /\ opc <> INVOKE /\ ~is_terminator opc /\
 run_inst_seq (emitted_insts st middle) initial =
   OK (update_var (STRING #"%" (toString st.cs_next_var)) w initial) /\
 fresh_vars_wrt st initial /\ fn_has_code st middle func /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?prepared.
   eval_operand out prepared = SOME w /\ fresh_vars_wrt middle prepared /\
   prepared with <|vs_vars := initial.vs_vars; vs_inst_idx := initial.vs_inst_idx|> = initial /\
   abi_encoder_registered_effect {} [] initial prepared /\
   (!x v. not_fresh_at st x /\ lookup_var x initial = SOME v ==>
     lookup_var x prepared = SOME v) /\
   ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
   prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
   abi_decode_sim ctx func initial prepared
Proof
 strip_tac >> drule deploy_ctor_emit_prefix_shape >> strip_tac >>
 `inst_extends st middle` by metis_tac[inst_extends_emit_op] >>
 `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
   (emitted_insts st middle)` by
   (drule emitted_insts_emit_op >> simp[mk_inst_def]) >>
 drule_all deploy_ctor_prefix_sequence_reach >>
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

Theorem deploy_ctor_add_prefix_actual:
 emit_op ADD [lhs;rhs] st = (out,middle) /\
 eval_operand lhs initial = SOME a /\ eval_operand rhs initial = SOME b /\
 fresh_vars_wrt st initial /\ fn_has_code st middle func /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?prepared.
   eval_operand out prepared = SOME (a+b) /\ fresh_vars_wrt middle prepared /\
   prepared with <|vs_vars := initial.vs_vars; vs_inst_idx := initial.vs_inst_idx|> = initial /\
   abi_encoder_registered_effect {} [] initial prepared /\
   (!x v. not_fresh_at st x /\ lookup_var x initial = SOME v ==>
     lookup_var x prepared = SOME v) /\
   ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
   prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
   abi_decode_sim ctx func initial prepared
Proof
 strip_tac >> drule deploy_ctor_emit_prefix_shape >> strip_tac >>
 `fresh_vars_wrt middle initial` by
   (irule fresh_vars_wrt_mono >> qexists `st` >> simp[GREATER_EQ]) >>
 drule abi_decoder_binary_reentry >>
 disch_then (qspecl_then [`initial`, `middle`] mp_tac) >>
 simp[] >> strip_tac >>
 drule deploy_ctor_register_prefix_finish >>
 simp[is_terminator_def] >> disch_then irule >> simp[]
QED

Theorem deploy_ctor_dload_prefix_actual:
 emit_op DLOAD [src] st = (out,middle) /\
 eval_operand src initial = SOME p /\
 fresh_vars_wrt st initial /\ fn_has_code st middle func /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?prepared.
   eval_operand out prepared = SOME (abi_decode_load DLOAD p initial) /\
   fresh_vars_wrt middle prepared /\
   prepared with <|vs_vars := initial.vs_vars; vs_inst_idx := initial.vs_inst_idx|> = initial /\
   abi_encoder_registered_effect {} [] initial prepared /\
   (!x v. not_fresh_at st x /\ lookup_var x initial = SOME v ==>
     lookup_var x prepared = SOME v) /\
   ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
   prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
   abi_decode_sim ctx func initial prepared
Proof
 strip_tac >> drule deploy_ctor_emit_prefix_shape >> strip_tac >>
 `fresh_vars_wrt middle initial` by
   (irule fresh_vars_wrt_mono >> qexists `st` >> simp[GREATER_EQ]) >>
 drule abi_decoder_read_reentry >>
 disch_then (qspecl_then [`initial`, `p`, `middle`] mp_tac) >>
 simp[abi_decode_source_opcode_def] >> strip_tac >>
 drule deploy_ctor_register_prefix_finish >>
 simp[is_terminator_def] >> disch_then irule >> simp[]
QED

Theorem deploy_ctor_prefix_decoder_code_phase[local]:
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

Theorem deploy_ctor_prefix_reset_trans[local]:
 t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s /\
 u with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> = t ==>
 u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s
Proof
 simp[venom_state_component_equality]
QED

Theorem deploy_ctor_prefix_reset_load[local]:
 t with <|vs_vars := s.vs_vars; vs_inst_idx := k|> = s ==>
 abi_decode_load DLOAD p t = abi_decode_load DLOAD p s
Proof
 simp[venom_state_component_equality, abi_decode_load_def, abi_decode_source_def]
QED

Theorem deploy_ctor_dynamic_address_prefix[local]:
 emit_op ADD [Lit 0w; Lit (n2w off)] st = (head,first) /\
 emit_op DLOAD [head] first = (offset_val,second) /\
 emit_op ADD [Lit 0w; offset_val] second = (src,middle) /\
 fn_has_code st middle func /\ fresh_vars_wrt st initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?prepared.
   eval_operand src prepared = SOME (abi_decode_load DLOAD (n2w off : bytes32) initial) /\
   fresh_vars_wrt middle prepared /\
   prepared with <|vs_vars := initial.vs_vars; vs_inst_idx := initial.vs_inst_idx|> = initial /\
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
   metis_tac[deploy_ctor_emit_prefix_shape] >>
 `cs_extends first middle` by metis_tac[cs_extends_trans] >>
 `fn_has_code st first func /\ fn_has_code first second func /\
  fn_has_code second middle func` by metis_tac[fn_has_code_split] >>
 qpat_assum `emit_op ADD _ st = _`
   (mp_then Any mp_tac deploy_ctor_add_prefix_actual) >>
 disch_then (qspecl_then [`initial`, `func`, `ctx`] mp_tac) >>
 simp[eval_operand_def] >> strip_tac >>
 rename1 `eval_operand head p1 = _` >>
 `eval_operand head p1 = SOME (n2w off)` by fs[] >>
 drule_all deploy_ctor_dload_prefix_actual >>
 disch_then (qspec_then `ctx` strip_assume_tac) >>
 rename1 `eval_operand offset_val p2 = _` >>
 qpat_assum `emit_op ADD _ second = _`
   (mp_then Any mp_tac deploy_ctor_add_prefix_actual) >>
 disch_then (qspecl_then [`p2`, `func`, `ctx`] mp_tac) >>
 simp[eval_operand_def] >> strip_tac >>
 rename1 `eval_operand src p3 = _` >>
 `abi_decode_load DLOAD (n2w off : bytes32) p1 = abi_decode_load DLOAD (n2w off : bytes32) initial` by
   (irule deploy_ctor_prefix_reset_load >> goal_assum (drule_at Any)) >>
 qexists `p3` >> simp[] >>
 conj_tac >- metis_tac[deploy_ctor_prefix_reset_trans] >>
 conj_tac >- metis_tac[abi_encoder_registered_effect_trans] >>
 conj_tac
 >- (rpt strip_tac >>
     `not_fresh_at first x /\ not_fresh_at second x` by
       (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
     metis_tac[]) >>
 metis_tac[abi_decode_sim_trans]
QED

Theorem deploy_ctor_singleton_address_prefix:
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
   compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit (n2w data_size))
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
   prepared with <|vs_vars := initial.vs_vars; vs_inst_idx := initial.vs_inst_idx|> = initial /\
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
     drule deploy_ctor_emit_prefix_shape >> strip_tac >>
     `st.cs_next_id <= first.cs_next_id` by decide_tac >>
     drule_all deploy_ctor_prefix_decoder_code_phase >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     drule deploy_ctor_add_prefix_actual >>
     disch_then (qspecl_then [`initial`, `func`, `ctx`] mp_tac) >>
     simp[eval_operand_def] >> strip_tac >>
     qexistsl [`static_src`, `first`, `prepared`] >> simp[]) >>
 `cs_extends st middle /\ middle.cs_blocks = st.cs_blocks /\
  st.cs_next_var <= middle.cs_next_var /\ st.cs_next_id <= middle.cs_next_id` by
   (imp_res_tac deploy_ctor_emit_prefix_shape >>
    conj_tac >- metis_tac[cs_extends_trans] >> simp[]) >>
 drule_all deploy_ctor_prefix_decoder_code_phase >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all deploy_ctor_dynamic_address_prefix >>
 disch_then (qspec_then `ctx` strip_assume_tac) >>
 qexistsl [`src`, `middle`, `prepared`] >> simp[]
QED
