(* Canonical constructor tuple source slices. *)
Theory ctorDeployLoweringEntryCanonical
Ancestors
 ctorDeployLoweringEntryAddress compileEnv exprLoweringProps abiDecoderTypedContract
 abiEncoderProps finite_map
 ctorRegisterArgs abiDecoderReentryAddress abiDecoderMemberSlice abiDecoderMemberBody
 abiDecoderCoherence abiDecoderContract abiEncoder vyperABI venomState venomInst venomExecSemantics
 words list rich_list arithmetic

Theorem deploy_ctor_canonical_member_split[local]:
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

Theorem deploy_ctor_canonical_member_source:
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
 strip_tac >> irule deploy_ctor_canonical_member_split >>
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

Theorem deploy_ctor_word_type_static[local]:
 is_word_type ty ==> ~is_abi_dynamic sf ty
Proof
 Cases_on `ty` >> simp[is_word_type_def, is_abi_dynamic_def] >>
 rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_word_type_def, is_abi_dynamic_def] >>
 rename1 `BytesT b` >> Cases_on `b` >> simp[is_word_type_def, is_abi_dynamic_def]
QED

Theorem deploy_ctor_eval_operand_not_fresh[local]:
 eval_operand op s = SOME w /\ fresh_vars_wrt st s ==>
 !x. op = Var x ==> not_fresh_at st x
Proof
 simp[eval_operand_def, not_fresh_at_def, fresh_vars_wrt_def] >>
 rpt strip_tac >> fs[eval_operand_def, lookup_var_def, GREATER_EQ, FLOOKUP_DEF] >>
 metis_tac[]
QED

Theorem deploy_ctor_canonical_singleton_prefix:
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
   compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit (n2w data_size))
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
   prepared.vs_gas_readings = initial.vs_gas_readings /\ prepared.vs_code = initial.vs_code /\
   prepared with <|vs_vars := initial.vs_vars; vs_inst_idx := initial.vs_inst_idx|> = initial /\
   abi_encoder_registered_effect {} [] initial prepared /\
   (!x v. not_fresh_at st x /\ lookup_var x initial = SOME v ==>
     lookup_var x prepared = SOME v) /\
   ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
   prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
   abi_decode_sim ctx func initial prepared
Proof
 qx_gen_tac `pvar` >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all deploy_ctor_canonical_member_source >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 drule abi_decoder_coherent_header >>
 simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
 drule_all deploy_ctor_singleton_address_prefix >>
 disch_then (qspec_then `ctx`
   (qx_choose_then `src` (qx_choose_then `middle`
     (qx_choose_then `prepared` (map_every assume_tac o CONJUNCTS))))) >>
 `eval_operand (Var pvar) prepared = SOME (n2w d)` by
   (simp[eval_operand_def] >> metis_tac[]) >>
 `prepared.vs_memory = initial.vs_memory /\ prepared.vs_allocas = initial.vs_allocas /\
  prepared.vs_alloca_next = initial.vs_alloca_next /\
  prepared.vs_data_section = initial.vs_data_section /\
  prepared.vs_call_ctx = initial.vs_call_ctx /\ prepared.vs_labels = initial.vs_labels /\
  prepared.vs_gas_readings = initial.vs_gas_readings /\ prepared.vs_code = initial.vs_code` by
   (qpat_x_assum `_ with <|vs_vars := _; vs_inst_idx := _|> = initial` mp_tac >>
    simp[venom_state_component_equality]) >>
 qexistsl [`src`, `middle`, `prepared`, `abi_tuple_child_offset atys avs i`] >>
 asm_rewrite_tac[] >>
 conj_tac
 >- (Cases_on `is_abi_dynamic ce.ce_struct_fields ty` >>
     fs[deploy_ctor_word_type_static] >> metis_tac[deploy_ctor_word_type_static]) >>
 conj_tac
 >- metis_tac[deploy_ctor_eval_operand_not_fresh, operand_distinct] >>
 qpat_assum `EL i atys = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
 asm_rewrite_tac[] >>
 metis_tac[LESS_EQ_LESS_TRANS, LESS_EQ_TRANS]
QED
