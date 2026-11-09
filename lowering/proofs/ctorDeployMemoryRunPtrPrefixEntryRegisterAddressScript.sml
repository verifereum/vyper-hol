(* Address computation with ambient projections at the paired endpoint. *)
Theory ctorDeployMemoryRunPtrPrefixEntryRegisterAddress
Ancestors
  loweringStateRelDefs
 ctorDeployMemoryRunPtrPrefixRegisterAddress ctorDeployMemoryRunPtrPrefixBoolBody
 ctorDeployMemoryRunPtrPrefixMemberSetup abiDecoderReentryAddress
 ctorRegisterArgs compileEnv emitHelperProps fragExec abiDecoderLoop exprLoweringProps
 ptrSafeRun ptrDiscipline venomState venomExecSemantics venomInst
 finite_map words arithmetic pred_set list rich_list
 abiDecoderContract abiEncoderRegisteredEffect
 ctorDeployLoweringEntryCanonical abiDecoderCoherence abiEncoderProps context

Theorem prefix_entry_register_address_add_actual:
 emit_op ADD [a;b] st = (out,middle) /\
 eval_operand a initial = SOME u /\ eval_operand b initial = SOME v /\
 op_taint tn a = {} /\ op_taint tn b = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
 fresh_vars_wrt st initial /\ fn_has_code st middle func /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?prepared H qt.
 eval_operand out prepared = SOME (u+v) /\ op_taint qt out = {} /\
 fresh_vars_wrt middle prepared /\
 prepared.vs_memory = initial.vs_memory /\ prepared.vs_allocas = initial.vs_allocas /\
 prepared.vs_alloca_next = initial.vs_alloca_next /\
 prepared.vs_data_section = initial.vs_data_section /\
 prepared.vs_call_ctx = initial.vs_call_ctx /\ prepared.vs_labels = initial.vs_labels /\
 abi_encoder_registered_effect {} [] initial prepared /\
 (!x v. not_fresh_at st x /\ lookup_var x initial = SOME v ==>
   lookup_var x prepared = SOME v) /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
   op_taint qt (Var x) = op_taint tn (Var x)) /\
 qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
 qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
 prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
 abi_decode_sim ctx func initial prepared /\
 prepared.vs_code = initial.vs_code /\ prepared.vs_outcomes = initial.vs_outcomes /\
 prepared.vs_tx_ctx = initial.vs_tx_ctx /\ prepared.vs_block_ctx = initial.vs_block_ctx /\
 prepared.vs_gas_readings = initial.vs_gas_readings /\
 ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt prepared) ==>
   !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
 strip_tac >>
 `run_inst_seq (emitted_insts st middle) initial =
   OK (update_var (STRING #"%" (toString st.cs_next_var)) (u+v) initial)` by
   (drule emitted_insts_emit_op >> strip_tac >>
    `step_inst_base (mk_inst st.cs_next_id ADD [a;b]
      [STRING #"%" (toString st.cs_next_var)]) initial =
      OK (update_var (STRING #"%" (toString st.cs_next_var)) (u+v) initial)` by
      (irule prefix_bool_body_add_step >> simp[]) >>
    simp[run_inst_seq_def]) >>
 drule_all (SRULE [is_terminator_def]
   (Q.INST [`opc` |-> `ADD`] prefix_register_address_emit_finish)) >>
 disch_then (qspec_then `ctx` mp_tac) >> simp_tac bool_ss [LET_THM] >> strip_tac >>
 qexistsl [`(update_var (STRING #"%" (toString st.cs_next_var)) (u+v) initial)
     with vs_inst_idx := LENGTH middle.cs_current_insts`,
   `set_prov G [STRING #"%" (toString st.cs_next_var)] (first_prov G [a;b])`,
   `tn with t_var := tn.t_var |+ (STRING #"%" (toString st.cs_next_var),{})`] >>
 drule prefix_register_address_emit_shape >> strip_tac >> simp[update_var_def] >>
 conj_tac >- simp[op_taint_def, FLOOKUP_UPDATE] >>
 conj_tac >-
   (rpt strip_tac >>
    `x <> STRING #"%" (toString st.cs_next_var)` by
      (strip_tac >> gvs[not_fresh_at_def]) >>
    Cases_on `first_prov G [a;b]` >>
    simp[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]) >>
 drule_all prefix_register_address_add_run >> simp[update_var_def]
QED

Theorem prefix_entry_register_address_dload_actual:
 emit_op DLOAD [off] st = (out,middle) /\
 eval_operand off initial = SOME a /\ op_taint tn off = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
 fresh_vars_wrt st initial /\ fn_has_code st middle func /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?prepared H qt.
 eval_operand out prepared = SOME (abi_decode_load DLOAD a initial) /\
 op_taint qt out = {} /\ fresh_vars_wrt middle prepared /\
 prepared.vs_memory = initial.vs_memory /\ prepared.vs_allocas = initial.vs_allocas /\
 prepared.vs_alloca_next = initial.vs_alloca_next /\
 prepared.vs_data_section = initial.vs_data_section /\
 prepared.vs_call_ctx = initial.vs_call_ctx /\ prepared.vs_labels = initial.vs_labels /\
 abi_encoder_registered_effect {} [] initial prepared /\
 (!x v. not_fresh_at st x /\ lookup_var x initial = SOME v ==>
   lookup_var x prepared = SOME v) /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
   op_taint qt (Var x) = op_taint tn (Var x)) /\
 qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
 qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
 prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
 abi_decode_sim ctx func initial prepared /\
 prepared.vs_code = initial.vs_code /\ prepared.vs_outcomes = initial.vs_outcomes /\
 prepared.vs_tx_ctx = initial.vs_tx_ctx /\ prepared.vs_block_ctx = initial.vs_block_ctx /\
 prepared.vs_gas_readings = initial.vs_gas_readings /\
 ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt prepared) ==>
   !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
 strip_tac >>
 `step_inst_base (mk_inst st.cs_next_id DLOAD [off]
     [STRING #"%" (toString st.cs_next_var)]) initial =
     OK (update_var (STRING #"%" (toString st.cs_next_var))
       (abi_decode_load DLOAD a initial) initial)` by
   (irule (cj 1 (SRULE [LET_THM] prefix_member_dload_pair)) >> metis_tac[]) >>
 `run_inst_seq (emitted_insts st middle) initial =
    OK (update_var (STRING #"%" (toString st.cs_next_var))
      (abi_decode_load DLOAD a initial) initial)` by
   (drule emitted_insts_emit_op >> strip_tac >> simp[run_inst_seq_def]) >>
 drule_all (SRULE [is_terminator_def]
   (Q.INST [`opc` |-> `DLOAD`] prefix_register_address_emit_finish)) >>
 disch_then (qspec_then `ctx` mp_tac) >> simp_tac bool_ss [LET_THM] >> strip_tac >>
 qexistsl [`(update_var (STRING #"%" (toString st.cs_next_var))
     (abi_decode_load DLOAD a initial) initial)
     with vs_inst_idx := LENGTH middle.cs_current_insts`,
   `DRESTRICT G (COMPL {STRING #"%" (toString st.cs_next_var)})`,
   `tn with t_var := tn.t_var |+ (STRING #"%" (toString st.cs_next_var),{})`] >>
 drule prefix_register_address_emit_shape >> strip_tac >> simp[update_var_def] >>
 conj_tac >- simp[op_taint_def, FLOOKUP_UPDATE] >>
 conj_tac >-
   (rpt strip_tac >>
    `x <> STRING #"%" (toString st.cs_next_var)` by
      (strip_tac >> gvs[not_fresh_at_def]) >>
    simp[FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE]) >>
 drule_all (SRULE [] (Q.INST
   [`w` |-> `abi_decode_load DLOAD a s`] prefix_register_address_dload_run)) >>
 simp[update_var_def]
QED

Theorem prefix_entry_register_address_dynamic_actual:
 emit_op ADD [Lit 0w;Lit (n2w off)] st = (head,first) /\
 emit_op DLOAD [head] first = (offset,second) /\
 emit_op ADD [Lit 0w;offset] second = (src,middle) /\
 fresh_vars_wrt st initial /\ fn_has_code st middle func /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?prepared H qt.
 eval_operand src prepared = SOME (abi_decode_load DLOAD (n2w off : bytes32) initial) /\
 op_taint qt src = {} /\ fresh_vars_wrt middle prepared /\
 prepared.vs_memory = initial.vs_memory /\ prepared.vs_allocas = initial.vs_allocas /\
 prepared.vs_alloca_next = initial.vs_alloca_next /\
 prepared.vs_data_section = initial.vs_data_section /\
 prepared.vs_call_ctx = initial.vs_call_ctx /\ prepared.vs_labels = initial.vs_labels /\
 abi_encoder_registered_effect {} [] initial prepared /\
 (!x v. not_fresh_at st x /\ lookup_var x initial = SOME v ==>
   lookup_var x prepared = SOME v) /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
   op_taint qt (Var x) = op_taint tn (Var x)) /\
 qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
 qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
 prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
 abi_decode_sim ctx func initial prepared /\
 prepared.vs_code = initial.vs_code /\ prepared.vs_outcomes = initial.vs_outcomes /\
 prepared.vs_tx_ctx = initial.vs_tx_ctx /\ prepared.vs_block_ctx = initial.vs_block_ctx /\
 prepared.vs_gas_readings = initial.vs_gas_readings /\
 ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt prepared) ==>
   !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
 strip_tac >>
 `cs_extends st first /\ cs_extends first second /\ cs_extends second middle /\
  first.cs_next_var = st.cs_next_var+1 /\
  second.cs_next_var = first.cs_next_var+1` by
   metis_tac[prefix_register_address_emit_shape] >>
 `cs_extends first middle` by metis_tac[cs_extends_trans] >>
 `fn_has_code st first func /\ fn_has_code first second func /\
  fn_has_code second middle func` by metis_tac[fn_has_code_split] >>
 drule_all (SRULE [eval_operand_def, op_taint_def]
   (Q.INST [`a` |-> `Lit 0w`, `b` |-> `Lit (n2w off)`,
            `u` |-> `0w`, `v` |-> `n2w off`]
     prefix_entry_register_address_add_actual)) >>
 disch_then (qspecl_then [`tn`,`PG`,`G`,`D`]
   (qx_choose_then `p1` (qx_choose_then `H1`
     (qx_choose_then `q1` strip_assume_tac)))) >>
 `allocas_from lo p1` by metis_tac[allocas_from_def] >>
 `op_taint q1 head = {}` by fs[op_taint_def] >>
 drule_all prefix_entry_register_address_dload_actual >>
 disch_then (qspecl_then [`PG`,`H1`,`D`]
   (qx_choose_then `p2` (qx_choose_then `H2`
     (qx_choose_then `q2` strip_assume_tac)))) >>
 `allocas_from lo p2` by metis_tac[allocas_from_def] >>
 `eval_operand (Lit 0w) p2 = SOME 0w /\ op_taint q2 (Lit 0w) = {}` by
   simp[eval_operand_def, op_taint_def] >>
 drule_all (Q.INST [`a` |-> `Lit 0w`] prefix_entry_register_address_add_actual) >>
 disch_then (qspecl_then [`PG`,`H2`,`D`]
   (qx_choose_then `p3` (qx_choose_then `H3`
     (qx_choose_then `q3` strip_assume_tac)))) >>
 `abi_decode_load DLOAD (0w + n2w off : bytes32) p1 =
    abi_decode_load DLOAD (n2w off : bytes32) initial` by
   simp[abi_decode_load_def, abi_decode_source_def, WORD_ADD_0] >>
 `!x. not_fresh_at st x ==> not_fresh_at first x /\ not_fresh_at second x` by
   (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
 qexistsl [`p3`,`H3`,`q3`] >> simp[WORD_ADD_0] >>
 conj_tac >- metis_tac[abi_encoder_registered_effect_trans] >>
 conj_tac >- (rpt strip_tac >> fs[op_taint_def]) >>
 metis_tac[abi_decode_sim_trans]
QED

Theorem prefix_entry_register_singleton_address_paired:
 !ptr. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ptr) (type_memory_bytes ce ty)) /\
 compile_decode_args ce [build_positional_arg ce (name,ty)] off
   DLOAD (Lit 0w) 0 st = ((),last) /\
 fresh_vars_wrt st initial /\ fn_has_code st last func /\
 (st.cs_blocks = last.cs_blocks \/ !bb.
   lookup_block last.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?src middle prepared H qt.
 compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit 0w)
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) middle = ((),last) /\
 eval_operand src prepared = SOME
   (if ~is_word_type ty /\ is_abi_dynamic ce.ce_struct_fields ty
    then abi_decode_load DLOAD (n2w off : bytes32) initial else n2w off) /\
 op_taint qt src = {} /\ fresh_vars_wrt middle prepared /\
 cs_extends st middle /\ middle.cs_blocks = st.cs_blocks /\
 st.cs_next_var <= middle.cs_next_var /\ st.cs_next_id <= middle.cs_next_id /\
 fn_has_code middle last func /\ frag_ids middle last SUBSET frag_ids st last /\
 (middle.cs_blocks = last.cs_blocks \/ !bb.
   lookup_block last.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 prepared.vs_memory = initial.vs_memory /\ prepared.vs_allocas = initial.vs_allocas /\
 prepared.vs_alloca_next = initial.vs_alloca_next /\
 prepared.vs_data_section = initial.vs_data_section /\
 prepared.vs_call_ctx = initial.vs_call_ctx /\ prepared.vs_labels = initial.vs_labels /\
 abi_encoder_registered_effect {} [] initial prepared /\
 (!x v. not_fresh_at st x /\ lookup_var x initial = SOME v ==>
   lookup_var x prepared = SOME v) /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
   op_taint qt (Var x) = op_taint tn (Var x)) /\
 qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
 qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
 prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
 abi_decode_sim ctx func initial prepared /\
 prepared.vs_code = initial.vs_code /\ prepared.vs_outcomes = initial.vs_outcomes /\
 prepared.vs_tx_ctx = initial.vs_tx_ctx /\ prepared.vs_block_ctx = initial.vs_block_ctx /\
 prepared.vs_gas_readings = initial.vs_gas_readings /\
 ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt prepared) ==>
   !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
 gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all (Q.INST [`data_size` |-> `0`] ctor_singleton_decode_phases) >>
 strip_tac
 >- (qpat_x_assum `src = static_src` SUBST_ALL_TAC >>
     qpat_x_assum `middle = first` SUBST_ALL_TAC >>
     drule prefix_register_address_emit_shape >> strip_tac >>
     `st.cs_next_id <= first.cs_next_id` by decide_tac >>
     drule_all prefix_register_address_code_phase >> strip_tac >>
     drule_all (SRULE [eval_operand_def, op_taint_def]
       (Q.INST [`a` |-> `Lit 0w`, `b` |-> `Lit (n2w off)`,
                `u` |-> `0w`, `v` |-> `n2w off`]
         prefix_entry_register_address_add_actual)) >>
     disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
     qexistsl [`static_src`,`first`,`prepared`,`H`,`qt`] >>
     gvs[WORD_ADD_0, op_taint_def]) >>
 `cs_extends st middle /\ middle.cs_blocks = st.cs_blocks /\
  st.cs_next_var <= middle.cs_next_var /\ st.cs_next_id <= middle.cs_next_id` by
   (imp_res_tac prefix_register_address_emit_shape >>
    conj_tac >- metis_tac[cs_extends_trans] >> simp[]) >>
 drule_all prefix_register_address_code_phase >> strip_tac >>
 drule_all prefix_entry_register_address_dynamic_actual >>
 disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
 qexistsl [`src`,`middle`,`prepared`,`H`,`qt`] >> gvs[]
QED

Theorem prefix_entry_register_word_static[local]:
 is_word_type ty ==> ~is_abi_dynamic sf ty
Proof
 Cases_on `ty` >> simp[is_word_type_def, is_abi_dynamic_def] >>
 rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_word_type_def, is_abi_dynamic_def] >>
 rename1 `BytesT b` >> Cases_on `b` >> simp[is_word_type_def, is_abi_dynamic_def]
QED

Theorem prefix_entry_register_operand_live[local]:
 eval_operand op s = SOME w /\ fresh_vars_wrt st s ==>
 !x. op = Var x ==> not_fresh_at st x
Proof
 simp[eval_operand_def, not_fresh_at_def, fresh_vars_wrt_def] >>
 rpt strip_tac >> fs[eval_operand_def, lookup_var_def, GREATER_EQ, FLOOKUP_DEF] >>
 metis_tac[]
QED

Theorem prefix_entry_register_canonical_address_paired:
 !ptr. i < LENGTH atys /\ LENGTH avs = LENGTH atys /\
 EL i atys = vyper_to_abi_type env ty /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 LENGTH encoded < dimword (:256) /\
 off = SUM (MAP abi_member_head_size (TAKE i atys)) /\
 abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
 FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ptr) (type_memory_bytes ce ty)) /\
 lookup_var ptr initial = SOME (n2w d) /\ not_fresh_at st ptr /\
 compile_decode_args ce [build_positional_arg ce (name,ty)] off
   DLOAD (Lit 0w) 0 st = ((),last) /\
 fresh_vars_wrt st initial /\ fn_has_code st last func /\
 (st.cs_blocks = last.cs_blocks \/ !bb.
   lookup_block last.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?src middle prepared sb H qt.
 compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit 0w)
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) middle = ((),last) /\
 eval_operand src prepared = SOME (n2w sb) /\
 eval_operand (Var ptr) prepared = SOME (n2w d) /\
 (!x. src = Var x \/ Var ptr = Var x \/ Lit 0w = Var x ==> not_fresh_at middle x) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)))
   prepared.vs_data_section = enc (vyper_to_abi_type env ty) (EL i avs) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) < dimword (:256) /\
 op_taint qt src = {} /\ fresh_vars_wrt middle prepared /\
 cs_extends st middle /\ middle.cs_blocks = st.cs_blocks /\
 st.cs_next_var <= middle.cs_next_var /\ st.cs_next_id <= middle.cs_next_id /\
 fn_has_code middle last func /\ frag_ids middle last SUBSET frag_ids st last /\
 (middle.cs_blocks = last.cs_blocks \/ !bb.
   lookup_block last.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 prepared.vs_memory = initial.vs_memory /\ prepared.vs_allocas = initial.vs_allocas /\
 prepared.vs_alloca_next = initial.vs_alloca_next /\ allocas_from lo prepared /\
 prepared.vs_data_section = initial.vs_data_section /\
 prepared.vs_call_ctx = initial.vs_call_ctx /\ prepared.vs_labels = initial.vs_labels /\
 abi_encoder_registered_effect {} [] initial prepared /\
 (!x v. not_fresh_at st x /\ lookup_var x initial = SOME v ==>
   lookup_var x prepared = SOME v) /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
   op_taint qt (Var x) = op_taint tn (Var x)) /\
 qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
 qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
 prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
 abi_decode_sim ctx func initial prepared /\
 prepared.vs_code = initial.vs_code /\ prepared.vs_outcomes = initial.vs_outcomes /\
 prepared.vs_tx_ctx = initial.vs_tx_ctx /\ prepared.vs_block_ctx = initial.vs_block_ctx /\
 prepared.vs_gas_readings = initial.vs_gas_readings /\
 ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt prepared) ==>
   !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
 gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all deploy_ctor_canonical_member_source >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 drule abi_decoder_coherent_header >>
 simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
 drule_all prefix_entry_register_singleton_address_paired >>
 disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] mp_tac) >>
 disch_then (qx_choose_then `src` (qx_choose_then `middle`
   (qx_choose_then `prepared` (qx_choose_then `H` (qx_choose_then `qt`
     (map_every assume_tac o CONJUNCTS)))))) >>
 `eval_operand (Var ptr') prepared = SOME (n2w d)` by
   (simp[eval_operand_def] >> metis_tac[]) >>
 qexistsl [`src`,`middle`,`prepared`,`abi_tuple_child_offset atys avs i`,`H`,`qt`] >>
 asm_rewrite_tac[] >>
 conj_tac
 >- (Cases_on `is_abi_dynamic ce.ce_struct_fields ty` >>
     fs[prefix_entry_register_word_static] >> metis_tac[prefix_entry_register_word_static]) >>
 conj_tac
 >- metis_tac[prefix_entry_register_operand_live, operand_distinct] >>
 qpat_assum `EL i atys = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
 asm_rewrite_tac[] >>
 conj_tac >- (gvs[Excl "enc_def"] >> decide_tac) >>
 simp_tac bool_ss [allocas_from_def] >>
 qpat_x_assum `allocas_from lo initial` mp_tac >>
 asm_simp_tac bool_ss [allocas_from_def]
QED

val _ = export_theory();
