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
  slotCopyExecution ctorDeployMemoryRunMemEntryRegistration fragGasPathMem abiEncoderWindowMembers
  fragGasOriginPtr fragGasOriginPtrLoop

val RegisterAddressAddMode = ``\checked.
 emit_op ADD [a;b] st = (out,middle) /\
 eval_operand a initial = SOME u /\ eval_operand b initial = SOME v /\
 (checked ==> alloca_history func initial) /\
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
   !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial) /\
 (checked ==> !D explicit. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (initial, G, tn) [] (OK prepared, H, qt)) /\
 (checked ==> gas_path_mem ctx func initial 0 (OK prepared) /\ alloca_history func prepared)``;

Theorem prefix_entry_register_address_add_actual_mode:
 !checked. (^RegisterAddressAddMode) checked
Proof
 gen_tac >> BETA_TAC >> strip_tac >>
 `run_inst_seq (emitted_insts st middle) initial =
   OK (update_var (STRING #"%" (toString st.cs_next_var)) (u+v) initial)` by
   (drule emitted_insts_emit_op >> strip_tac >>
    `step_inst_base (mk_inst st.cs_next_id ADD [a;b]
      [STRING #"%" (toString st.cs_next_var)]) initial =
      OK (update_var (STRING #"%" (toString st.cs_next_var)) (u+v) initial)` by
      (irule slotCopyExecutionTheory.slot_copy_step_add >> simp[]) >>
    simp[run_inst_seq_def]) >>
 `!D' explicit. gas_origin_ptr_path (D', lo, explicit, ctx, func, PG) (initial, G, tn) []
    (OK ((update_var (STRING #"%" (toString st.cs_next_var)) (u+v) initial) with vs_inst_idx := LENGTH middle.cs_current_insts),
     set_prov G [STRING #"%" (toString st.cs_next_var)] (first_prov G [a;b]),
     tn with t_var := tn.t_var |+ (STRING #"%" (toString st.cs_next_var),{}))` by
   (rpt gen_tac >> drule emitted_insts_emit_op >> strip_tac >>
    `ghost_step 0 ctx PG G tn (mk_inst st.cs_next_id ADD [a;b] [STRING #"%" (toString st.cs_next_var)]) initial =
       (set_prov G [STRING #"%" (toString st.cs_next_var)] (first_prov G [a;b]),
        tn with t_var := tn.t_var |+ (STRING #"%" (toString st.cs_next_var),{}))` by
      (`step_taint (mk_inst st.cs_next_id ADD [a;b] [STRING #"%" (toString st.cs_next_var)]) initial
          (update_var (STRING #"%" (toString st.cs_next_var)) (u+v) initial) tn =
        tn with t_var := tn.t_var |+ (STRING #"%" (toString st.cs_next_var),{})` by
         (irule prefix_member_add_taint >> simp[]) >>
       pop_assum (fn th => pure_once_rewrite_tac[GSYM th]) >>
       irule (SRULE [LET_THM] prefix_bool_body_add_ghost) >> simp[]) >>
    drule prefix_register_address_emit_origin >> disch_then irule >>
    gvs[is_terminator_def, prefix_bool_body_arith_ptr_step] >>
     simp[mk_inst_def, inst_mem_below_frontier_def, inst_dload_in_section_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
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
 conj_tac >- (drule_all prefix_register_address_add_run >> simp[update_var_def]) >>
 conj_tac >-
   (qpat_x_assum `!D' explicit. gas_origin_ptr_path _ _ _ _` mp_tac >>
    simp[update_var_def]) >>
 strip_tac >> `alloca_history func initial` by metis_tac[] >>
 drule_all ctor_checked_arg_add_reach >> strip_tac >> gvs[update_var_def]
QED


val RegisterAddressDloadMode = ``\checked.
 emit_op DLOAD [off] st = (out,middle) /\
 eval_operand off initial = SOME a /\ op_taint tn off = {} /\
 (checked ==> w2n a + 32 <= LENGTH initial.vs_data_section /\ alloca_history func initial) /\
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
   !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial) /\
 (checked ==> !D explicit. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (initial, G, tn) [] (OK prepared, H, qt)) /\
 (checked ==> gas_path_mem ctx func initial 0 (OK prepared) /\ alloca_history func prepared)``;

Theorem prefix_entry_register_address_dload_actual_mode:
 !checked. (^RegisterAddressDloadMode) checked
Proof
 gen_tac >> BETA_TAC >> strip_tac >>
 `step_inst_base (mk_inst st.cs_next_id DLOAD [off]
     [STRING #"%" (toString st.cs_next_var)]) initial =
     OK (update_var (STRING #"%" (toString st.cs_next_var))
       (abi_decode_load DLOAD a initial) initial)` by
   (irule (cj 1 (SRULE [LET_THM] prefix_member_dload_pair)) >> metis_tac[]) >>
 `run_inst_seq (emitted_insts st middle) initial =
    OK (update_var (STRING #"%" (toString st.cs_next_var))
      (abi_decode_load DLOAD a initial) initial)` by
   (drule emitted_insts_emit_op >> strip_tac >> simp[run_inst_seq_def]) >>
 `checked ==> !D' explicit. gas_origin_ptr_path (D', lo, explicit, ctx, func, PG) (initial, G, tn) []
    (OK ((update_var (STRING #"%" (toString st.cs_next_var)) (abi_decode_load DLOAD a initial) initial)
           with vs_inst_idx := LENGTH middle.cs_current_insts),
     DRESTRICT G (COMPL {STRING #"%" (toString st.cs_next_var)}),
     tn with t_var := tn.t_var |+ (STRING #"%" (toString st.cs_next_var),{}))` by
   (rpt strip_tac >>
    `w2n a + 32 <= LENGTH initial.vs_data_section` by metis_tac[] >>
    `w2n a <= LENGTH initial.vs_data_section` by decide_tac >>
    drule emitted_insts_emit_op >> strip_tac >>
    mp_tac (Q.INST [`iid` |-> `st.cs_next_id`, `x` |-> `STRING #"%" (toString st.cs_next_var)`, `s` |-> `initial`,
      `w` |-> `abi_decode_load DLOAD a initial`, `fuel` |-> `0`, `fn` |-> `func`,
      `D` |-> `D'`] prefix_member_dload_pair) >>
    simp_tac bool_ss [LET_THM] >> impl_tac >- simp[] >> strip_tac >>
    drule prefix_register_address_emit_origin >> disch_then irule >>
    gvs[is_terminator_def] >>
     simp[mk_inst_def, inst_mem_below_frontier_def, inst_dload_in_section_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
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
 conj_tac >-
   (drule_all (SRULE [] (Q.INST
     [`w` |-> `abi_decode_load DLOAD a s`] prefix_register_address_dload_run)) >>
    simp[update_var_def]) >>
 conj_tac >-
   (qpat_x_assum `checked ==> !D' explicit. gas_origin_ptr_path _ _ _ _` mp_tac >>
    simp[update_var_def]) >>
 strip_tac >>
 `w2n a + 32 <= LENGTH initial.vs_data_section /\ alloca_history func initial` by metis_tac[] >>
 drule_all (SRULE [n2w_w2n, w2n_lt] (Q.INST [`p` |-> `w2n (a:bytes32)`] ctor_checked_arg_read_reach)) >>
 disch_then (qspec_then `ctx` strip_assume_tac) >> fs[update_var_def] >> gvs[]
QED


val RegisterAddressDynamicMode = ``\checked.
 emit_op ADD [Lit 0w;Lit (n2w off)] st = (head,first) /\
 emit_op DLOAD [head] first = (offset,second) /\
 emit_op ADD [Lit 0w;offset] second = (src,middle) /\
 (checked ==> off < dimword (:256) /\ off + 32 <= LENGTH initial.vs_data_section /\
   alloca_history func initial) /\
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
   !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial) /\
 (checked ==> !D explicit. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (initial, G, tn) [] (OK prepared, H, qt)) /\
 (checked ==> gas_path_mem ctx func initial 0 (OK prepared) /\ alloca_history func prepared)``;

Theorem prefix_entry_register_address_dynamic_actual_mode:
 !checked. (^RegisterAddressDynamicMode) checked
Proof
 gen_tac >> BETA_TAC >> strip_tac >>
 `checked ==> alloca_history func initial` by metis_tac[] >>
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
     (BETA_RULE (Q.SPEC `checked` prefix_entry_register_address_add_actual_mode)))) >>
 disch_then (qspecl_then [`tn`,`PG`,`G`,`D`]
   (qx_choose_then `p1` (qx_choose_then `H1`
     (qx_choose_then `q1` strip_assume_tac)))) >>
 `allocas_from lo p1` by metis_tac[allocas_from_def] >>
 `op_taint q1 head = {}` by fs[op_taint_def] >>
 `checked ==> w2n (0w + n2w off : bytes32) + 32 <= LENGTH p1.vs_data_section /\
    alloca_history func p1` by
   (Cases_on `checked` >> fs[WORD_ADD_0, w2n_n2w]) >>
 drule_all (BETA_RULE (Q.SPEC `checked` prefix_entry_register_address_dload_actual_mode)) >>
 disch_then (qspecl_then [`PG`,`H1`,`D`]
   (qx_choose_then `p2` (qx_choose_then `H2`
     (qx_choose_then `q2` strip_assume_tac)))) >>
 `allocas_from lo p2` by metis_tac[allocas_from_def] >>
 `eval_operand (Lit 0w) p2 = SOME 0w /\ op_taint q2 (Lit 0w) = {}` by
   simp[eval_operand_def, op_taint_def] >>
 `checked ==> alloca_history func p2` by metis_tac[] >>
 drule_all (Q.INST [`a` |-> `Lit 0w`]
   (BETA_RULE (Q.SPEC `checked` prefix_entry_register_address_add_actual_mode))) >>
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
 conj_tac >- metis_tac[abi_decode_sim_trans] >>
 conj_tac >- (
    qpat_x_assum `checked ==> !D explicit. gas_origin_ptr_path _ (initial,_,_) _ _` mp_tac >>
    qpat_x_assum `checked ==> !D explicit. gas_origin_ptr_path _ (p1,_,_) _ _` mp_tac >>
    qpat_x_assum `checked ==> !D explicit. gas_origin_ptr_path _ (p2,_,_) _ _` mp_tac >>
    rpt (pop_assum kall_tac) >> metis_tac[gas_origin_ptr_path_trans]) >>
 strip_tac >>
 `gas_path_mem ctx func initial 0 (OK p2)` by
   (irule (SRULE [ADD] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_mem_then)) >>
    qexists_tac `p1` >> simp[]) >>
 irule (SRULE [ADD] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_mem_then)) >>
 qexists_tac `p2` >> simp[]
QED


Theorem prefix_entry_register_singleton_address_paired_mode:
 !checked ptr.
 (checked ==> off < dimword (:256) /\
   ((~is_word_type ty /\ is_abi_dynamic ce.ce_struct_fields ty) ==>
     off + 32 <= LENGTH initial.vs_data_section) /\ alloca_history func initial) /\ FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ptr) (type_memory_bytes ce ty)) /\
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
 compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit 0w) (Lit 0w)
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
 /\ (checked ==> !D explicit. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (initial, G, tn) [] (OK prepared, H, qt))
 /\ (checked ==> gas_path_mem ctx func initial 0 (OK prepared) /\ alloca_history func prepared)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 `checked ==> alloca_history func initial` by metis_tac[] >>
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
         (BETA_RULE (Q.SPEC `checked` prefix_entry_register_address_add_actual_mode)))) >>
     disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
     qexistsl [`static_src`,`first`,`prepared`,`H`,`qt`] >>
     gvs[WORD_ADD_0, op_taint_def]) >>
 `cs_extends st middle /\ middle.cs_blocks = st.cs_blocks /\
  st.cs_next_var <= middle.cs_next_var /\ st.cs_next_id <= middle.cs_next_id` by
   (imp_res_tac prefix_register_address_emit_shape >>
    conj_tac >- metis_tac[cs_extends_trans] >> simp[]) >>
 drule_all prefix_register_address_code_phase >> strip_tac >>
 `checked ==> off < dimword (:256) /\ off + 32 <= LENGTH initial.vs_data_section /\
   alloca_history func initial` by metis_tac[] >>
 drule_all (BETA_RULE (Q.SPEC `checked` prefix_entry_register_address_dynamic_actual_mode)) >>
 disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
 qexistsl [`src`,`middle`,`prepared`,`H`,`qt`] >> gvs[]
QED




Theorem prefix_entry_register_canonical_address_paired_mode:
 !checked ptr.
 (checked ==> LENGTH encoded <= LENGTH initial.vs_data_section /\ alloca_history func initial) /\
 i < LENGTH atys /\ LENGTH avs = LENGTH atys /\
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
 compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit 0w) (Lit 0w)
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
 /\ (checked ==> !D explicit. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (initial, G, tn) [] (OK prepared, H, qt))
 /\ (checked ==> gas_path_mem ctx func initial 0 (OK prepared) /\
      alloca_history func prepared /\
      sb + LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) <= LENGTH prepared.vs_data_section)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all deploy_ctor_canonical_member_source >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 drule abi_decoder_coherent_header >>
 simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
 `off <= LENGTH encoded` by
   (mp_tac (Q.SPECL [`atys`,`i`] window_member_head_bound) >>
    drule window_member_tuple_length >> simp[Excl "enc_def"]) >>
 `checked ==> off < dimword (:256) /\
   ((~is_word_type ty /\ is_abi_dynamic ce.ce_struct_fields ty) ==>
     off + 32 <= LENGTH initial.vs_data_section) /\ alloca_history func initial` by
   (strip_tac >> conj_tac >- decide_tac >>
    reverse conj_tac >- metis_tac[] >> strip_tac >>
    `is_dynamic (EL i atys)` by metis_tac[] >>
    `LENGTH atys = LENGTH avs` by simp[] >>
    drule_all window_member_dynamic_bounds >>
    drule window_member_tuple_length >> rpt strip_tac >> fs[Excl "enc_def"] >> decide_tac) >>
 drule_all (Q.SPEC `checked` prefix_entry_register_singleton_address_paired_mode) >>
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
     fs[ctorRegisterArgsTheory.ctor_word_type_static] >> metis_tac[ctorRegisterArgsTheory.ctor_word_type_static]) >>
 conj_tac
 >- metis_tac[ctorRegisterArgsTheory.ctor_eval_operand_not_fresh, operand_distinct] >>
 qpat_assum `EL i atys = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
 asm_rewrite_tac[] >>
 conj_tac >- (gvs[Excl "enc_def"] >> decide_tac) >>
 conj_tac >-
   (simp_tac bool_ss [allocas_from_def] >>
    qpat_x_assum `allocas_from lo initial` mp_tac >>
    asm_simp_tac bool_ss [allocas_from_def]) >>
 strip_tac >> gvs[Excl "enc_def"] >> decide_tac
QED


val _ = export_theory();
