Theory abiScratchDecoderArrayIteration
Ancestors
  abiScratchDecoderContract abiScratchDecoderSubwindow abiDecoderValidContract
  abiDecoderValidArraySetupInputs abiDecoderArraySetupInputs abiDecoderArraySlice
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecodeRanges abiValidMember
  abiValidMembers compileEnv valueEncoding vyperABI vyperValue contractABI venomState words list
  arithmetic abiScratchDecoderArraySetup abiScratchDecoderTuple abiDecoderArraySetupCode
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderLoop abiEncoder fragExec
  venomExecSemantics abiScratchEncoderContract abiScratchAfterAddress abiScratchEffect
  abiDecoderArrayInitExec abiScratchDecoderTransport abiScratchDecoderLoopInvariant
  abiDecoderValidArrayMemory abiDecoderRecursiveArrayIteration abiDecoderEffect
  abiDecoderProtectedScratch abiDecoderAllocation rich_list

(* Actual array windows and conversion establish the child's physical ownership. *)
Theorem abi_scratch_decoder_array_child_input:
  let at = vyper_to_abi_type env ty;
      ao = j * abi_member_head_size at;
      childbs = abi_decode_member_bytes at (DROP 32 bs) (DROP ao (DROP 32 bs));
      off = 32 + abi_decode_member_offset at (DROP 32 bs) ao in
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE at) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE at) bs /\ j < LENGTH vs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  abi_scratch_decoder_ranges opc hi src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) first last b cap s /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  eval_operand childsrc s = SOME (n2w (sb + off)) /\
  eval_operand childdst s = SOME (n2w (d + 32 + j * type_memory_bytes ce ty)) /\
  abi_decoder_operand_live st.cs_next_var childsrc /\
  abi_decoder_operand_live st.cs_next_var childdst /\ abi_decoder_operand_live st.cs_next_var hi ==>
  abi_scratch_decoder_input ce env sf ty tv childbs (EL j vs) st childsrc childdst opc hi
    (sb + off) (d + 32 + j * type_memory_bytes ce ty) first last b cap s
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_dynarray_values >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_array_metadata_child >> strip_tac >>
  `j < abi_head_word bs /\ j < maxn` by (asm_simp_tac bool_ss [] >> decide_tac) >>
  mp_tac (Q.ISPECL [`LENGTH (vs:vyperValue$value list)`, `j:num`,
    `vyper_to_abi_type env ty`, `DROP 32 (bs:word8 list)`, `DROP 32 (bs:word8 list)`]
    abi_decode_array_member_EL) >> impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `sb + LENGTH bs < dimword (:256)` by fs[abi_scratch_decoder_ranges_def] >>
  drule_all (SIMP_RULE arith_ss [LET_THM] abi_valid_array_child_window) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `j * type_memory_bytes ce ty + type_memory_bytes ce ty <= maxn * type_memory_bytes ce ty`
    by simp[abi_decoder_array_cell_capacity] >>
  `d + 32 + j * type_memory_bytes ce ty + type_memory_bytes ce ty <=
    d + type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    (simp_tac bool_ss [Once type_memory_bytes_def] >> decide_tac) >>
  RULE_ASSUM_TAC (SIMP_RULE arith_ss []) >>
  simp_tac bool_ss [abi_scratch_decoder_input_def] >>
  asm_simp_tac arith_ss [abi_decoder_head_window] >>
  irule abi_scratch_decoder_subwindow_ranges >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`d`, `dst`, `LENGTH (bs:word8 list)`,
    `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`, `sb`, `src`] >>
  asm_simp_tac arith_ss [GSYM ADD_ASSOC]
QED

(* Reach a physical recursive child after either actual array-address prefix. *)
Theorem abi_scratch_decoder_array_setup_from_state:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,ready) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_scratch_decoder_ranges opc hi src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  abi_decoder_budget first last b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st ready (\s. s = initial)
    (abi_scratch_decoder_array_setup_post ce env ty bs j ready ops sb d
      st.cs_next_var limit_st initial) (K F)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_scratch_decoder_ranges_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_scratch_decoder_array_setup_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) initial = OK prepared` >>
  qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_array_setup_reach:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,ready) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_scratch_decoder_ranges opc hi src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  abi_decoder_budget first last b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st ready func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared.
    abi_scratch_decoder_input ce env sf ty tv
      (abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP 32 bs)
        (DROP (j * abi_member_head_size (vyper_to_abi_type env ty)) (DROP 32 bs)))
      (EL j vs) ready (FST (SND ops)) (SND (SND ops)) opc hi
      (sb + (32 + abi_decode_member_offset (vyper_to_abi_type env ty) (DROP 32 bs)
        (j * abi_member_head_size (vyper_to_abi_type env ty))))
      (d + 32 + j * type_memory_bytes ce ty) first last b cap prepared /\
    eval_operand (FST ops) prepared = SOME (n2w j) /\
    abi_decoder_operand_live ready.cs_next_var (FST ops) /\
    fresh_vars_wrt limit_st prepared /\ abi_decoder_address_frame st.cs_next_var initial prepared /\
    prepared.vs_current_bb = ready.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\ ~prepared.vs_halted /\
    abi_decode_sim ctx func initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_array_setup_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  qhdtm_x_assum `abi_scratch_decoder_array_setup_post`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_array_setup_post_def]) >>
  drule abi_decode_array_element_setup_operands >> strip_tac >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `new_next` |-> `ready.cs_next_var`,
    `len` |-> `LENGTH (bs:word8 list)`,
    `sz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`, `hi_op` |-> `hi:operand`]
    abi_scratch_decoder_address_observations) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (SIMP_RULE bool_ss [LET_THM] (Q.INST [`st` |-> `ready`,
    `s` |-> `prepared:venom_state`, `childsrc` |-> `FST (SND (ops:operand # operand # operand))`,
    `childdst` |-> `SND (SND (ops:operand # operand # operand))`]
    abi_scratch_decoder_array_child_input)) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `~prepared.vs_halted` by fs[abi_decoder_address_frame_def] >>
  qexists_tac `prepared` >> RULE_ASSUM_TAC (SIMP_RULE arith_ss []) >> asm_simp_tac arith_ss []
QED

(* Execute an actual array child under the physical recursive contract. *)
Theorem abi_scratch_decoder_array_body:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  fn_has_code st end_st func /\
  (!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decoder ce env sf ty tv /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    di (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_scratch_decoder_ranges opc hi src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\ abi_decoder_operand_live st.cs_next_var ip /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  st.cs_next_id <= middle.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory tv (EL j vs) (d + 32 + j * type_memory_bytes ce ty) actual.vs_memory /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + 32 + j * type_memory_bytes ce ty) (type_memory_bytes ce ty) b cap initial actual /\
    eval_operand (FST ops) actual = SOME (n2w j) /\ eval_operand ip actual = SOME p /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_scratch_decoder_ranges_def] >>
  drule_all abi_decoder_array_body_code >> strip_tac >>
  `first <= middle.cs_next_id /\ middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_scratch_decoder_array_setup_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  `abi_decoder_budget first last b cap prepared` by
    (qpat_assum `abi_decoder_address_frame _ _ _`
      (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
     drule_all abi_decoder_budget_transport >> simp[]) >>
  qhdtm_x_assum `abi_scratch_decoder` (mp_tac o PURE_REWRITE_RULE [abi_scratch_decoder_def]) >>
  disch_then (qspecl_then [`SND (SND (ops:operand # operand # operand))`,
    `FST (SND (ops:operand # operand # operand))`, `opc`, `hi`, `middle`, `end_st`,
    `func`, `ctx`, `first`, `last`, `b`, `cap`, `limit_st`, `prepared:venom_state`,
    `abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP 32 bs)
      (DROP (j * abi_member_head_size (vyper_to_abi_type env ty)) (DROP 32 bs))`,
    `EL j (vs:vyperValue$value list)`,
    `sb + (32 + abi_decode_member_offset (vyper_to_abi_type env ty) (DROP 32 bs)
      (j * abi_member_head_size (vyper_to_abi_type env ty)))`,
    `d + 32 + j * type_memory_bytes ce ty`] mp_tac) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `eval_operand (FST ops) actual = SOME (n2w j)` by
    (drule_all abi_scratch_effect_operand >> simp[]) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + 32 + j * type_memory_bytes ce ty) (type_memory_bytes ce ty) b cap initial actual` by
    (irule abi_scratch_effect_after_address >>
     qexistsl_tac [`d + 32 + j * type_memory_bytes ce ty`, `end_st.cs_next_id`,
       `middle.cs_next_id`, `middle.cs_next_var`, `type_memory_bytes ce ty`, `prepared`] >>
     asm_simp_tac arith_ss []) >>
  `eval_operand ip actual = SOME p` by (drule_all abi_scratch_effect_operand >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

(* Actual recursive array body execution extends the initialized typed prefix. *)
Theorem abi_scratch_decoder_body_inputs:
  abi_scratch_decoder_loop_inv opc bs tv vs sb d outsz slot site
    first last lo hi next limit_st b cap initial body_lbl j s /\
  abi_scratch_decoder_ranges opc hi_op src dst sb (LENGTH bs)
    d outsz first last b cap initial /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi_op /\ abi_decoder_operand_live next ip /\
  eval_operand ip initial = SOME (n2w slot) /\ slot < dimword (:256) /\ next <= body_next ==>
  abi_decoder_valid_array_memory opc bs tv vs sb d j s /\
  abi_scratch_decoder_ranges opc hi_op src dst sb (LENGTH bs)
    d outsz first last b cap s /\
  fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s /\
  eval_operand ip s = SOME (n2w slot) /\ mload (w2n (n2w slot:bytes32)) s = n2w j /\
  abi_decoder_operand_live body_next src /\ abi_decoder_operand_live body_next dst /\
  abi_decoder_operand_live body_next hi_op /\ abi_decoder_operand_live body_next ip /\
  s.vs_current_bb = body_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_decoder_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_loop_inv_def]) >>
  drule_all abi_scratch_decoder_ranges_effect >> strip_tac >>
  `fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s /\
    eval_operand ip s = SOME (n2w slot)` by
    (fs[abi_scratch_effect_def, Excl "enc_def"] >> metis_tac[]) >>
  asm_simp_tac bool_ss [w2n_n2w, LESS_MOD] >>
  metis_tac[abi_decoder_operand_live_mono]
QED

(* TOP-LEVEL: the generated body extends the initialized prefix even when its
   recursive child allocates scratch and changes the current basic block. *)
Theorem abi_scratch_decoder_array_iteration:
  abi_decode_array_element_setup ip src dst opc hi_op (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi_op
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  fn_has_code st end_st func /\ st.cs_current_insts = [] /\
  (!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decoder ce env sf ty tv /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    di (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_scratch_decoder_loop_inv opc bs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial st.cs_current_bb j s /\ j < LENGTH vs /\
  abi_scratch_decoder_ranges opc hi_op src dst sb
    (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) first last b cap initial /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi_op /\ abi_decoder_operand_live next ip /\
  eval_operand ip initial = SOME (n2w slot) /\ slot < dimword (:256) /\
  first <= lo /\ lo <= st.cs_next_id /\ st.cs_next_id <= middle.cs_next_id /\
  end_st.cs_next_id <= hi /\ hi <= last /\ next <= st.cs_next_var /\
  first <= site /\ site < last /\ (site < st.cs_next_id \/ end_st.cs_next_id <= site) /\
  end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. abi_decoder_valid_array_memory opc bs tv vs sb d (SUC j) actual /\
    abi_scratch_effect first last lo hi next limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\ mload slot actual = n2w j /\
    eval_operand (FST ops) actual = SOME (n2w j) /\
    eval_operand ip actual = SOME (n2w slot) /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func s actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`body_next` |-> `st.cs_next_var`, `body_lbl` |-> `st.cs_current_bb`,
    `outsz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`]
    abi_scratch_decoder_body_inputs) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `first <= st.cs_next_id /\ end_st.cs_next_id <= last` by decide_tac >>
  `s.vs_inst_idx = LENGTH st.cs_current_insts` by simp[] >>
  `mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs` by
    fs[abi_decoder_valid_array_memory_def] >>
  drule_all (Q.INST [`initial` |-> `s:venom_state`, `p` |-> `n2w slot:bytes32`]
    abi_scratch_decoder_array_body) >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func s actual` >>
  drule_all abi_decoder_valid_dynarray_values >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  `type_memory_size tv = type_memory_bytes ce ty` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `j < maxn` by decide_tac >>
  `j * type_memory_size tv + type_memory_size tv <= maxn * type_memory_size tv`
    by simp[abi_decoder_array_cell_capacity] >>
  `d + 32 + j * type_memory_bytes ce ty + type_memory_bytes ce ty <=
    d + type_memory_bytes ce (ArrayT ty (Dynamic maxn))`
    by (qpat_x_assum `j * type_memory_size tv + type_memory_size tv <= _` mp_tac >>
        simp_tac bool_ss [Once type_memory_bytes_def] >>
        asm_simp_tac bool_ss [] >> decide_tac) >>
  qpat_assum `type_memory_size tv = _`
    (fn size => mp_tac (PURE_REWRITE_RULE [size]
      (Q.INST [`child_lo` |-> `st.cs_next_id`, `child_hi` |-> `end_st.cs_next_id`,
        `child_next` |-> `st.cs_next_var`, `body_lbl` |-> `st.cs_current_bb`,
        `t` |-> `actual:venom_state`,
        `outsz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`]
        abi_scratch_decoder_child_advance))) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
