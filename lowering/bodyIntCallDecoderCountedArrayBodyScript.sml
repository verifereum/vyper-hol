(* Counted physical array setup and recursive child execution. *)
Theory bodyIntCallDecoderCountedArrayBody
Ancestors
  bodyIntCallDecoderCountedPrimitive bodyIntCallDecoderCountedContract
  abiScratchDecoderArrayIteration abiScratchDecoderArraySetup abiScratchDecoderTuple
  abiScratchDecoderContract abiScratchEncoderContract abiScratchAfterAddress
  abiDecoderArraySetupCode abiDecoderArraySetupInputs abiDecoderDynamicLoopSetup abiDecoderArrayInitExec
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecoderReentry
  abiDecoderLoop abiDecoderAllocation abiScratchEffect abiScratchDecoderRanges
  abiScratchDecoderLoopInvariant abiDecoderValidArrayMemory abiDecoderValidContract
  abiDecoderRecursiveArrayIteration abiDecoderValidArraySetupInputs abiDecoderArraySlice
  entrySinkExtraction instIdxIndep exprLoweringProps compileEnv venomState
  valueEncoding vyperABI contractABI venomExecSemantics fragGasPath words list arithmetic

Theorem intcall_scratch_decoder_array_setup_path:
  abi_decode_array_element_setup ip src dst opc base_op hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,ready) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_scratch_decoder_ranges opc base_op hi src dst B sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) first last b cap initial /\
  mem_bytes_at (B + sb) (LENGTH bs) (abi_decode_source opc initial) = bs /\
  abi_decoder_budget first last b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var base_op /\ abi_decoder_operand_live st.cs_next_var hi /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st ready func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared n.
    abi_scratch_decoder_input ce env sf ty tv
      (abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP 32 bs)
        (DROP (j * abi_member_head_size (vyper_to_abi_type env ty)) (DROP 32 bs)))
      (EL j vs) ready (FST (SND ops)) (SND (SND ops)) opc base_op hi B
      (sb + (32 + abi_decode_member_offset (vyper_to_abi_type env ty) (DROP 32 bs)
        (j * abi_member_head_size (vyper_to_abi_type env ty))))
      (d + 32 + j * type_memory_bytes ce ty) first last b cap prepared /\
    eval_operand (FST ops) prepared = SOME (n2w j) /\
    abi_decoder_operand_live ready.cs_next_var (FST ops) /\
    fresh_vars_wrt limit_st prepared /\ abi_decoder_address_frame st.cs_next_var initial prepared /\
    prepared.vs_current_bb = ready.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\ ~prepared.vs_halted /\
    gas_path ctx func initial n (OK prepared)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_scratch_decoder_ranges_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule_all abi_scratch_decoder_array_setup_sequence >> strip_tac >>
  drule_all intcall_same_block_seq_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) initial = OK prepared` >>
  `abi_scratch_decoder_array_setup_post ce env ty bs j ready ops sb d st.cs_next_var limit_st initial
    (prepared with vs_inst_idx := LENGTH ready.cs_current_insts)` by simp[] >>
  qpat_x_assum `abi_scratch_decoder_array_setup_post _ _ _ _ _ _ _ _ _ _ _ _ prepared` kall_tac >>
  qhdtm_x_assum `abi_scratch_decoder_array_setup_post`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_array_setup_post_def]) >>
  drule abi_decode_array_element_setup_operands >> strip_tac >>
  drule_all abi_scratch_decoder_address_observations >> strip_tac >>
  `mem_bytes_at (B + sb) (LENGTH bs)
    (abi_decode_source opc (prepared with vs_inst_idx := LENGTH ready.cs_current_insts)) = bs` by simp[] >>
  drule_all (SIMP_RULE bool_ss [LET_THM] abi_scratch_decoder_array_child_input) >> strip_tac >>
  qexistsl_tac [`prepared with vs_inst_idx := LENGTH ready.cs_current_insts`, `n`] >>
  asm_simp_tac bool_ss [] >> simp[]
QED

Theorem intcall_scratch_decoder_array_body:
  abi_decode_array_element_setup ip src dst opc base_op hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc base_op hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  (base_op = Lit 0w \/ opc = MLOAD) /\ fn_has_code st end_st func /\
  (!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  intcall_scratch_decoder_counted ce env sf ty tv /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    di (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_scratch_decoder_ranges opc base_op hi src dst B sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) first last b cap initial /\
  mem_bytes_at (B + sb) (LENGTH bs) (abi_decode_source opc initial) = bs /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var base_op /\ abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_operand_live st.cs_next_var ip /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  st.cs_next_id <= middle.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. val_in_memory tv (EL j vs) (d + 32 + j * type_memory_bytes ce ty) actual.vs_memory /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + 32 + j * type_memory_bytes ce ty) (type_memory_bytes ce ty) b cap initial actual /\
    eval_operand (FST ops) actual = SOME (n2w j) /\ eval_operand ip actual = SOME p /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_scratch_decoder_ranges_def] >>
  drule_all abi_decoder_array_body_code >> strip_tac >>
  `first <= middle.cs_next_id /\ middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all intcall_scratch_decoder_array_setup_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path ctx func initial n (OK prepared)` >>
  `abi_decoder_budget first last b cap prepared` by
    (qpat_assum `abi_decoder_address_frame _ _ _`
      (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
     drule_all abi_decoder_budget_transport >> simp[]) >>
  `first <= abi_decoder_entry_floor middle` by simp[abi_decoder_entry_floor_def] >>
  qhdtm_x_assum `intcall_scratch_decoder_counted`
    (assume_tac o PURE_REWRITE_RULE [intcall_scratch_decoder_counted_def]) >>
  first_x_assum (drule_at (Pat `abi_scratch_decoder_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`end_st`, `func`, `ctx`, `limit_st`] mp_tac) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `val_in_memory tv (EL j vs) (d + 32 + j * type_memory_bytes ce ty) actual.vs_memory` >>
  `eval_operand (FST ops) actual = SOME (n2w j)` by
    (drule_all abi_scratch_effect_operand >> simp[]) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + 32 + j * type_memory_bytes ce ty) (type_memory_bytes ce ty) b cap initial actual` by
    (irule abi_scratch_effect_after_address >>
     qexistsl_tac [`d + 32 + j * type_memory_bytes ce ty`, `end_st.cs_next_id`,
       `middle.cs_next_id`, `middle.cs_next_var`, `type_memory_bytes ce ty`, `prepared`] >>
     asm_simp_tac arith_ss []) >>
  `eval_operand ip actual = SOME p` by (drule_all abi_scratch_effect_operand >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >> metis_tac[gas_path_then]
QED

Theorem intcall_scratch_decoder_array_iteration:
  abi_decode_array_element_setup ip src dst opc base_op hi_op (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc base_op hi_op
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  (base_op = Lit 0w \/ opc = MLOAD) /\
  fn_has_code st end_st func /\ st.cs_current_insts = [] /\
  (!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  intcall_scratch_decoder_counted ce env sf ty tv /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    di (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_scratch_decoder_loop_inv opc bs tv vs (B + sb) d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial st.cs_current_bb j s /\ j < LENGTH vs /\
  abi_scratch_decoder_ranges opc base_op hi_op src dst B sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) first last b cap initial /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next base_op /\ abi_decoder_operand_live next hi_op /\
  abi_decoder_operand_live next ip /\
  eval_operand ip initial = SOME (n2w slot) /\ slot < dimword (:256) /\
  first <= lo /\ lo <= st.cs_next_id /\ st.cs_next_id <= middle.cs_next_id /\
  end_st.cs_next_id <= hi /\ hi <= last /\ next <= st.cs_next_var /\
  first <= site /\ site < last /\ (site < st.cs_next_id \/ end_st.cs_next_id <= site) /\
  end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual n. abi_decoder_valid_array_memory opc bs tv vs (B + sb) d (SUC j) actual /\
    abi_scratch_effect first last lo hi next limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\ mload slot actual = n2w j /\
    eval_operand (FST ops) actual = SOME (n2w j) /\ eval_operand ip actual = SOME (n2w slot) /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    gas_path ctx func s n (OK actual)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`body_next` |-> `st.cs_next_var`, `body_lbl` |-> `st.cs_current_bb`,
    `outsz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`]
    abi_scratch_decoder_body_inputs) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `first <= st.cs_next_id /\ end_st.cs_next_id <= last` by decide_tac >>
  `s.vs_inst_idx = LENGTH st.cs_current_insts` by simp[] >>
  `mem_bytes_at (B + sb) (LENGTH bs) (abi_decode_source opc s) = bs` by
    fs[abi_decoder_valid_array_memory_def] >>
  drule_all (Q.INST [`initial` |-> `s:venom_state`, `p` |-> `n2w slot:bytes32`]
    intcall_scratch_decoder_array_body) >> disch_then (qspec_then `ctx` strip_assume_tac) >>
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
        simp_tac bool_ss [Once type_memory_bytes_def] >> asm_simp_tac bool_ss [] >> decide_tac) >>
  qpat_assum `type_memory_size tv = _`
    (fn size => mp_tac (PURE_REWRITE_RULE [size]
      (Q.INST [`child_lo` |-> `st.cs_next_id`, `child_hi` |-> `end_st.cs_next_id`,
        `child_next` |-> `st.cs_next_var`, `body_lbl` |-> `st.cs_current_bb`,
        `t` |-> `actual:venom_state`,
        `outsz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`]
        abi_scratch_decoder_child_advance))) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qexistsl_tac [`actual`, `n`] >> asm_simp_tac bool_ss []
QED
