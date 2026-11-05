(* Canonical bytes-array execution inside an independently based owner. *)
Theory entryReachBodyOwnedBytesArray
Ancestors
  entryReachBodyCanonicalBytesArray
  entryReachBodyOwnedBytesChild entryReachBodyOwnedLoop
  entryReachBodyOwnedRegion entryReachBodyOperationalPath
  entryReachBodySequenceObservations entryReachBodyArrayInit entryReachBodyExactArrayLoop
  abiDecoderExecution abiDecoderLoopRegisters
  abiAllocationHistory allocaFrontierBound allocaBudgetProps
  abiEncoderRegisteredEffect abiDecoderArrayInit abiDecoderLoopSetup
  abiDecoderContract abiDecodeRanges fragExec venomExecProofs venomInstProps exprLoweringProps
  venomExecSemantics venomMemDefs venomState finite_map words pred_set list arithmetic instIdxIndep

(* The initializer's actual endpoint retains the enclosing allocation, even
   when the array count is stored strictly inside it. *)
Theorem owned_array_initializer[local]:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st = ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME srcword /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ d < dimword (:256) /\
  32 <= sz /\ d+sz <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\ unit_alloca_budget ctx < dimword (:256) /\
  (!i. MEM i (emitted_insts st loop_st) ==> MEM i (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  alloca_inv initial /\ ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  abi_decode_load CALLDATALOAD srcword initial = n2w ncount /\ ncount <= maxn /\
  abi_alloca_history (fn_insts fn) initial /\ fn_has_code st loop_st fn /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  entry_owned_region oid root extent d sz initial /\ oid <> header_st.cs_next_id /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?t. entry_decode_path ctx fn initial t /\
    entry_owned_loop_resources ctx fn site header_st.cs_next_id p oid root extent d sz t /\
    abi_encoder_registered_effect {header_st.cs_next_id} [(d,32)] initial t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    eval_operand cnt t = SOME (n2w ncount) /\ mem_word_at d t.vs_memory = n2w ncount /\
    entry_loop_fields initial t /\ fresh_vars_wrt limit_st t /\ ~t.vs_halted /\
    t.vs_current_bb = loop_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  SUBGOAL_THEN ``d+sz <= p \/ p+32 <= d`` assume_tac
  >- (drule entry_owned_region_counter_separation >>
      disch_then (qspecl_then [`p`,`header_st.cs_next_id`] mp_tac) >> simp[] >> metis_tac[]) >>
  drule_all entry_array_init_operational >>
  disch_then (qx_choose_then `prepared` strip_assume_tac) >>
  `fresh_vars_wrt limit_st prepared` by
    (drule_all entry_array_initializer_final_fresh >> simp[]) >>
  `entry_owned_region oid root extent d sz prepared` by
    (irule entry_owned_region_preserved >>
     goal_assum (drule_at Any) >> simp[]) >>
  `prepared.vs_current_bb = loop_st.cs_current_bb /\
   prepared.vs_call_ctx = initial.vs_call_ctx /\
   prepared.vs_data_section = initial.vs_data_section` by
    suspend "control" >>
  `remaining_alloca_budget (fn_insts fn)
      (prepared with vs_inst_idx := LENGTH loop_st.cs_current_insts) =
    remaining_alloca_budget (fn_insts fn) prepared` by
    (irule remaining_alloca_budget_domain_cong >> simp[]) >>
  `entry_owned_loop_resources ctx fn site header_st.cs_next_id p oid root extent d sz prepared` by
    simp[entry_owned_loop_resources_def] >>
  qexists_tac `prepared with vs_inst_idx := LENGTH loop_st.cs_current_insts` >>
  suspend "pc_frame"
QED

Resume owned_array_initializer[control]:
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  `prepared.vs_current_bb = initial.vs_current_bb` by
    (irule run_inst_seq_preserves_field >>
     qexists_tac `emitted_insts st loop_st` >> asm_rewrite_tac[] >>
     rpt strip_tac >> fs[EVERY_MEM] >>
     metis_tac[step_preserves_control_flow, step_inst_non_invoke]) >>
  simp[] >> conj_tac >> irule run_inst_seq_preserves_field >>
  qexists_tac `emitted_insts st loop_st` >> asm_rewrite_tac[] >>
  rpt strip_tac >> fs[EVERY_MEM] >>
  metis_tac[step_preserves_call_ctx, step_preserves_data_section, step_inst_non_invoke]
QED
Resume owned_array_initializer[pc_frame]:
  map_every (fn q => qpat_x_assum q kall_tac)
    [`abi_decode_array_loop_init _ _ _ _ _ _ _ = _`,
     `abi_decode_dynarray_prefix _ _ _ _ _ _ = _`,
     `abi_decode_array_header _ _ _ _ = _`, `abi_decode_index_init _ = _`,
     `eval_operand src initial = _`, `eval_operand dst initial = _`,
     `!i. MEM i (emitted_insts _ _) ==> _`,
     `FLOOKUP initial.vs_allocas _ = NONE /\ _ \/ _`,
     `alloca_inv initial`, `alloca_frontier_inv _ _ _ initial`,
     `abi_alloca_history _ initial`, `fn_has_code _ _ _`,
     `run_inst_seq _ initial = _`, `entry_owned_region _ _ _ _ _ initial`,
     `d+sz <= p \/ p+32 <= d`,
     `!id. id <> _ ==> _`, `if _ then _ else _`,
     `abi_decode_footprint_frame _ _ _`] >>
  fs[entry_owned_loop_resources_def, entry_owned_region_def,
     abi_encoder_registered_effect_def, entry_loop_fields_def,
     alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
     abi_alloca_history_def, alloca_frontier_inv_def, eval_op_inst_idx, mload_def,
     compileEnvTheory.fresh_vars_wrt_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise owned_array_initializer

(* Canonical calldata and range facts depend only on the stable operands and
   call context, not on the allocation root used by the enclosing owner. *)
Theorem owned_bytes_invariant_inputs[local]:
  entry_bytes_array_inv next limit_st d outsz q ncount prepared t /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb len d outsz b cap prepared /\
  mem_bytes_at sb len (abi_decode_source CALLDATALOAD prepared) = bytes ==>
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb len d outsz b cap t /\
  mem_bytes_at sb len (abi_decode_source CALLDATALOAD t) = bytes
Proof
  simp_tac bool_ss [entry_bytes_array_inv_def] >> strip_tac >>
  fs[abiDecoderTypedContractTheory.abi_decoder_ranges_def,
     abiDecoderContractTheory.abi_decode_source_def, entry_loop_fields_def] >>
  metis_tac[]
QED

(* The concrete body-phase predicate retains the backedge's source facts as
   well as the canonical invariant.  Ownership remains in the loop contract. *)
Definition owned_bytes_body_phase_def:
  owned_bytes_body_phase next limit_st d outsz q ncount prepared ip src p srcaddr j u <=>
    entry_bytes_array_inv next limit_st d outsz q ncount prepared u /\
    eval_operand ip u = SOME p /\ mload (w2n p) u = n2w j /\
    eval_operand src u = SOME srcaddr /\
    abi_decode_load CALLDATALOAD srcaddr u = n2w ncount
End

Theorem owned_bytes_header_phase[local]:
  entry_bytes_array_inv next limit_st d outsz q ncount prepared s /\
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr ncount j s /\
  abi_decoder_operand_live next ip /\ abi_decoder_operand_live next src /\
  next+4 <= limit_st.cs_next_var ==>
  owned_bytes_body_phase next limit_st d outsz q ncount prepared ip src p srcaddr j
    (jump_to body_lbl (abi_decode_header_state (STRING #"%" (toString next))
      (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
      (STRING #"%" (toString (next+3))) j ncount s))
Proof
  strip_tac >>
  `fresh_vars_wrt limit_st s` by fs[entry_bytes_array_inv_def] >>
  drule_all abi_decoder_header_registers >>
  disch_then (qspecl_then [`ncount`,`j`] strip_assume_tac) >>
  simp_tac bool_ss [owned_bytes_body_phase_def] >> conj_tac
  >- (irule entry_bytes_array_inv_header >> asm_rewrite_tac[]) >>
  fs[abi_decode_loop_ready_def] >>
  asm_simp_tac (srw_ss()) [] >>
  fs[abi_decode_load_def, abi_decode_source_def, jump_to_def,
     abi_decode_header_state_def, update_var_def, mload_def]
QED

Theorem owned_bytes_body_to_backedge[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops))
    CALLDATALOAD (Lit 0w) (DecBytestring n) middle = ((),last) /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  j < LENGTH xs /\ is_dynamic (vyper_to_abi_type env ty) /\
  type_memory_bytes ce ty = type_memory_size tv /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d outsz b cap prepared /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD prepared) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  outsz = type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
  owned_bytes_body_phase next limit_st d outsz (w2n p) (LENGTH xs) prepared
    ip src p srcaddr j u /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next ip /\ next <= st.cs_next_var /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  ~u.vs_halted /\ u.vs_current_bb = st.cs_current_bb /\
  u.vs_inst_idx = LENGTH st.cs_current_insts /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d region_sz u /\
  d+32+j*type_memory_size tv+type_memory_size tv <= d+outsz /\
  FST ops = Var iv /\
  (?bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = last.cs_current_insts ++
      abi_decode_backedge_insts last.cs_next_id iv nv ip hdr) ==>
  ?t. entry_bytes_array_inv next limit_st d outsz (w2n p) (LENGTH xs) prepared t /\
    entry_loop_child_end fn last.cs_current_bb last.cs_current_insts last.cs_next_id
      iv nv ip hdr src p srcaddr (LENGTH xs) j t /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d region_sz t /\
    val_in_memory tv (EL j xs) (d+32+j*type_memory_size tv) t.vs_memory /\
    entry_loop_fields u t /\ entry_decode_path ctx fn u t /\
    abi_encoder_registered_effect {} [(d+32+j*type_memory_size tv,type_memory_size tv)] u t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `owned_bytes_body_phase _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [owned_bytes_body_phase_def]) >>
  `abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb
     (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
     d outsz b cap u /\
   mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
     (abi_decode_source CALLDATALOAD u) =
     enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
    (drule_all owned_bytes_invariant_inputs >> asm_rewrite_tac[]) >>
  `abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb
     (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
     d outsz (d+outsz) region_sz u` by
    (fs[abiDecoderTypedContractTheory.abi_decoder_ranges_def]) >>
  qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
  `fresh_vars_wrt limit_st u` by fs[entry_bytes_array_inv_def] >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst /\
   abi_decoder_operand_live st.cs_next_var ip` by
    (rpt conj_tac >> irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
     qexists_tac `next` >> asm_rewrite_tac[]) >>
  drule_all entry_owned_bytes_child >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  `entry_bytes_array_inv next limit_st d
     (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) (w2n p) (LENGTH xs) prepared t` by
    (irule entry_bytes_array_inv_child >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
     qexistsl_tac [`d+32+j*type_memory_size tv`,`st.cs_next_var`,`type_memory_size tv`,`u`] >>
     asm_rewrite_tac[] >>
     qpat_assum `type_memory_bytes ce ty = _`
       (fn th => fs[th, Excl "enc_def"])) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  simp_tac bool_ss [entry_loop_child_end_def] >> asm_rewrite_tac[] >>
  fs[entry_loop_fields_def, abi_decode_load_def, abi_decode_source_def] >> metis_tac[]
QED
