(* Canonical bytes-array execution inside an independently based owner. *)
Theory entryReachBodyOwnedBytesArray
Ancestors
  entryReachBodyCanonicalBytesArray
  entryReachBodyOwnedBytesChild entryReachBodyOwnedLoop
  entryReachBodyActualOwnedLoop
  entryReachBodyOwnedRegion entryReachBodyOperationalPath entryReachBodyOperationalHeader
  entryReachBodySequenceObservations entryReachBodyArrayInit entryReachBodyExactArrayLoop
  abiDecoderExecution abiDecoderLoopRegisters abiDecoderArrayBackedge calldataDynOwned
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
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op initial) /\
    (!id. id <> header_st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (if FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE then
       t.vs_alloca_next = initial.vs_alloca_next+32 else t.vs_alloca_next = initial.vs_alloca_next)
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

(* The existing compiler configuration contains no allocation-root assertion;
   only the old live-state predicate had that restriction. Reuse its static
   facts with the enclosing owner resources and the actual two-register loop. *)
Theorem owned_bytes_actual_contract[local]:
  cfg = ((ce,env,sf,ty,tv,maxn,parent_di,avs,xs,n),
       (ip,src,dst,ops,st,middle,last,limit_st),
       (next,d,p,srcaddr,sb,b,cap,oid,capacity),
       (ctx,fn,hdr,body_lbl,exit_lbl,hid,tail,prefix,bid,iv,nv)) /\
  entry_bytes_array_config cfg /\ bid = last.cs_next_id /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap prepared /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD prepared) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  oid <> cid /\ 32+LENGTH xs*type_memory_size tv <= capacity ==>
  entry_actual_owned_indexed_contract ctx fn site hdr body_lbl exit_lbl hid tail prefix bid
    ip src (STRING #"%" (toString next)) iv
    (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
    (STRING #"%" (toString (next+3))) (STRING #"%" (toString nv))
    p srcaddr tv xs d capacity cid oid root extent {cid} {}
    (\j s. entry_bytes_array_inv next limit_st d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) (w2n p) (LENGTH xs) prepared s)
    (owned_bytes_body_phase next limit_st d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) (w2n p) (LENGTH xs) prepared
      ip src p srcaddr)
    (\j s. entry_bytes_array_inv next limit_st d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) (w2n p) (LENGTH xs) prepared s)
    (entry_bytes_array_inv next limit_st d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) (w2n p) (LENGTH xs) prepared)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qpat_x_assum `entry_bytes_array_config _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [entry_bytes_array_config_def]) >>
  `ip <> Var (STRING #"%" (toString nv)) /\
   src <> Var (STRING #"%" (toString nv))` by
    (conj_tac >> irule abi_decoder_live_excludes_output >>
     qexists_tac `next` >> simp[]) >>
  simp_tac bool_ss [entry_actual_owned_indexed_contract_def] >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [Excl "enc_def"] >> rpt conj_tac
  >- suspend "header"
  >- suspend "child"
  >> suspend "successor"
QED

Resume owned_bytes_actual_contract[header]:
  rpt strip_tac >> Cases_on `j < LENGTH xs`
  >- (simp[] >> irule owned_bytes_header_phase >>
      fs[entry_owned_loop_inv_def, SF SFY_ss, Excl "enc_def"]) >>
  simp[] >> irule entry_bytes_array_inv_header >> simp[]
QED

Resume owned_bytes_actual_contract[child]:
  rpt strip_tac >>
  `d+32+j*type_memory_size tv+type_memory_size tv <=
     d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by metis_tac[] >>
  qpat_x_assum `last.cs_current_bb = tail` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `last.cs_current_insts = prefix` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `bid = last.cs_next_id` SUBST_ALL_TAC >>
  irule owned_bytes_body_to_backedge >> asm_rewrite_tac[] >>
  qhdtm_assum `abi_decode_array_element_setup` (irule_at Any) >>
  qhdtm_assum `abi_decoder_metadata` (irule_at Any) >>
  asm_rewrite_tac[] >> simp[SF SFY_ss, Excl "enc_def"]
QED

Resume owned_bytes_actual_contract[successor]:
  rpt strip_tac >> irule entry_bytes_array_inv_backedge >> simp[]
QED
Finalise owned_bytes_actual_contract

Theorem owned_bytes_loop_endpoint[local]:
  cfg = ((ce,env,sf,ty,tv,maxn,parent_di,avs,xs,n),
       (ip,src,dst,ops,st,middle,last,limit_st),
       (next,d,p,srcaddr,sb,b,cap,oid,capacity),
       (ctx,fn,hdr,body_lbl,exit_lbl,hid,tail,prefix,bid,iv,nv)) /\
  entry_bytes_array_config cfg /\ bid = last.cs_next_id /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap prepared /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD prepared) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  oid <> cid /\ 32+LENGTH xs*type_memory_size tv <= capacity /\
  entry_owned_loop_inv ctx fn site hdr ip src p srcaddr tv xs d capacity
    cid oid root extent 0 s /\
  entry_bytes_array_inv next limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
    (w2n p) (LENGTH xs) prepared s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d capacity t /\
    entry_bytes_array_inv next limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
      (w2n p) (LENGTH xs) prepared t /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d t.vs_memory /\
    entry_loop_trace ctx fn {cid} [(d,32+LENGTH xs*type_memory_size tv)] s t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all owned_bytes_actual_contract >>
  disch_then (qspecl_then [`site`,`root`,`extent`] assume_tac) >>
  drule entry_actual_owned_indexed_array_loop_from_index >>
  simp_tac bool_ss [] >> disch_then drule >>
  asm_rewrite_tac[] >> disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule (cj 2 calldata_terminal_array_memory) >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  fs[entry_loop_prefix_def, entry_bytes_array_inv_def,
     entry_bytes_array_config_def, Excl "enc_def"] >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Canonical initialization keeps the decoded interval inside its actual owner. *)
Theorem owned_array_canonical_initializer:
  entry_array_init_resources dst src maxn abi_sz
    (st,guard_st,header_st,loop_st,ip,cnt) (ctx,fn,site,d,sz,b,cap,p,initial) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb
    (LENGTH (enc (Array NONE aty) (ListV avs))) d sz b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE aty) (ListV avs)))
    (abi_decode_source CALLDATALOAD initial) = enc (Array NONE aty) (ListV avs) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ LENGTH avs <= maxn /\
  abi_alloca_history (fn_insts fn) initial /\ fn_has_code st loop_st fn /\
  (!i. MEM i (emitted_insts st loop_st) ==> MEM i (fn_insts fn)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  entry_owned_region oid root extent d sz initial /\ oid <> header_st.cs_next_id /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?t. entry_decode_path ctx fn initial t /\
    entry_owned_loop_resources ctx fn site header_st.cs_next_id p oid root extent d sz t /\
    abi_encoder_registered_effect {header_st.cs_next_id} [(d,32)] initial t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    eval_operand cnt t = SOME (n2w (LENGTH avs)) /\
    mem_word_at d t.vs_memory = n2w (LENGTH avs) /\
    entry_loop_fields initial t /\ fresh_vars_wrt limit_st t /\ ~t.vs_halted /\
    t.vs_current_bb = loop_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op initial) /\
    abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb
      (LENGTH (enc (Array NONE aty) (ListV avs))) d sz b cap t /\
    mem_bytes_at sb (LENGTH (enc (Array NONE aty) (ListV avs)))
      (abi_decode_source CALLDATALOAD t) = enc (Array NONE aty) (ListV avs) /\
    (!id. id <> header_st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (if FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE then
       t.vs_alloca_next = initial.vs_alloca_next+32 else t.vs_alloca_next = initial.vs_alloca_next)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `entry_array_init_resources _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [entry_array_init_resources_def]) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abiDecoderTypedContractTheory.abi_decoder_ranges_def]) >>
  `d < dimword (:256)` by decide_tac >>
  `abi_decode_load CALLDATALOAD (n2w sb:bytes32) initial = n2w (LENGTH avs)` by
    (irule abiCanonicalHeadSizeTheory.canonical_dynamic_array_count_load >>
     qexists_tac `aty` >> asm_rewrite_tac[]) >>
  drule_all owned_array_initializer >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  pure_rewrite_tac[abiDecoderTypedContractTheory.abi_decoder_ranges_def] >>
  asm_rewrite_tac[] >>
  fs[entry_loop_fields_def, abi_decode_source_def, Excl "enc_def"] >>
  metis_tac[]
QED

Theorem owned_initializer_header[local]:
  ~prepared.vs_halted /\ prepared.vs_current_bb = loop_st.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
  lookup_block loop_st.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := loop_st.cs_current_bb; bb_instructions :=
      loop_st.cs_current_insts ++ [mk_inst loop_st.cs_next_id JMP [Label hdr] []]|> /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  entry_owned_loop_resources ctx fn site cid p oid root extent d capacity prepared /\
  eval_operand ip prepared = SOME (n2w p) /\ eval_operand src prepared = SOME srcaddr /\
  mload p prepared = 0w /\ abi_decode_load CALLDATALOAD srcaddr prepared = n2w (LENGTH xs) /\
  p < dimword (:256) /\ fresh_vars_wrt limit_st prepared /\
  mem_word_at d prepared.vs_memory = n2w (LENGTH xs) ==>
  entry_decode_path ctx fn prepared (jump_to hdr prepared) /\
  entry_owned_loop_inv ctx fn site hdr ip src (n2w p) srcaddr tv xs
    d capacity cid oid root extent 0 (jump_to hdr prepared) /\
  entry_bytes_array_inv next limit_st d outsz p (LENGTH xs) prepared (jump_to hdr prepared) /\
  entry_loop_fields prepared (jump_to hdr prepared) /\
  abi_encoder_registered_effect ids outs prepared (jump_to hdr prepared)
Proof
  strip_tac >> conj_tac
  >- (`prepared with vs_inst_idx := LENGTH loop_st.cs_current_insts = prepared` by
        simp[venom_state_component_equality] >>
      drule_all entry_initializer_header_jump_path >> simp[]) >>
  `remaining_alloca_budget (fn_insts fn) (jump_to hdr prepared) =
   remaining_alloca_budget (fn_insts fn) prepared` by
    (irule remaining_alloca_budget_domain_cong >> simp[jump_to_def]) >>
  gvs[entry_owned_loop_inv_def, entry_owned_loop_resources_def, entry_owned_region_def,
     abi_decode_loop_ready_def, entry_loop_prefix_def, entry_bytes_array_inv_def,
     entry_loop_fields_def, abi_encoder_registered_effect_def, jump_to_def,
     alloca_frontier_inv_def, abi_alloca_history_def, alloca_inv_def,
     allocas_non_overlapping_def, alloca_next_valid_def,
     compileEnvTheory.fresh_vars_wrt_def, eval_operand_def, lookup_var_def,
     abi_decode_load_def, abi_decode_source_def, mload_def,
     abiDecoderFrameTheory.abi_decode_footprint_frame_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem entry_owned_canonical_bytes_array_execution:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (DecDynArray (DecBytestring n) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) T maxn) st = ((),final) /\
  fn_has_code st final fn /\
  (!bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecBytestring n) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) T maxn) (ListV avs) (ArrayV (DynArrayV xs)) /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  is_dynamic (vyper_to_abi_type env ty) /\
  type_memory_bytes ce ty = type_memory_size tv /\ EVERY (val_wf tv) xs /\
  LENGTH xs = LENGTH avs /\ LENGTH xs <= maxn /\
  maxn < dimword (:256) /\ n < dimword (:256) /\
  entry_array_init_resources dst src maxn (abi_embedded_static_size ce.ce_struct_fields ty)
    (st,guard_st,header_st,loop_st,ip,cnt)
    (ctx,fn,site,d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)),b,cap,p,initial) /\
  (!i. MEM i (emitted_insts st loop_st) ==> MEM i (fn_insts fn)) /\
  entry_owned_region oid root extent d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) initial /\
  oid <> header_st.cs_next_id /\ abi_alloca_history (fn_insts fn) initial /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD initial) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  fresh_vars_wrt limit_st initial /\ final.cs_next_var <= limit_st.cs_next_var /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d t.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\ fresh_vars_wrt limit_st t /\
    entry_owned_loop_resources ctx fn site header_st.cs_next_id p oid root extent d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) t /\
    entry_loop_fields initial t /\ entry_decode_path ctx fn initial t /\
    abi_encoder_registered_effect {header_st.cs_next_id}
      [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))] initial t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
       eval_operand op t = SOME w) /\
    (!id. id <> header_st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (if FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE then
       t.vs_alloca_next = initial.vs_alloca_next+32 else t.vs_alloca_next = initial.vs_alloca_next)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `entry_array_init_resources _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [entry_array_init_resources_def]) >>
  drule_all entry_bytes_array_code_split >> strip_tac >>
  drule_all entry_bytes_array_compile_phases >> strip_tac >>
  drule_all entry_bytes_array_initial_live >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all entry_bytes_array_phase_layout >> strip_tac >>
  `loop_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `LENGTH avs <= maxn` by decide_tac >>
  drule_all owned_array_canonical_initializer >>
  disch_then (qx_choose_then `prepared` strip_assume_tac) >>
  suspend "assembly"
QED

Resume entry_owned_canonical_bytes_array_execution[assembly]:
  `p < dimword (:256)` by
    (qpat_assum `alloca_frontier_inv _ _ _ initial` mp_tac >>
     simp_tac bool_ss [alloca_frontier_inv_def] >> strip_tac >>
     qpat_x_assum `FLOOKUP initial.vs_allocas _ = NONE /\ _ \/ _` strip_assume_tac >>
     gvs[] >> decide_tac) >>
  `d+type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= p \/ p+32 <= d` by
    (drule entry_owned_region_counter_separation >>
     disch_then (qspecl_then [`p`,`header_st.cs_next_id`] mp_tac) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `entry_bytes_array_config
    ((ce,env,sf,ty,tv,maxn,
       DecDynArray (DecBytestring n) (abi_embedded_static_size ce.ce_struct_fields ty)
         (type_memory_bytes ce ty) T maxn,avs,xs,n),
     (ip,src,dst,ops,body_st,middle,last,limit_st),
     (loop_st.cs_next_var,d,(n2w p:bytes32),(n2w sb:bytes32),sb,b,cap,oid,
       type_memory_bytes ce (ArrayT ty (Dynamic maxn))),
     (ctx,fn,FST labels,FST (SND labels),SND (SND labels),loop_st.cs_next_id+1,
      last.cs_current_bb,last.cs_current_insts,last.cs_next_id,
      STRING #"%" (toString body_st.cs_next_var),last.cs_next_var))` by
    (irule entry_bytes_array_concrete_config >> simp[Excl "enc_def", SF SFY_ss]) >>
  qmatch_asmsub_abbrev_tac `entry_bytes_array_config cfg` >>
  suspend "configured"
QED

Resume entry_owned_canonical_bytes_array_execution[configured]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  drule_all abiDecoderRecursiveLoopEntryTheory.abi_decoder_loop_phase_entry >> strip_tac >>
  drule_all abiDecoderRecursiveLoopLayoutTheory.abi_decoder_loop_phase_lookups >> strip_tac >>
  `eval_operand src prepared = SOME (n2w sb)` by
    (qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ prepared` mp_tac >>
     pure_rewrite_tac[abiDecoderTypedContractTheory.abi_decoder_ranges_def] >> metis_tac[]) >>
  `abi_decode_load CALLDATALOAD (n2w sb:bytes32) prepared = n2w (LENGTH avs)` by
    (irule abiCanonicalHeadSizeTheory.canonical_dynamic_array_count_load >>
     qexists_tac `vyper_to_abi_type env ty` >> asm_rewrite_tac[] >>
     qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ prepared` mp_tac >>
     pure_rewrite_tac[abiDecoderTypedContractTheory.abi_decoder_ranges_def] >> metis_tac[]) >>
  qpat_assum `LENGTH xs = LENGTH avs` (SUBST_ALL_TAC o SYM) >>
  `entry_decode_path ctx fn prepared (jump_to (FST labels) prepared) /\
   entry_owned_loop_inv ctx fn site (FST labels) ip src (n2w p) (n2w sb) tv xs d
     (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) header_st.cs_next_id oid root extent 0
     (jump_to (FST labels) prepared) /\
   entry_bytes_array_inv loop_st.cs_next_var limit_st d
     (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) p (LENGTH xs) prepared
     (jump_to (FST labels) prepared) /\
   entry_loop_fields prepared (jump_to (FST labels) prepared) /\
   abi_encoder_registered_effect {header_st.cs_next_id}
     [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))] prepared
     (jump_to (FST labels) prepared)` by
    (irule owned_initializer_header >> simp[Excl "enc_def", SF SFY_ss,
       abi_decode_header_insts_def, phi_prefix_length_def, venomInstTheory.mk_inst_def] >>
     qexists_tac `loop_st` >> simp[venomInstTheory.mk_inst_def]) >>
  `32+LENGTH xs*type_memory_size tv <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    simp[Once compileEnvTheory.type_memory_bytes_def, LE_MULT_RCANCEL] >>
  qpat_assum `Abbrev (cfg = _)` (assume_tac o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule owned_bytes_loop_endpoint >> simp[Excl "enc_def"] >>
  disch_then drule_all >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  `(!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
       eval_operand op t = SOME w) /\
    (!id. id <> header_st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (if FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE then
       t.vs_alloca_next = initial.vs_alloca_next+32 else t.vs_alloca_next = initial.vs_alloca_next)` by
    suspend "producer_frame" >>
  qexists_tac `t` >> simp[Excl "enc_def"] >> suspend "final_frame"
QED

Resume entry_owned_canonical_bytes_array_execution[final_frame]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  qpat_x_assum `entry_bytes_array_inv _ _ _ _ _ _ _ t` mp_tac >>
  qpat_x_assum `entry_loop_trace _ _ _ _ _ t` mp_tac >>
  qpat_x_assum `entry_loop_fields initial prepared` mp_tac >>
  qpat_x_assum `entry_loop_fields prepared _` mp_tac >>
  qpat_x_assum `entry_decode_path _ _ initial prepared` mp_tac >>
  qpat_x_assum `entry_decode_path _ _ prepared _` mp_tac >>
  qpat_x_assum `abi_encoder_registered_effect _ _ initial prepared` mp_tac >>
  qpat_x_assum `abi_encoder_registered_effect _ _ prepared _` mp_tac >>
  qpat_x_assum `32 + LENGTH xs * _ <= _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
  `fresh_vars_wrt limit_st t` by
    (qpat_assum `entry_bytes_array_inv _ _ _ _ _ _ _ t` mp_tac >>
     simp_tac bool_ss [entry_bytes_array_inv_def] >> metis_tac[]) >>
  qpat_x_assum `entry_bytes_array_inv _ _ _ _ _ _ _ t` kall_tac >>
  qpat_x_assum `entry_loop_trace _ _ _ _ _ t`
    (strip_assume_tac o PURE_REWRITE_RULE [entryReachBodyOperationalLoopTheory.entry_loop_trace_def]) >>
  `abi_encoder_registered_effect {header_st.cs_next_id}
     [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))] initial prepared` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`{header_st.cs_next_id}`, `[(d,32)]`] >> simp[] >>
     rpt strip_tac >> decide_tac) >>
  `abi_encoder_registered_effect {header_st.cs_next_id}
     [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))]
     (jump_to (FST labels) prepared) t` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`{header_st.cs_next_id}`, `[(d,LENGTH xs * type_memory_size tv + 32)]`] >>
     simp[] >> rpt strip_tac >> decide_tac) >>
  metis_tac[entryReachBodyRegisteredChildTheory.entry_registered_fields_trans, entry_decode_path_trans,
            abi_encoder_registered_effect_trans]
QED
Resume entry_owned_canonical_bytes_array_execution[producer_frame]:
  markerLib.RESUME_TAC >>
  `st.cs_next_var <= loop_st.cs_next_var` by
    (drule abi_decode_array_loop_init_shape >> simp[abi_decode_source_opcode_def]) >>
  qpat_x_assum `entry_bytes_array_inv _ _ _ _ _ _ _ t` mp_tac >>
  qpat_x_assum `!op. abi_decoder_operand_live st.cs_next_var op ==> _` mp_tac >>
  qpat_x_assum `!id. id <> header_st.cs_next_id ==> _` mp_tac >>
  qpat_x_assum `if FLOOKUP initial.vs_allocas _ = NONE then _ else _` mp_tac >>
  qpat_x_assum `st.cs_next_var <= loop_st.cs_next_var` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac (srw_ss()) [entry_bytes_array_inv_def, jump_to_def] >>
  rpt strip_tac >>
  metis_tac[abiDecoderReentryTheory.abi_decoder_operand_live_mono]
QED
Finalise entry_owned_canonical_bytes_array_execution
