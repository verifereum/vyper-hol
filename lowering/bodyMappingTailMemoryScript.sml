(* Counted instruction safety for the mapping hash tail. *)
Theory bodyMappingTailMemory
Ancestors
  bodyMappingKeyMemory exprSimMapKey bodyAllocMemory allocaFootprint
  abiBuiltinAllocation instMemFrontier fragExecMem fragExec exprLowering
  exprLoweringProps loweringStateRelDefs emitHelper emitHelperProps
  context venomExecSemantics venomState venomInst venomMemDefs
  finite_map words list rich_list compileEnv abiDecoderIndexInit dynCopyExec
  freshWrites exprSimWordArgs mappingTailFrames venomMemProps venomInstProofs
  fragGasSeqMem allocaHistoryFragment exprBopSimProps

Theorem mapping_slot_store_hash_mem[local]:
  eval_operand (Var x) s = SOME (n2w p) /\ eval_operand key s = SOME k /\
  key <> Var y /\ x <> y /\ p + 64 < dimword (:256) /\
  p + 64 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst a MSTORE [Var x; base_op] [];
     mk_inst b ADD [Var x; Lit 32w] [y];
     mk_inst c MSTORE [Var y; key] [];
     mk_inst d SHA3 [Var x; Lit 64w] [z]] s
Proof
  strip_tac >>
  Cases_on `eval_operand base_op s` >-
    simp[run_inst_seq_mem_ok_cons, below_frontier_MSTORE,
      step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def] >>
  rename1 `eval_operand base_op s = SOME w` >>
  `step_inst_base (mk_inst a MSTORE [Var x; base_op] []) s =
     OK (mstore p w s)` by
    (`p < dimword (:256) /\ p + 32 <= s.vs_alloca_next` by decide_tac >>
     metis_tac[scratch_mstore_mem_ok]) >>
  simp[run_inst_seq_mem_ok_cons, below_frontier_MSTORE] >>
  `eval_operand (Var x) (mstore p w s) = SOME (n2w p)` by
    gvs[eval_operand_def, lookup_var_def, mstore_def] >>
  drule step_ADD >> disch_then (qspec_then `Lit 32w` mp_tac) >>
  simp[eval_operand_def] >>
  disch_then (qspecl_then [`b`, `y`] assume_tac) >>
  simp[mk_inst_def, below_frontier_no_ranges] >>
  `eval_operand key (update_var y (n2w p + 32w) (mstore p w s)) = SOME k` by
    (Cases_on `key` >> gvs[eval_operand_def, lookup_var_def,
      update_var_def, mstore_def, FLOOKUP_UPDATE]) >>
  `n2w p + 32w = (n2w (p+32):bytes32)` by simp[word_add_n2w] >>
  `eval_operand (Var y) (update_var y (n2w p + 32w) (mstore p w s)) =
     SOME (n2w (p+32))` by
    simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst c MSTORE [Var y; key] [])
     (update_var y (n2w p + 32w) (mstore p w s)) =
     OK (mstore (p+32) k (update_var y (n2w p + 32w) (mstore p w s)))` by
    (`p+32 < dimword (:256)` by decide_tac >>
     irule (cj 1 scratch_mstore_mem_ok) >>
     simp[update_var_def, mstore_def]) >>
  gvs[mk_inst_def] >>
  conj_tac >-
    (simp[lookup_var_def, update_var_def, mstore_def, FLOOKUP_UPDATE] >>
     `p+32 < dimword (:256)` by decide_tac >> simp[]) >>
  simp[GSYM mk_inst_def, run_inst_seq_mem_ok_last, below_frontier_SHA3] >>
  `eval_operand (Var x) (update_var y (n2w (p+32)) (mstore p w s)) =
     SOME (n2w p)` by (irule eval_operand_update_other_local >> simp[]) >>
  `p < dimword (:256)` by decide_tac >>
  simp[eval_operand_def]
QED

Theorem mapping_slot_seq_mem:
  compile_mapping_subscript base_op key sa = (op,sb) /\
  (!v. base_op = Var v ==> not_fresh_at sa v) /\
  (!v. key = Var v ==> not_fresh_at sa v) /\
  eval_operand base_op s = SOME b /\ eval_operand key s = SOME k /\
  alloca_next_valid s /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 64 s).vs_allocas
    sa.cs_next_id = SOME (p,64) /\ p + 64 < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `p + 64 <= (abi_builtin_allocate_state sa.cs_next_id 64 s).vs_alloca_next`
    by (drule_all alloca_site_frontier >> simp[]) >>
  `!n w. sa.cs_next_var <= n ==>
     eval_operand base_op (update_var (STRING #"%" (toString n)) w s) = SOME b /\
     eval_operand key (update_var (STRING #"%" (toString n)) w s) = SOME k` by
    (rpt strip_tac >> irule eval_operand_update_other_local >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[not_fresh_at_def]) >>
  qpat_x_assum `compile_mapping_subscript _ _ _ = _` mp_tac >>
  simp[compile_mapping_subscript_def, compile_alloc_buffer_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  `!j. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + j) = 0`
    by decide_tac >>
  simp[emitted_insts_def, DROP_APPEND] >>
  drule step_alloca_site >>
  disch_then (qspec_then `STRING #"%" (toString sa.cs_next_var)` mp_tac) >>
  simp[dimword_def] >> strip_tac >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_no_ranges, mk_inst_def] >>
  irule (SRULE [mk_inst_def] mapping_slot_store_hash_mem) >>
  conj_tac >- simp[ASCIInumbersTheory.toString_inj] >>
  conj_tac >-
    (strip_tac >> first_x_assum drule >> simp[not_fresh_at_def]) >>
  reverse conj_tac >-
    (qexists_tac `p` >>
     simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  qexists_tac `k` >>
  Cases_on `key` >>
  gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
      abi_builtin_allocate_state_def]
QED

Theorem mapping_slot_body_seq_mem:
  compile_mapping_subscript base_op key sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
  (!v. base_op = Var v ==> not_fresh_at sa v) /\
  (!v. key = Var v ==> not_fresh_at sa v) /\
  eval_operand base_op s = SOME b /\ eval_operand key s = SOME k ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> drule_all mapping_alloca_code >> strip_tac >>
  `?p. FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 64 s).vs_allocas
        sa.cs_next_id = SOME (p,64)` by
    (simp[alloca_site_cases] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >- simp[] >>
     PairCases_on `x` >> fs[stmt_state_rel_def] >>
     qpat_x_assum `!inst n base sz. _` drule >> simp[mk_inst_def, dimword_def]) >>
  `alloca_next_valid s /\ alloca_room ctx func s` by
    fs[stmt_state_rel_def, alloca_inv_def] >>
  `p+64 < dimword (:256)` by
    (fs[alloca_site_cases] >-
       (`sa.cs_next_id NOTIN FDOM s.vs_allocas` by fs[FLOOKUP_DEF] >>
        drule alloca_room_fresh >> disch_then drule >>
        simp[mk_inst_def, dimword_def]) >>
     drule_all alloca_room_next_lt >> fs[alloca_next_valid_def] >>
     first_x_assum drule >> decide_tac) >>
  irule mapping_slot_seq_mem >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

Theorem compile_hashmap_tail_seq_mem:
  expr_post ctx func cenv cx e es sa sn s0 en kv key s /\
  expr_store_bound cx (expr_type e) kv key s /\
  expr_type e = kt /\ hashmap_key_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv kv /\
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript base_op hashed sp = (slot,sb) /\
  (!x. key = Var x ==> not_fresh_at sn x) /\
  (!x. base_op = Var x ==> not_fresh_at sn x) /\
  eval_operand base_op s = SOME base_slot /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sn /\
  fn_has_code sp sb func ==>
  run_inst_seq_mem_ok (emitted_insts sn sb) s
Proof
  strip_tac >>
  Cases_on `is_bytestring_type kt` >-
    (gvs[] >>
     drule compile_hashmap_dynamic_key_frame >>
     disch_then (qspecl_then [`tv`, `sp`, `hashed`, `expr_type e`] mp_tac) >>
     simp[] >> strip_tac >>
     `run_inst_seq_mem_ok (emitted_insts sn sp) s` by
       (irule compile_mapping_bytestring_key_mem_ok >>
        goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     `sn.cs_next_var <= sp.cs_next_var /\
      sp.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sp /\
      (!x. hashed = Var x ==> not_fresh_at sp x)` by
       (drule (cj 1 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >>
        strip_tac >> gvs[]) >>
     `sb.cs_current_insts = sp.cs_current_insts ++ emitted_insts sp sb` by
       (drule (cj 2 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >> simp[]) >>
     `emitted_insts sn sb = emitted_insts sn sp ++ emitted_insts sp sb` by
       (irule emitted_insts_append >> simp[]) >>
     asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[] >>
     rpt strip_tac >> gvs[] >>
     drule mapping_slot_body_seq_mem >> disch_then irule >> simp[] >>
     conj_tac >- metis_tac[not_fresh_at_mono] >>
     Cases_on `base_op` >> gvs[eval_operand_def] >>
     qpat_assum `t with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >> simp[] >> metis_tac[]) >>
  gvs[] >>
  drule mapping_slot_body_seq_mem >> disch_then irule >> simp[] >>
  gvs[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def] >>
  metis_tac[]
QED

Theorem mapping_slot_frontier[local]:
  compile_mapping_subscript base_op key sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  qpat_x_assum `compile_mapping_subscript _ _ _ = _` mp_tac >>
  simp[compile_mapping_subscript_def, compile_alloc_buffer_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  `!j. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + j) = 0`
    by decide_tac >>
  gvs[emitted_insts_def, DROP_APPEND, run_inst_seq_def, AllCaseEqs()] >>
  imp_res_tac venomMemPropsTheory.step_inst_base_preserves_alloca_next >>
  gvs[mk_inst_def] >>
  qpat_x_assum `step_inst_base _ s = OK _` mp_tac >>
  simp[step_inst_base_opcode_eqs] >>
  strip_tac >> drule venomMemPropsTheory.exec_alloca_alloca_next_mono >> simp[]
QED

Theorem compile_hashmap_tail_frontier[local]:
  expr_post ctx func cenv cx e es sa sn s0 en kv key s /\
  expr_type e = kt /\ hashmap_key_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv kv /\
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript base_op hashed sp = (slot,sb) /\
  (!x. key = Var x ==> not_fresh_at sn x) /\ local_ptrs_reserved cenv sn /\
  run_inst_seq (emitted_insts sn sb) s = OK u ==>
  s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> Cases_on `is_bytestring_type kt`
  >- (gvs[] >> drule compile_hashmap_dynamic_key_frame >>
      disch_then (qspecl_then [`tv`, `sp`, `hashed`, `expr_type e`] mp_tac) >>
      simp[] >> strip_tac >>
      `sp.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sp` by
        (drule (cj 1 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >> simp[]) >>
      `sb.cs_current_insts = sp.cs_current_insts ++ emitted_insts sp sb` by
        (drule (cj 2 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >> simp[]) >>
      `emitted_insts sn sb = emitted_insts sn sp ++ emitted_insts sp sb` by
        (irule emitted_insts_append >> simp[]) >>
      `run_inst_seq (emitted_insts sp sb) t = OK u` by
        (metis_tac[run_inst_seq_append]) >>
      `t.vs_alloca_next = s.vs_alloca_next` by
        (qpat_assum `t with vs_vars := _ = _`
           (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next`) >> simp[]) >>
      drule_all mapping_slot_frontier >> simp[]) >>
  gvs[] >> drule_all mapping_slot_frontier >> simp[]
QED

Theorem compile_hashmap_tail_mem_path[local]:
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript base_op hashed sp = (slot,sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sn sb) s /\
  run_inst_seq (emitted_insts sn sb) s = OK t ==>
  gas_marked_path T ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> drule_all compile_hashmap_tail_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sn sb)` by fs[EVERY_MEM] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sn sb)` by
    fs[EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sn sb) = []` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sn sb) = LENGTH sb.cs_current_insts`
    by simp[] >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sn sb ++ rest` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND1] >> metis_tac[APPEND_ASSOC]) >>
  `isPREFIX (emitted_insts sn sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND3] >>
  drule_all alloca_history_run_inst_seq >> strip_tac >>
  simp[fragGasModeTheory.gas_marked_path_def] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` mp_tac) >> gvs[]
QED

Theorem compile_mapping_index_success_tail_mem:
  expr_post ctx func cenv cx idx em sm sn s1 en kv key t /\
  expr_type idx = kt /\ hashmap_key_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv kv /\
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript base_op hashed sp = (slot,sb) /\
  (!x. key = Var x ==> not_fresh_at sn x) /\
  (!x. base_op = Var x ==> not_fresh_at sm x) /\ (!l. base_op <> Label l) /\
  eval_operand base_op s1 = SOME base_slot /\
  fn_inst_ids_distinct func /\ fn_has_code sp sb func /\ fn_has_code sn sb func /\
  stmt_state_rel ctx func cenv cx em s1 /\ local_ptrs_reserved cenv sm /\
  MAP FDOM em.scopes = MAP FDOM en.scopes /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts /\
  expr_store_bound cx (expr_type idx) kv key t /\ alloca_history func t ==>
  ?u. gas_marked_path T ctx func t 0 (OK u) /\
      eval_operand slot u = SOME (hashmap_slot base_slot (encode_hashmap_key kt kv)) /\
      stmt_state_rel ctx func cenv cx en u /\ wb_frame cenv em en sm s1 u /\
      (~expr_has_effect idx ==> pure_frame cenv func em sm s1 u) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  `eval_operand base_op t = SOME base_slot` by
    (irule eval_operand_frame >> simp[] >> qexistsl_tac [`sm`, `s1`] >>
     gvs[loweringPostsTheory.expr_post_def]) >>
  `!x. base_op = Var x ==> not_fresh_at sn x` by
    metis_tac[not_fresh_at_mono] >>
  `local_ptrs_reserved cenv sn` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all compile_hashmap_tail_run >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sn sb) t` by
    (drule_all compile_hashmap_tail_seq_mem >> simp[]) >>
  `t.vs_alloca_next <= u.vs_alloca_next` by
    (drule_all compile_hashmap_tail_frontier >> simp[]) >>
  `alloca_inv t` by
    (drule expr_post_state >> simp[stmt_state_rel_def]) >>
  `gas_marked_path T ctx func t 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (drule_all compile_hashmap_tail_mem_path >> simp[]) >>
  `wb_frame cenv em en sm s1 u /\
   (~expr_has_effect idx ==> pure_frame cenv func em sm s1 u)` by
    (irule expr_post_suffix_frames >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `u.vs_current_bb = sb.cs_current_bb` by
    (drule_all compile_hashmap_tail_shape >> strip_tac >>
     `u.vs_current_bb = t.vs_current_bb` suffices_by gvs[same_blocks_def] >>
     drule_at (Pos hd)
       (Q.ISPEC `\s:venom_state. s.vs_current_bb` run_inst_seq_preserves_field) >>
     simp[] >> disch_then irule >> rpt strip_tac >> fs[EVERY_MEM] >>
     metis_tac[step_preserves_control_flow, step_inst_non_invoke]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx] >>
  qpat_x_assum `wb_frame cenv em en sm s1 u` mp_tac >>
  simp[loweringPostsTheory.wb_frame_def, lookup_var_def] >>
  strip_tac >> first_assum ACCEPT_TAC
QED
