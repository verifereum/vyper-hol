(* Counted mapping scratch allocation, stores, and hash reads. *)
Theory targetMappingSuffixMemory
Ancestors
  targetSubscriptMapping bodyAllocMemory bodyMemTbExtract32MemoryTransfer
  bodyMemBiMethodIdSuffix bodyMemBiSha256Compose entrySinkExtraction
  bodyDeclMemoryCounted entryDecoderHistoryFrame allocaHistoryFragment
  exprSimHashBoundary exprSimHash exprSimMapKey exprOperandVar exprSimOperators
  valueEncodingProps words ASCIInumbers exprSimProps freshWrites varsExt fragExec fragExecMem memSafeRun instMemFrontier
  venomMemDefs exprLowering exprLoweringProps emitHelper emitHelperProps
  context compileEnv loweringPosts loweringStateRelDefs fragGasMode
  venomExecSemantics venomState venomInst list rich_list finite_map
Libs
  pairLib

Theorem target_mapping_store_frontier_vars_ext[local]:
  vars_ext s big /\
  ((?t. step_inst_base (mk_inst id MSTORE [addr; value] []) s = OK t) \/
   (?a t. step_inst_base (mk_inst id MSTORE [addr; value] []) s = Abort a t)) /\
  inst_mem_below_frontier (mk_inst id MSTORE [addr; value] []) s ==>
  inst_mem_below_frontier (mk_inst id MSTORE [addr; value] []) big /\
  inst_dload_in_section (mk_inst id MSTORE [addr; value] []) big
Proof
  strip_tac >>
  Cases_on `eval_operand addr s` >> Cases_on `eval_operand value s` >>
  gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
      below_frontier_MSTORE, inst_dload_in_section_def] >>
  qpat_x_assum `vars_ext s big` (strip_assume_tac o REWRITE_RULE [vars_ext_def]) >>
  qpat_x_assum `big = _` SUBST1_TAC >> simp[eval_operand_vars_ext]
QED

Theorem target_mapping_hash_frontier_vars_ext[local]:
  vars_ext s big /\
  ((?t. step_inst_base (mk_inst id SHA3 [addr; len] [out]) s = OK t) \/
   (?a t. step_inst_base (mk_inst id SHA3 [addr; len] [out]) s = Abort a t)) /\
  inst_mem_below_frontier (mk_inst id SHA3 [addr; len] [out]) s ==>
  inst_mem_below_frontier (mk_inst id SHA3 [addr; len] [out]) big /\
  inst_dload_in_section (mk_inst id SHA3 [addr; len] [out]) big
Proof
  strip_tac >>
  Cases_on `eval_operand addr s` >> Cases_on `eval_operand len s` >>
  gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
      below_frontier_SHA3, inst_dload_in_section_def] >>
  qpat_x_assum `vars_ext s big` (strip_assume_tac o REWRITE_RULE [vars_ext_def]) >>
  qpat_x_assum `big = _` SUBST1_TAC >> simp[eval_operand_vars_ext]
QED

Theorem target_mapping_mem_opcode_shape[local]:
  compile_mapping_subscript bop key sa = (op,sb) ==>
  EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    (?id a b. i = mk_inst id MSTORE [a;b] []) \/
    (?id a b out. i = mk_inst id SHA3 [a;b] [out])) (emitted_insts sa sb)
Proof
  simp[compile_mapping_subscript_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  pure_rewrite_tac[emitted_insts_def, APPEND_ASSOC] >>
  pure_rewrite_tac[DROP_LENGTH_APPEND] >>
  `!k. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + k) = 0` by decide_tac >>
  simp[DROP_APPEND, mk_inst_def] >> metis_tac[]
QED

Theorem target_mapping_body_mem_safe[local]:
  compile_mapping_subscript bop key sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~block_is_terminated sa /\ stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME b /\ eval_operand key s = SOME k ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es (drop_fresh sa s)` by
    simp[stmt_state_rel_drop_fresh] >>
  `eval_operand bop (drop_fresh sa s) = SOME b /\
   eval_operand key (drop_fresh sa s) = SOME k` by simp[eval_operand_drop_fresh] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) (drop_fresh sa s)` by
    (irule compile_mapping_subscript_body_mem_ok >>
     goal_assum (drule_at Any) >> simp[fresh_vars_wrt_drop_fresh] >> metis_tac[]) >>
  drule_all target_mapping_run >> strip_tac >>
  drule target_mapping_mem_opcode_shape >> strip_tac >>
  drule target_mapping_suffix_shape >> strip_tac >>
  irule run_inst_seq_mem_ok_total_vars_ext >>
  reverse conj_tac
  >- (conj_tac
      >- (fs[EVERY_MEM] >> rpt strip_tac >>
          qpat_x_assum `!i. MEM i _ ==> _ \/ _` drule >>
          strip_tac >> gvs[mk_inst_def, is_ext_call_op_def]) >>
      qexists `drop_fresh sa s` >> simp[vars_ext_drop_fresh] >> metis_tac[]) >>
  qpat_x_assum `EVERY (\i. _ \/ _) _` mp_tac >>
  rpt (pop_assum kall_tac) >> strip_tac >> rpt strip_tac >>
  `i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
   (?id a b. i = mk_inst id MSTORE [a;b] []) \/
   (?id a b out. i = mk_inst id SHA3 [a;b] [out])` by fs[EVERY_MEM] >>
  gvs[] >> simp[below_frontier_no_ranges, inst_dload_in_section_def] >> FIRST [irule (cj 1 target_mapping_store_frontier_vars_ext),
            irule (cj 1 target_mapping_hash_frontier_vars_ext)] >>
  qexists `u` >> simp[]
QED

Theorem target_mapping_suffix_mem:
  compile_mapping_subscript bop keyop sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~block_is_terminated sm /\
  stmt_state_rel ctx func cenv cx es' s /\
  local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  wb_frame cenv es es' sa s0 s /\
  (!x. bop = Var x ==> not_fresh_at sm x) /\
  (!x. keyop = Var x ==> not_fresh_at sm x) /\
  eval_operand bop s = SOME slot /\
  eval_operand keyop s = SOME (encode_hashmap_key kt key) /\
  extend_place cx (HashMapRef tr slot kt vt) (ValueSubscript key) es' =
    (INL pv, es'') /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    target_post ctx func cenv cx es sa sb s0 es'' pv vt
      (op,SOME (slot_loc tr),SOME (value_type_place vt)) t /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >>
  drule_all target_mapping_body_mem_safe >> strip_tac >>
  drule_all target_mapping_run >> strip_tac >>
  drule target_mapping_suffix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sb)` by fs[EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb) = []` by
    fs[FILTER_EQ_NIL, EVERY_MEM] >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all method_id_run_path_mem >> strip_tac >>
  drule_all sha256_run_inst_seq_alloca_next_mono >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `es'' = es'` by metis_tac[target_mapping_extend_place] >> gvs[] >>
  `wb_frame cenv es es' sa s0 t` by
    (irule wb_frame_allocating_tail >> conj_tac >- simp[] >>
     qexistsl [`s`, `es'.scopes`, `sm`] >> simp[] >> metis_tac[]) >>
  qexists `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[] >> irule target_mapping_post >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`es'`, `key`, `kt`, `slot`] >> simp[]
QED

Theorem target_keccak_key_mem_safe[local]:
  compile_keccak256_key key F sa = (op,sb) /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  eval_operand key s = SOME (n2w b) /\ mload b s = n2w len /\
  b+32 < dimword(:256) /\ len < dimword(:256) /\
  b+32 <= s.vs_alloca_next /\
  (len = 0 \/ b+32+len <= s.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[compile_keccak256_key_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >> gnvs[] >>
  `!k. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + k) = 0`
    by decide_tac >>
  simp[emitted_insts_def, DROP_APPEND] >>
  rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  drule step_ADD >> disch_then (qspec_then `Lit 32w` mp_tac) >>
  simp[eval_operand_def] >>
  disch_then (qspecl_then [`sa.cs_next_id`,
    `STRING #"%" (toString sa.cs_next_var)`] assume_tac) >> simp[] >>
  `eval_operand key (update_var (STRING #"%" (toString sa.cs_next_var))
      (n2w b + 32w) s) = SOME (n2w b)` by
    (irule eval_operand_update_other_local >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[not_fresh_at_def]) >>
  conj_tac >- simp[below_frontier_MLOAD, update_var_def] >>
  drule step_MLOAD_local >>
  disch_then (qspecl_then [`STRING #"%" (toString (sa.cs_next_var+1))`,
                          `sa.cs_next_id+1`] assume_tac) >> simp[] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_SHA3,
       eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, toString_inj, GSYM word_add_n2w] >>
  gvs[mload_def, GSYM word_add_n2w] >>
  Cases_on `len = 0` >> simp[] >>
  `n2w b + 32w = (n2w (b+32):bytes32)` by simp[word_add_n2w] >>
  simp[] >> decide_tac
QED

Theorem target_keccak_key_prefix_mem[local]:
  compile_keccak256_key key F sa = (op,sb) /\ fn_has_code sa sb func /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  eval_operand key s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
  b+32 < dimword(:256) /\ LENGTH bs < dimword(:256) /\
  b+32 <= s.vs_alloca_next /\
  (bs = [] \/ b+32+LENGTH bs <= s.vs_alloca_next) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fn_inst_ids_distinct func /\ alloca_history func s ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand op t = SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    stmt_state_rel ctx func cenv cx es t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule target_keccak_key_mem_safe >> goal_assum (drule_at Any) >>
     simp[GSYM mem_word_at_eq_mload] >>
     qexistsl [`key`, `LENGTH bs`, `op`] >> simp[]) >>
  drule_all compile_keccak256_key_run >> strip_tac >>
  drule target_keccak_key_suffix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    fs[FILTER_EQ_NIL, EVERY_MEM] >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all method_id_run_path_mem >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule hash_readonly_state_rel >> goal_assum (drule_at Any) >> simp[]) >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `t with vs_vars := _ = s`
       (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next`) >> simp[]) >>
  qpat_x_assum `!ctx. _` (qspec_then `ctx` strip_assume_tac) >>
  qexists `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def] >>
  qpat_x_assum `t with vs_vars := _ = s`
    (mp_tac o Q.AP_TERM `\z. z with vs_inst_idx := s.vs_inst_idx`) >> gvs[]
QED
