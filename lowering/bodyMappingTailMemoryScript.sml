(* Counted instruction safety for the mapping hash tail. *)
Theory bodyMappingTailMemory
Ancestors
  bodyMappingKeyMemory exprSimMapKey bodyAllocMemory allocaFootprint
  abiBuiltinAllocation instMemFrontier fragExecMem fragExec exprLowering
  exprLoweringProps loweringStateRelDefs emitHelper emitHelperProps
  context venomExecSemantics venomState venomInst venomMemDefs
  finite_map words list rich_list compileEnv abiDecoderIndexInit dynCopyExec

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
      step_inst_base_def, mk_inst_def, exec_write2_def] >>
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
