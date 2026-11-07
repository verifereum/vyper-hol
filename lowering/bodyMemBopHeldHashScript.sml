(* Read bounds for the comparison hash (ADD, MLOAD, SHA3). *)
Theory bodyMemBopHeldHash
Ancestors
  exprSimHashBoundary
  bodyMemBiKeccakBounds bodyMemBiKeccakSuffix bytestringHashProps
  fragGasSeqMem allocaHistoryFragment exprSimMemDefs exprSimHash
  exprLowering emitHelper emitHelperProps compileEnv venomMemDefs
  venomInst venomExecSemantics words list exprLoweringProps
  fragExec fragExecMem instMemFrontier venomState venomMemProps memSafeRun
  valueEncoding valueEncodingProps rich_list exprSimMapKey

Theorem held_hash_mem_ok:
  compile_bytestring_hash x sa = (op,sb) /\
  (!v. x = Var v ==> not_fresh_at sa v) /\
  eval_operand x s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w n /\
  b + 32 < dimword (:256) /\ n < dimword (:256) /\
  b + 32 <= s.vs_alloca_next /\
  (n = 0 \/ b + 32 + n <= s.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[compile_bytestring_hash_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, emit_op_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!k. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + k) = 0`
    by decide_tac >>
  qpat_x_assum `_ with <| cs_next_var := _; cs_next_id := _;
      cs_current_insts := _ |> = sb` (SUBST1_TAC o SYM) >>
  simp[emitted_insts_def, DROP_APPEND] >>
  rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  drule step_ADD >>
  disch_then (qspec_then `Lit 32w` mp_tac) >>
  simp[eval_operand_def] >>
  disch_then (qspecl_then [`sa.cs_next_id`,
    `STRING #"%" (toString sa.cs_next_var)`] assume_tac) >>
  simp[] >>
  `eval_operand x (update_var (STRING #"%" (toString sa.cs_next_var))
      (n2w b + 32w) s) = SOME (n2w b)` by
    (irule eval_operand_update_other_local >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[not_fresh_at_def]) >>
  conj_tac >- simp[below_frontier_MLOAD, update_var_def] >>
  drule step_MLOAD_local >>
  disch_then (qspecl_then [`STRING #"%" (toString (sa.cs_next_var + 1))`,
                          `sa.cs_next_id + 1`] assume_tac) >>
  simp[run_inst_seq_mem_ok_last, below_frontier_SHA3] >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, ASCIInumbersTheory.toString_inj,
       GSYM mem_word_at_eq_mload, GSYM word_add_n2w] >>
  Cases_on `n = 0` >> simp[] >>
  `n2w b + 32w = (n2w (b + 32):256 word)` by simp[word_add_n2w] >>
  simp[] >> decide_tac
QED

Theorem held_hash_counted_nofresh:
  compile_bytestring_hash x sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  b + 32 <= s.vs_alloca_next /\
  (LENGTH bs = 0 \/ b + 32 + LENGTH bs <= s.vs_alloca_next) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    eval_operand op t = SOME (word_of_bytes_be (Keccak_256_w64 bs):bytes32) /\
    stmt_state_rel ctx func cenv cx es t /\
    (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s) /\
    (!p w. (!z. p = Var z ==> not_fresh_at sa z) /\
           eval_operand p s = SOME w ==> eval_operand p t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ alloca_history func t /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_bytestring_hash_run_nofresh >> strip_tac >>
  drule_all held_hash_mem_ok >> strip_tac >>
  drule_all compile_bytestring_hash_shape >> strip_tac >>
  `LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts +
     LENGTH (emitted_insts sa sb)` by metis_tac[listTheory.LENGTH_APPEND] >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (conj_tac
     >- (fs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
         qpat_x_assum `LENGTH sb.cs_current_insts = _` kall_tac >>
         metis_tac[DROP_APPEND, emitted_insts_def]) >>
     decide_tac) >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  drule_all run_inst_seq_gas_path_mem >> simp[] >> strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  drule_all alloca_history_run_inst_seq >> simp[] >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule hash_readonly_state_rel >> goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[venom_state_component_equality, stmt_state_rel_inst_idx,
      eval_operand_def, lookup_var_def] >>
  rpt strip_tac >> Cases_on `p` >>
  gvs[eval_operand_def, lookup_var_def]
QED
