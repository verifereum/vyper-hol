(* Compiled fixed-bytes keccak: semantic and counted ghost endpoints agree. *)
Theory bodyPtrHashBuiltinsKeccakFixedFrame
Ancestors bodyPtrHashBuiltinsKeccakFixedRun bodyPtrHashBuiltinsFreshFrame
  bodyPtrHashBuiltinsCursor
  bodyPtrHashBuiltinsAllocFrame bodyPtrHashBuiltinsGhostFrame
  exprSimHash exprSimAlloc bodyPtrDefs fragGasSeqPtr ghostPcTransportPtr
  venomExecSemantics venomState venomInst ptrDiscipline exprLowering
  exprLoweringProps emitHelperProps compileEnv words finite_map rich_list

Theorem hash_fixed_keccak_ptr_frame:
  !value bs sa op sb s w ctx fn cenv cx es G tn d bb D PG.
    compile_keccak256_bytesm value (LENGTH bs) sa = (op,sb) /\
    (!x. value = Var x ==> not_fresh_at sa x) /\
    eval_operand value s = SOME w /\ op_taint tn value = {} /\
    LENGTH bs <= 32 /\ TAKE (LENGTH bs) (word_to_bytes_be w) = bs /\
    stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved cenv sa /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
    ghost_inv d cenv cx es G tn s /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
    ?u G3 tn3.
      run_inst_seq (emitted_insts sa sb) s = OK u /\
      u.vs_current_bb = s.vs_current_bb /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 G3 tn3
        (OK (u with vs_inst_idx := s.vs_inst_idx+3)) /\
      eval_operand op u = SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
      stmt_state_rel ctx fn cenv cx es u /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      ghost_inv d cenv cx es G3 tn3 u /\ ghost_kept cenv es sa G tn s G3 tn3 /\
      op_taint tn3 op = {} /\ op_prov G3 op = NONE /\
      ghost_inv d cenv cx es G3 tn3 (u with vs_inst_idx := s.vs_inst_idx+3) /\
      eval_operand op (u with vs_inst_idx := s.vs_inst_idx+3) =
        SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_keccak256_bytesm_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK u` >>
  `u.vs_current_bb = s.vs_current_bb` by
    (irule hash_run_inst_seq_current_bb >>
     goal_assum (drule_at Any) >> metis_tac[keccak_suffix_shape]) >>
  drule hash_fixed_keccak_emission >> strip_tac >>
  `?buf sm. compile_alloc_buffer 32 sa = (buf,sm)` by metis_tac[pairTheory.PAIR] >>
  drule_all hash_literal_alloc_store_frame >>
  disch_then (qspecl_then [`PG`, `sa.cs_next_id+1`] strip_assume_tac) >>
  qpat_x_assum `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> _` kall_tac >>
  qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _` kall_tac >>
  qpat_x_assum `!n b sz. local_region cenv es.scopes s n b sz ==> _` kall_tac >>
  qpat_x_assum `compile_keccak256_bytesm _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts sa sm) _ = _` kall_tac >>
  qpat_x_assum `buf.buf_operand = _` kall_tac >>
  qpat_x_assum `p = STRING _ _` SUBST_ALL_TAC >>
  `step_inst_base (mk_inst (sa.cs_next_id+1) MSTORE [Var (STRING #"%" (toString sa.cs_next_var));value] []) t =
    OK (mstore (w2n a) w t)` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def]) >>
  qabbrev_tac `s2 = mstore (w2n a) w t` >>
  `step_inst_base (mk_inst (sa.cs_next_id+2) SHA3
      [Var (STRING #"%" (toString sa.cs_next_var));Lit (n2w (LENGTH bs))] [STRING #"%" (toString (sa.cs_next_var+1))]) s2 = OK u` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = _` mp_tac >>
     simp[run_inst_seq_def, Abbr `s2`, AllCaseEqs()]) >>
  qpat_assum `emitted_insts sa sb = _` (fn th =>
    rule_assum_tac (REWRITE_RULE[th]) >> assume_tac th) >>
  qpat_assum `tn1 = _` (fn th =>
    rule_assum_tac (REWRITE_RULE[th]) >> assume_tac th) >>
  drule_all hash_alloc_store_sha3_counted >>
  disch_then (qspecl_then [`D`, `PG`, `G`] strip_assume_tac) >>
  qabbrev_tac `i1 = mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  qabbrev_tac `i2 = mk_inst (sa.cs_next_id+1) MSTORE
    [Var (STRING #"%" (toString sa.cs_next_var));value] []` >>
  qabbrev_tac `i3 = mk_inst (sa.cs_next_id+2) SHA3
    [Var (STRING #"%" (toString sa.cs_next_var));Lit (n2w (LENGTH bs))]
    [STRING #"%" (toString (sa.cs_next_var+1))]` >>
  `~is_terminator i2.inst_opcode /\ ~is_terminator i3.inst_opcode` by
    simp[Abbr `i2`, Abbr `i3`, mk_inst_def, is_terminator_def] >>
  drule_all hash_inst_seq_triple_endpoint_raw >> strip_tac >>
  suspend "finish"
QED

Resume hash_fixed_keccak_ptr_frame[finish]:
  `?h. u = update_var (STRING #"%" (toString (sa.cs_next_var+1))) h s2` by
    (qsuff_tac `?h. step_inst_base i3 s2 = OK
       (update_var (STRING #"%" (toString (sa.cs_next_var+1))) h s2)`
     >- (strip_tac >> qexists_tac `h` >> fs[]) >>
     qexists_tac `word_of_bytes T (0w:bytes32) (Keccak_256_w64
       (mem_bytes_at (w2n a) (w2n (n2w (LENGTH bs):bytes32)) s2.vs_memory))` >>
     simp[NoAsms, Abbr `i3`] >> irule step_SHA3_bytes >>
     simp[eval_operand_def, Abbr `s2`, lookup_var_def, mstore_def]) >>
  `~not_fresh_at sa (STRING #"%" (toString (sa.cs_next_var+1)))` by
    simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  `G' = step_prov PG G2 i3 u /\ tn' = step_taint i3 s2 u tn2` by metis_tac[] >>
  `ghost_inv d cenv cx es G' tn' u /\
   ghost_kept cenv es sa G tn s G' tn' /\ op_taint tn' op = {} /\
   op_prov G' op = NONE` by
    (qpat_assum `G' = step_prov PG G2 i3 u` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `tn' = step_taint i3 s2 u tn2` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `u = update_var _ _ _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `op = Var _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, Abbr `i3`] >> irule hash_sha3_fresh_frame >>
     metis_tac[]) >>
  qexistsl_tac [`u`, `G'`, `tn'`] >>
  simp[hash_ghost_inv_inst_idx]
QED

Finalise hash_fixed_keccak_ptr_frame
