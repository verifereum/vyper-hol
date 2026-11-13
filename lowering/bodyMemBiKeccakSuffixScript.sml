(* Memory checks for the fixed-bytes keccak scratch sequence. *)
Theory bodyMemBiKeccakSuffix
Ancestors
  exprSimHash exprSimAlloc exprSimDefs allocaFootprint bodyAllocMemory
  valueEncodingProps builtinHashing emitHelper emitHelperProps exprLoweringProps fragExecMem
  instMemFrontier compileEnv loweringStateRelDefs context venomState venomInst venomExecSemantics
  abiBuiltinAllocation venomMemDefs venomMemProps memSafeRun words list finite_map
Libs
  pairLib

Theorem keccak_fixed_suffix_mem_ok:
  compile_keccak256_bytesm x m sa = (op,sb) /\ m <= 32 /\
  eval_operand x s = SOME w /\ fresh_vars_wrt sa s /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
  ~block_is_terminated sa ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (mp_tac (Q.INST [`sha` |-> `F`, `v` |-> `x`] hash_fixed_alloca_code) >> simp[]) >>
  qpat_x_assum `compile_keccak256_bytesm _ _ _ = _` mp_tac >>
  simp[compile_keccak256_bytesm_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `compile_alloc_buffer 32 sa = (buf,sm)` >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  `alloca_next_valid s` by fs[stmt_state_rel_def, alloca_inv_def] >>
  `?p. FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas
      sa.cs_next_id = SOME (p,32)` by
    (simp[alloca_site_cases] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >- simp[] >>
     PairCases_on `x'` >>
     fs[stmt_state_rel_def] >>
     qpat_x_assum `!inst n base sz. _` drule >>
     simp[mk_inst_def]) >>
  drule_all compile_alloc_buffer_mem_ok >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `t = update_var (STRING #"%" (toString sa.cs_next_var)) (n2w p)
      (abi_builtin_allocate_state sa.cs_next_id 32 s)` by
    (gvs[run_inst_seq_def]) >>
  `p < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
     decide_tac) >>
  `p + 32 < dimword (:256)` by
    (gvs[update_var_def]) >>
  irule compile_keccak256_bytesm_mem_ok >>
  simp[] >>
  qexistsl_tac [`m`, `op`, `x`, `w`] >>
  gvs[] >>
  simp[compile_keccak256_bytesm_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def]
QED

Theorem keccak_fixed_suffix_frontier:
  compile_keccak256_bytesm x m sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  simp[compile_keccak256_bytesm_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!k. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + k) = 0`
    by decide_tac >>
  gvs[emitted_insts_def, DROP_APPEND] >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  `s.vs_alloca_next <= ss'.vs_alloca_next` by
    (irule venomMemPropsTheory.step_inst_alloca_next_mono >>
     qexistsl_tac [`ARB`, `0`,
       `mk_inst sa.cs_next_id ALLOCA [Lit 32w]
         [STRING #"%" (toString sa.cs_next_var)]`] >>
     simp[step_inst_non_invoke, mk_inst_def, is_terminator_def, is_ext_call_op_def]) >>
  `ss'.vs_alloca_next <= ss''.vs_alloca_next` by
    (irule step_inst_alloca_next_mono >>
     qexistsl_tac [`ARB`, `0`,
       `mk_inst (sa.cs_next_id + 1) MSTORE
         [Var (STRING #"%" (toString sa.cs_next_var)); x] []`] >>
     simp[step_inst_non_invoke, mk_inst_def, is_terminator_def, is_ext_call_op_def]) >>
  `ss''.vs_alloca_next <= t.vs_alloca_next` by
    (irule step_inst_alloca_next_mono >>
     qexistsl_tac [`ARB`, `0`,
       `mk_inst (sa.cs_next_id + 2) SHA3
         [Var (STRING #"%" (toString sa.cs_next_var)); Lit (n2w m)]
         [STRING #"%" (toString (sa.cs_next_var + 1))]`] >>
     simp[step_inst_non_invoke, mk_inst_def, is_terminator_def, is_ext_call_op_def]) >>
  decide_tac
QED

Theorem keccak_memory_suffix_mem_ok:
  compile_keccak256_bytes x sa = (op,sb) /\
  (!v. x = Var v ==> not_fresh_at sa v) /\
  eval_operand x s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w n /\
  b + 32 < dimword (:256) /\ n < dimword (:256) /\
  b + 32 <= s.vs_alloca_next /\
  (n = 0 \/ b + 32 + n <= s.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[compile_keccak256_bytes_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!k. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + k) = 0`
    by decide_tac >>
  qpat_x_assum `_ with <| cs_next_var := _; cs_next_id := _;
      cs_current_insts := _ |> = sb` (SUBST1_TAC o SYM) >>
  simp[emitted_insts_def, DROP_APPEND] >>
  rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- simp[below_frontier_MLOAD] >>
  drule step_MLOAD_local >>
  disch_then (qspecl_then [`STRING #"%" (toString sa.cs_next_var)`,
                          `sa.cs_next_id`] assume_tac) >>
  simp[] >>
  `eval_operand x (update_var (STRING #"%" (toString sa.cs_next_var))
      (mload b s) s) = SOME (n2w b)` by
    (irule eval_operand_update_other_local >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[not_fresh_at_def]) >>
  conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  drule step_ADD >>
  disch_then (qspec_then `Lit 32w` mp_tac) >>
  simp[eval_operand_def] >>
  disch_then (qspecl_then [`sa.cs_next_id + 1`,
    `STRING #"%" (toString (sa.cs_next_var + 1))`] assume_tac) >>
  simp[run_inst_seq_mem_ok_last, below_frontier_SHA3] >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, ASCIInumbersTheory.toString_inj,
       GSYM mem_word_at_eq_mload, GSYM word_add_n2w] >>
  Cases_on `n = 0` >> simp[] >>
  `n2w b + 32w = (n2w (b + 32):256 word)` by simp[word_add_n2w] >>
  simp[] >> decide_tac
QED

Theorem keccak_memory_suffix_frontier:
  compile_keccak256_bytes x sa = (op,sb) /\
  (!v. x = Var v ==> not_fresh_at sa v) /\
  eval_operand x s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >> drule_all compile_keccak256_bytes_run >>
  strip_tac >> gvs[] >>
  qpat_x_assum `_ with vs_vars := _ = _` mp_tac >>
  simp[venom_state_component_equality]
QED
