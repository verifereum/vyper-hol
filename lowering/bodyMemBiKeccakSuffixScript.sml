(* Memory checks for the fixed-bytes keccak scratch sequence. *)
Theory bodyMemBiKeccakSuffix
Ancestors
  exprSimHash exprSimAlloc exprSimDefs allocaFootprint bodyAllocMemory
  builtinHashing emitHelper emitHelperProps exprLoweringProps fragExecMem
  instMemFrontier compileEnv context venomState venomInst venomExecSemantics
  abiBuiltinAllocation venomMemDefs venomMemProps words list finite_map
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
  rpt strip_tac >>
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
