(* Ghost preservation boundaries for counted builtin instruction suffixes. *)
Theory bodyPtrEnvBuiltinsEdges
Ancestors
  bodyPtrDefs fragGasSeqPtr gasSummaryComposePtr ptrDiscipline ptrSafeRun
  venomState venomInst venomExecSemantics compileEnv loweringStateRelDefs finite_map pred_set
  list memLocDefs codegenRel contextCodegenRel decoderGhostFramePtr
  fragGasPathPtr ghostPcTransportPtr venomInstProofs emitHelperProps
  exprLoweringProps emitHelper fragExec rich_list

Theorem ghost_kept_refl:
  ghost_kept cenv es sa G tn s G tn
Proof
  simp[ghost_kept_def]
QED

Theorem ghost_kept_clean_suffix:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa x ==>
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem SUBSET tn.t_mem ==>
  ghost_kept cenv es sa G0 tn0 s0 G' tn'
Proof
  rw[ghost_kept_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ghost_inv_register_transport:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  tn'.t_imm = tn.t_imm ==>
  ghost_inv d cenv cx es G' tn' t
Proof
  simp[ghost_inv_def, local_ptrs_reserved_def, stor_taint_ok_def] >>
  rpt strip_tac
  >- (gvs[ptr_covers_def] >> metis_tac[])
  >- metis_tac[]
  >- (Cases_on `d` >- gvs[return_buf_ptr_def] >>
      PairCases_on `x` >> gvs[return_buf_ptr_def, ptr_covers_def] >>
      metis_tac[])
  >> metis_tac[]
QED

Theorem ptr_inst_ok_scalar_builtin:
  MEM opc [CALLER; ADDRESS; CALLVALUE; TIMESTAMP; NUMBER; BLOBBASEFEE;
    GASPRICE; BLOCKHASH; CHAINID; COINBASE; GASLIMIT; BASEFEE; PREVRANDAO;
    ORIGIN; GAS; CALLDATASIZE; BALANCE; EXTCODESIZE; EXTCODEHASH;
    BLOBHASH; ISZERO; SUB; ADD; SHR; SHL] /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops [out]) s
Proof
  strip_tac >>
  gvs[MEM] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
       step_inst_non_invoke] >>
  simp[step_inst_base_opcode_eqs] >>
  simp[exec_read0_def, exec_read1_def, exec_pure1_def, exec_pure2_def,
       exec_gas_def, update_var_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem scalar_builtin_counted_edge:
  MEM opc [CALLER; ADDRESS; CALLVALUE; TIMESTAMP; NUMBER; BLOBBASEFEE;
    GASPRICE; BLOCKHASH; CHAINID; COINBASE; GASLIMIT; BASEFEE; PREVRANDAO;
    ORIGIN; GAS; CALLDATASIZE; BALANCE; EXTCODESIZE; EXTCODEHASH;
    BLOBHASH; ISZERO; SUB; ADD; SHR; SHL] /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) /\
  step_inst_base (mk_inst id opc ops [out]) s = OK u ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s
    (if opc = GAS then 1 else 0)
    (step_prov PG G (mk_inst id opc ops [out]) u)
    (step_taint (mk_inst id opc ops [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops [out]) s` by
    (irule ptr_inst_ok_scalar_builtin >> simp[]) >>
  `opc <> INVOKE /\ ~is_terminator opc` by
    (gvs[MEM] >> simp[is_terminator_def]) >>
  drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
  simp[mk_inst_def] >> disch_then irule >> gvs[mk_inst_def]
QED

Theorem scalar_builtin_out_taint:
  MEM opc [CALLER; ADDRESS; CALLVALUE; TIMESTAMP; NUMBER; BLOBBASEFEE;
    GASPRICE; BLOCKHASH; CHAINID; COINBASE; GASLIMIT; BASEFEE; PREVRANDAO;
    ORIGIN; GAS; CALLDATASIZE; BALANCE; EXTCODESIZE; EXTCODEHASH;
    BLOBHASH; ISZERO; SUB; ADD; SHR; SHL] /\
  (!op. MEM op ops ==> op_taint tn op = {}) ==>
  out_taint tn (mk_inst id opc ops outs) s = {}
Proof
  strip_tac >> gvs[MEM] >>
  (namedCases_on `ops` ["", "a rest"]
  >- simp[out_taint_def, mk_inst_def] >>
  namedCases_on `rest` ["", "b more"]
  >- (Cases_on `eval_operand a s` >> gvs[out_taint_def, mk_inst_def]) >>
  namedCases_on `more` ["", "c tail"]
  >- (Cases_on `eval_operand a s` >>
      gvs[out_taint_def, mk_inst_def, shift_taint_def, EXTENSION]) >>
  Cases_on `tail` >> simp[out_taint_def, mk_inst_def])
QED

Theorem scalar_builtin_output_clean:
  MEM opc [CALLER; ADDRESS; CALLVALUE; TIMESTAMP; NUMBER; BLOBBASEFEE;
    GASPRICE; BLOCKHASH; CHAINID; COINBASE; GASLIMIT; BASEFEE; PREVRANDAO;
    ORIGIN; GAS; CALLDATASIZE; BALANCE; EXTCODESIZE; EXTCODEHASH;
    BLOBHASH; ISZERO; SUB; ADD; SHR; SHL] /\
  (!op. MEM op ops ==> op_taint tn op = {}) ==>
  op_taint (step_taint (mk_inst id opc ops [out]) s t tn) (Var out) = {}
Proof
  strip_tac >> drule_all scalar_builtin_out_taint >> strip_tac >>
  simp[op_taint_def, step_taint_def, mk_inst_def, set_var_taint_def,
       FLOOKUP_UPDATE]
QED

Theorem scalar_builtin_output_no_prov:
  MEM opc [CALLER; ADDRESS; CALLVALUE; TIMESTAMP; NUMBER; BLOBBASEFEE;
    GASPRICE; BLOCKHASH; CHAINID; COINBASE; GASLIMIT; BASEFEE; PREVRANDAO;
    ORIGIN; GAS; CALLDATASIZE; BALANCE; EXTCODESIZE; EXTCODEHASH;
    BLOBHASH; ISZERO; SHR; SHL] ==>
  op_prov (step_prov PG G (mk_inst id opc ops [out]) t) (Var out) = NONE
Proof
  simp[MEM] >> strip_tac >>
  gvs[op_prov_def, step_prov_def, set_prov_def, out_prov_def,
      mk_inst_def, FLOOKUP_DRESTRICT]
QED

Theorem step_taint_no_memory_effect:
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  source_memory_write_ranges inst s = [] /\ written_taint tn inst s = {} ==>
  (step_taint inst s t tn).t_mem = tn.t_mem
Proof
  simp[step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
       range_bytes_def, FLOOKUP_DEF, EXTENSION] >> metis_tac[]
QED

Theorem single_output_ghost_kept:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  ~not_fresh_at sa out /\
  (step_taint (mk_inst id opc ops [out]) s t tn).t_mem SUBSET tn.t_mem ==>
  ghost_kept cenv es sa G0 tn0 s0
    (step_prov PG G (mk_inst id opc ops [out]) t)
    (step_taint (mk_inst id opc ops [out]) s t tn)
Proof
  strip_tac >> irule ghost_kept_clean_suffix >>
  qexistsl_tac [`G`, `tn`] >> simp[] >> rpt strip_tac >>
  `x <> out` by metis_tac[] >>
  simp[step_prov_other_output, step_taint_other_output, mk_inst_def]
QED

Theorem single_output_ghost_inv:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  ~not_fresh_at sa out /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  t.vs_memory = s.vs_memory /\
  (step_taint (mk_inst id opc ops [out]) s t tn).t_mem = tn.t_mem /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\
  opc <> CALL /\ opc <> SSTORE /\ opc <> TSTORE /\ opc <> ISTORE ==>
  ghost_inv d cenv cx es (step_prov PG G (mk_inst id opc ops [out]) t)
    (step_taint (mk_inst id opc ops [out]) s t tn) t
Proof
  strip_tac >> irule ghost_inv_register_transport >>
  qexistsl_tac [`G`, `s`, `sa`, `tn`] >> simp[] >>
  `((step_taint (mk_inst id opc ops [out]) s t tn).t_stor = tn.t_stor) /\
   ((step_taint (mk_inst id opc ops [out]) s t tn).t_trans = tn.t_trans) /\
   ((step_taint (mk_inst id opc ops [out]) s t tn).t_imm = tn.t_imm)` by
    (irule step_taint_nonmemory_frame >> simp[mk_inst_def]) >>
  simp[] >> rpt strip_tac >>
  `x <> out` by metis_tac[] >>
  simp[step_prov_other_output, step_taint_other_output, mk_inst_def]
QED

Theorem scalar_builtin_update_ghosts:
  MEM opc [CALLER; ADDRESS; CALLVALUE; TIMESTAMP; NUMBER; BLOBBASEFEE;
    GASPRICE; BLOCKHASH; CHAINID; COINBASE; GASLIMIT; BASEFEE; PREVRANDAO;
    ORIGIN; GAS; CALLDATASIZE; BALANCE; EXTCODESIZE; EXTCODEHASH;
    BLOBHASH; ISZERO; SUB; ADD; SHR; SHL] /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  ~not_fresh_at sa out ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst id opc ops [out]) (update_var out w s))
    (step_taint (mk_inst id opc ops [out]) s (update_var out w s) tn)
    (update_var out w s) /\
  ghost_kept cenv es0 sa G0 tn0 s0
    (step_prov PG G (mk_inst id opc ops [out]) (update_var out w s))
    (step_taint (mk_inst id opc ops [out]) s (update_var out w s) tn)
Proof
  strip_tac >>
  `(step_taint (mk_inst id opc ops [out]) s (update_var out w s) tn).t_mem =
   tn.t_mem` by
    (irule step_taint_no_memory_effect >>
     gvs[MEM, source_memory_write_ranges_def, mk_inst_def,
         update_var_def, written_taint_def] >>
     Cases_on `ops` >> simp[] >> Cases_on `t` >> simp[] >>
     Cases_on `t'` >> simp[] >> Cases_on `t` >> simp[]) >>
  `opc <> CALL /\ opc <> ISTORE /\ opc <> SSTORE /\ opc <> TSTORE` by
    gvs[MEM] >>
  conj_tac
  >- (irule single_output_ghost_inv >>
      simp[update_var_def] >>
      qexists_tac `sa` >> simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> IF_CASES_TAC >> gvs[]) >>
  irule single_output_ghost_kept >> simp[]
QED

Theorem scalar_builtin_counted_suffix:
  MEM opc [CALLER; ADDRESS; CALLVALUE; TIMESTAMP; NUMBER; BLOBBASEFEE;
    GASPRICE; BLOCKHASH; CHAINID; COINBASE; GASLIMIT; BASEFEE; PREVRANDAO;
    ORIGIN; GAS; CALLDATASIZE; BALANCE; EXTCODESIZE; EXTCODEHASH;
    BLOBHASH; ISZERO; SUB; ADD; SHR; SHL] /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) /\
  step_inst_base (mk_inst id opc ops [out]) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s
    (if opc = GAS then 1 else 0)
    (step_prov PG G (mk_inst id opc ops [out]) u)
    (step_taint (mk_inst id opc ops [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `opc <> INVOKE /\ ~is_terminator opc` by
    (gvs[MEM] >> simp[is_terminator_def]) >>
  `step_inst 0 ctx (mk_inst id opc ops [out]) s = OK u` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  `~u.vs_halted` by
    (drule_at (Pat `step_inst _ _ _ _ = _`) step_preserves_halted >>
     simp[mk_inst_def]) >>
  drule_all scalar_builtin_counted_edge >>
  disch_then (qspecl_then [`PG`, `G`, `D`] assume_tac) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[Once gas_path_ptr_cases]
QED

Theorem scalar_builtin_outcome_prefix:
  MEM opc [CALLER; ADDRESS; CALLVALUE; TIMESTAMP; NUMBER; BLOBBASEFEE;
    GASPRICE; BLOCKHASH; CHAINID; COINBASE; GASLIMIT; BASEFEE; PREVRANDAO;
    ORIGIN; GAS; CALLDATASIZE; BALANCE; EXTCODESIZE; EXTCODEHASH;
    BLOBHASH; ISZERO; SUB; ADD; SHR; SHL] /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) /\
  step_inst_base (mk_inst id opc ops [out]) s = OK u /\
  gas_outcome_ptr D tops (ctx, fn) PG source
    (es, u with vs_inst_idx := SUC s.vs_inst_idx,
     step_prov PG G (mk_inst id opc ops [out]) u,
     step_taint (mk_inst id opc ops [out]) s u tn) Q R ==>
  gas_outcome_ptr D tops (ctx, fn) PG source (es, s, G, tn) Q R
Proof
  strip_tac >> drule_all scalar_builtin_counted_suffix >> strip_tac >>
  irule gas_outcome_ptr_prefix >> goal_assum (drule_at Any) >>
  qexists_tac `if opc = GAS then 1 else 0` >> simp[]
QED

Theorem emit_scalar_builtin_counted_suffix:
  emit_op opc args sa = (op, sb) /\ fn_has_code sa sb fn /\
  MEM opc [CALLER; ADDRESS; CALLVALUE; TIMESTAMP; NUMBER; BLOBBASEFEE;
    GASPRICE; BLOCKHASH; CHAINID; COINBASE; GASLIMIT; BASEFEE; PREVRANDAO;
    ORIGIN; GAS; CALLDATASIZE; BALANCE; EXTCODESIZE; EXTCODEHASH;
    BLOBHASH; ISZERO; SUB; ADD; SHR; SHL] /\
  (!a. MEM a args ==> op_taint tn a = {}) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id opc args
    [STRING #"%" (toString sa.cs_next_var)]) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s (if opc = GAS then 1 else 0)
    (step_prov PG G (mk_inst sa.cs_next_id opc args
      [STRING #"%" (toString sa.cs_next_var)]) u)
    (step_taint (mk_inst sa.cs_next_id opc args
      [STRING #"%" (toString sa.cs_next_var)]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  irule scalar_builtin_counted_suffix >> simp[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED
