(* Account suffix edges start in the operand-final frame. *)
Theory bodyPtrEnvBuiltinsAccountSuffix
Ancestors
  bodyPtrEnvBuiltinsEdges bodyPtrEnvBuiltinsScalarCompose
  ptrDiscipline ptrSafeRun venomInst venomExecSemantics venomState
  compileEnv loweringStateRelDefs list memLocDefs venomInstProofs codegenRel contextCodegenRel
  fragGasPathPtr fragGasSeqPtr finite_map bodyPtrDefs emitHelper emitHelperProps
  exprLoweringProps fragExec stmtFragPtr
  bodyPtrEnvBuiltinsAccountReads bodyPtrEnvBuiltinsScalar
  valueEncoding vyperValue vyperContext vyperTypeSystem exprSimAccounts

Theorem ptr_inst_ok_account_gt:
  op_taint tn arg = {} /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id GT [arg; Lit lit] [out]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
       step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, update_var_def, AllCaseEqs()] >>
  rpt strip_tac >> Cases_on `op = arg` >> gvs[] >>
  Cases_on `op = Lit lit` >> gvs[op_taint_def]
QED

Theorem account_gt_counted_edge:
  op_taint tn arg = {} /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id GT [arg; Lit lit] [out]) /\
  step_inst_base (mk_inst id GT [arg; Lit lit] [out]) s = OK u ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id GT [arg; Lit lit] [out]) u)
    (step_taint (mk_inst id GT [arg; Lit lit] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id GT [arg; Lit lit] [out]) s` by
    (irule ptr_inst_ok_account_gt >> simp[]) >>
  drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def] >> disch_then irule >> gvs[mk_inst_def]
QED

Theorem account_gt_update_ghosts:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\ ~not_fresh_at sa out ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst id GT [arg; Lit lit] [out]) (update_var out w s))
    (step_taint (mk_inst id GT [arg; Lit lit] [out]) s (update_var out w s) tn)
    (update_var out w s) /\
  ghost_kept cenv es0 sa G0 tn0 s0
    (step_prov PG G (mk_inst id GT [arg; Lit lit] [out]) (update_var out w s))
    (step_taint (mk_inst id GT [arg; Lit lit] [out]) s (update_var out w s) tn)
Proof
  strip_tac >>
  `(step_taint (mk_inst id GT [arg; Lit lit] [out]) s (update_var out w s) tn).t_mem =
    tn.t_mem` by
    (irule step_taint_no_memory_effect >>
     simp[source_memory_write_ranges_def, mk_inst_def, update_var_def,
          written_taint_def]) >>
  conj_tac
  >- (irule single_output_ghost_inv >>
      simp[update_var_def] >> qexists_tac `sa` >>
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> IF_CASES_TAC >> gvs[]) >>
  irule single_output_ghost_kept >> simp[]
QED

Theorem account_gt_counted_suffix:
  op_taint tn arg = {} /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id GT [arg; Lit lit] [out]) /\
  step_inst_base (mk_inst id GT [arg; Lit lit] [out]) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id GT [arg; Lit lit] [out]) u)
    (step_taint (mk_inst id GT [arg; Lit lit] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst 0 ctx (mk_inst id GT [arg; Lit lit] [out]) s = OK u` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  `~u.vs_halted` by
    (drule_at (Pat `step_inst _ _ _ _ = _`) step_preserves_halted >>
     simp[mk_inst_def, is_terminator_def]) >>
  drule_all account_gt_counted_edge >>
  disch_then (qspecl_then [`PG`, `G`, `D`] assume_tac) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[Once gas_path_ptr_cases]
QED

Theorem emit_account_gt_counted_suffix:
  emit_op GT [arg; Lit lit] sa = (op,sb) /\ fn_has_code sa sb fn /\
  op_taint tn arg = {} /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id GT [arg; Lit lit]
    [STRING #"%" (toString sa.cs_next_var)]) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id GT [arg; Lit lit]
      [STRING #"%" (toString sa.cs_next_var)]) u)
    (step_taint (mk_inst sa.cs_next_id GT [arg; Lit lit]
      [STRING #"%" (toString sa.cs_next_var)]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  irule account_gt_counted_suffix >> simp[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem emit_account_gt_run:
  emit_op GT [arg; Lit lit] sa = (op,sb) /\ fn_has_code sa sb fn /\
  op_taint tn arg = {} /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\
  ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id GT [arg; Lit lit]
    [STRING #"%" (toString sa.cs_next_var)]) s =
      OK (update_var (STRING #"%" (toString sa.cs_next_var)) w s) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es0 sa G0 tn0 s0 G' tn' /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\ eval_operand op t = SOME w /\
    stmt_state_rel ctx fn cenv cx es t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  `~not_fresh_at sa (STRING #"%" (toString sa.cs_next_var))` by
    simp[not_fresh_at_def] >>
  drule_all emit_account_gt_counted_suffix >>
  disch_then (qspecl_then [`PG`, `G`, `D`] assume_tac) >>
  drule_all account_gt_update_ghosts >>
  disch_then (qspecl_then [`w`, `lit`, `sa.cs_next_id`, `arg`, `PG`] strip_assume_tac) >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx es
    (update_var (STRING #"%" (toString sa.cs_next_var)) w s)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[stmt_state_rel_inst_idx, update_var_def, eval_operand_def,
       lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (Cases_on `eval_operand arg s` >>
      simp[op_taint_def, step_taint_def, mk_inst_def, set_var_taint_def,
           out_taint_def, FLOOKUP_UPDATE]) >>
  conj_tac
  >- simp[op_prov_def, step_prov_def, set_prov_def, out_prov_def,
          mk_inst_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED

Theorem account_read_counted_run:
  MEM (item,opc) [(Balance,BALANCE); (Codesize,EXTCODESIZE); (Codehash,EXTCODEHASH)] /\
  emit_op opc [arg] sa = (op,sb) /\ fn_has_code sa sb fn /\
  LENGTH bs = 20 /\
  eval_operand arg s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  evaluate_type (get_tenv cx) (account_item_type item) = SOME tv /\
  op_taint tn arg = {} /\ local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\
  ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es0 sa G0 tn0 s0 G' tn' /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\
    eval_operand op t = SOME (typed_val_to_w256 tv
      (evaluate_account_op item bs
        (lookup_account (word_of_bytes_be bs) es.accounts))) /\
    stmt_state_rel ctx fn cenv cx es t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  `MEM opc [CALLER; ADDRESS; CALLVALUE; TIMESTAMP; NUMBER; BLOBBASEFEE;
    GASPRICE; BLOCKHASH; CHAINID; COINBASE; GASLIMIT; BASEFEE; PREVRANDAO;
    ORIGIN; GAS; CALLDATASIZE; BALANCE; EXTCODESIZE; EXTCODEHASH;
    BLOBHASH; ISZERO; SUB; ADD; SHR; SHL] /\ opc <> GAS` by gvs[] >>
  drule_all account_read_typed_step >>
  disch_then (qspecl_then [`STRING #"%" (toString sa.cs_next_var)`,
    `sa.cs_next_id`] assume_tac) >>
  `!a. MEM a [arg] ==> op_taint tn a = {}` by simp[] >>
  drule_all emit_scalar_builtin_run >> simp[] >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >> gvs[]
QED

Theorem emit_account_gt_append:
  emit_op GT [arg; Lit lit] sm = (op,sb) /\ fn_has_code sm sb fn /\
  op_taint tn arg = {} /\
  gas_path_ptr D 0 ctx fn PG G0 tn0 s0 k G tn (OK s) /\
  ghost_inv d cenv cx es G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  local_ptrs_rel fn cenv es.scopes s0 /\
  stmt_state_rel ctx fn cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x s0) /\
  s.vs_memory = s0.vs_memory /\ s.vs_allocas = s0.vs_allocas /\
  step_inst_base (mk_inst sm.cs_next_id GT [arg; Lit lit]
    [STRING #"%" (toString sm.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sm.cs_next_var)) w s) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G0 tn0 s0 k G' tn' (OK t) /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es sa G0 tn0 s0 G' tn' /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\ eval_operand op t = SOME w /\
    stmt_state_rel ctx fn cenv cx es t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
    t.vs_memory = s0.vs_memory /\ t.vs_allocas = s0.vs_allocas
Proof
  strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sm x` by metis_tac[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sm x` by metis_tac[] >>
  `ghost_kept cenv es sm G tn s G tn` by simp[ghost_kept_refl] >>
  drule_all emit_account_gt_run >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `ghost_kept cenv es sa G0 tn0 s0 G' tn'` by
    (drule_all scalar_frame_kept_trans >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G0 tn0 s0 (k + 0) G' tn' (OK t)` by
    (irule gas_path_ptr_then >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >> qexistsl_tac [`G'`, `tn'`, `t`] >> simp[] >>
  metis_tac[]
QED
