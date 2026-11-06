Theory externalReturnBoundaryPtr
Ancestors
  loweringHalt stmtLowering compileEnv emitHelper venomInst
  compileVyper entryStateRel bodySim bodyPtrDefs fragExecPtr fragExec stmtSim
  ptrSafeRun ptrDiscipline venomState venomExecSemantics contextCodegenRelProps
  abiBuiltinAllocation allocationPtr finite_map words arithmetic list
  exprOperandVar exprLoweringProps stmtSimReturn

val _ = Parse.hide "body";
val _ = Parse.hide "base";

Theorem compile_return_none_external_code:
  compile_stmt cenv lctx ty (Return NONE) st = (x,st') /\
  cenv.ce_return_pc = NONE /\ cenv.ce_ctor_exit_label = NONE /\
  cenv.ce_nonreentrant = (nr,nkey,ut,iv) /\ (nr ==> iv) ==>
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts ++
    [mk_inst st.cs_next_id STOP [] []]
Proof
  strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[compile_stmt_def, optional_unlock_view, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emit_inst_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[]
QED

Theorem external_registered_no_ctor_exit:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,ret,body)) =
    (lbl,cenv0,pos,cds,payable,nr',key,ut,view,body',rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv,sa) ==>
  cenv.ce_ctor_exit_label = NONE
Proof
  strip_tac >>
  drule compile_register_positional_args_cenv >> strip_tac >> gvs[] >>
  qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
  simp[package_external_fn_def, set_external_package_target_def] >>
  Cases_on `ret = NoneT` >>
  simp[update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `cenv = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem external_return_none_stmt_frag_ptr:
  cenv.ce_return_pc = NONE /\ cenv.ce_ctor_exit_label = NONE /\
  cenv.ce_nonreentrant = (nr,nkey,ut,iv) /\ (nr ==> iv) /\
  eval_stmt cx (Return NONE) es = (INR (ReturnException v),es') ==>
  stmt_frag_ptr d ctx PG func cx lctx (\v es gt r. T) cenv
    (stmt_env cenv lctx ret_ty (Return NONE)) es
    (INR (ReturnException v)) es'
Proof
  strip_tac >> simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule_all compile_return_none_external_code >> strip_tac >>
  disj2_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s0.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id STOP [] [])` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `run_from 0 ctx func s0 = Halt (halt_state (s0 with vs_returndata := []))` by
    (irule run_from_halt >>
     qexistsl [`bb`, `mk_inst sa.cs_next_id STOP [] []`] >>
     simp[mk_inst_def, step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[mk_inst_def]) >>
  qexists `0` >> simp[exit_result_def, stmt_exit_ptr_def] >>
  irule ptr_safe_run_stop >> simp[] >>
  conj_tac >- (qexists `sa.cs_next_id` >> gvs[]) >>
  gvs[ghost_inv_def]
QED

Theorem compile_external_return_word_run_ptr:
  compile_external_return (SOME op) T F ei msz nr nkey ut iv sa = (x,sb) /\
  (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at sa y) /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand op s = SOME w /\ op_taint tn op = {} /\
  stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas
    sa.cs_next_id = SOME (base,32) /\ base < dimword (:256) ==>
  !fuel. ptr_safe_run (cx_dead cx) 0 fuel ctx func PG G tn s /\
    ?ss. run_from fuel ctx func s = Halt ss /\
      ss.vs_returndata = word_to_bytes w T /\
      ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
      ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
      ss.vs_pending_deletions = s.vs_pending_deletions
Proof
  strip_tac >>
  drule_all compile_external_return_word_parts >> strip_tac >>
  `op <> Var buf` by metis_tac[] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [buf]) /\
   get_instruction bb (s.vs_inst_idx+1) =
     SOME (mk_inst (sa.cs_next_id+1) MSTORE [Var buf;op] []) /\
   get_instruction bb (s.vs_inst_idx+2) =
     SOME (mk_inst (sa.cs_next_id+2) RETURN [Var buf;Lit 32w] [])` by
    (qpat_x_assum `!i. _` (fn th =>
       map_every (fn j => mp_tac (Q.SPEC j th)) [`0`,`1`,`2`]) >> simp[]) >>
  gen_tac >> conj_tac
  >- (irule ptr_safe_run_return_word >> simp[] >>
      qexistsl [`base`,`buf`,`sa.cs_next_id`,`op`,`w`] >> gvs[]) >>
  irule return_word_run >> simp[] >>
  qexistsl [`buf`,`sa.cs_next_id`,`op`] >> gvs[]
QED

Theorem compile_external_return_word_state_rel_run_ptr:
  compile_external_return (SOME op) T F ei msz nr nkey ut iv sa = (x,sb) /\
  (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at sa y) /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand op s = SOME w /\ op_taint tn op = {} /\
  stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx /\
  stmt_state_rel ctx func cenv cx es s ==>
  !fuel. ptr_safe_run (cx_dead cx) 0 fuel ctx func PG G tn s /\
    ?ss. run_from fuel ctx func s = Halt ss /\
      ss.vs_returndata = word_to_bytes w T /\
      ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
      ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
      ss.vs_pending_deletions = s.vs_pending_deletions
Proof
  strip_tac >>
  drule_all compile_external_return_word_parts >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w 32)] [buf]) (fn_insts func)` by
    (irule lookup_block_fn_insts >> qexistsl [`bb`,`sa.cs_current_bb`] >>
     simp[] >> gvs[get_instruction_def] >>
     qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[] >>
     strip_tac >> metis_tac[EL_MEM]) >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  `?base. FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas
      sa.cs_next_id = SOME (base,32) /\ base < dimword (:256)` by
    (Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
     >- (drule_all stmt_state_rel_alloca_fresh_bound >> strip_tac >>
         qexists `s.vs_alloca_next` >>
         simp[abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >> decide_tac) >>
     rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME slot` >>
     PairCases_on `slot` >>
     drule_all stmt_state_rel_alloca_site_bound >> strip_tac >>
     qexists `slot0` >> simp[abi_builtin_allocate_state_def] >> decide_tac) >>
  drule_all compile_external_return_word_run_ptr >> simp[]
QED
