Theory externalReturnBoundaryPtr
Ancestors
  loweringHalt stmtLowering compileEnv emitHelper venomInst
  compileVyper entryStateRel bodySim bodyPtrDefs fragExecPtr fragExec stmtSim
  ptrSafeRun ptrDiscipline venomState venomExecSemantics contextCodegenRelProps
  abiBuiltinAllocation allocationPtr allocaFootprint finite_map words arithmetic list
  exprOperandVar exprLoweringProps stmtSimReturn context rich_list
  vyperInterpreter vyperExprNoControl vyperState exprSim
Libs
  monadsyntax

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

Theorem external_return_word_stmt_frag_ptr:
  !cenv nr nkey ut iv ret_ty d ctx PG func cx e es res es' lctx.
    cenv.ce_return_pc = NONE /\ cenv.ce_raw_return = F /\
    cenv.ce_nonreentrant = (nr,nkey,ut,iv) /\ (nr ==> iv) /\
    is_word_type ret_ty /\
    expr_sim_ptr d ctx PG func cenv cx ret_ty e es /\
    eval_stmt cx (Return (SOME e)) es = (res,es') ==>
    stmt_frag_ptr d ctx PG func cx lctx (\v es gt r. T) cenv
      (stmt_env cenv lctx ret_ty (Return (SOME e))) es res es'
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_ptr_def] >>
  rpt gen_tac >> strip_tac >> disj2_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `lower_value compile_expr cenv ret_ty e sa` >>
  rename1 `_ = (op,sm)` >> simp[] >> strip_tac >> gvs[] >>
  Cases_on `compile_external_return (SOME op) T F cenv.ce_ret_enc_info
    cenv.ce_max_return_size nr nkey ut iv sm` >>
  rename1 `_ = (u,sb')` >> gvs[] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `cs_extends sm sb` by
    (qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_external_return_def, optional_unlock_view,
          compile_alloc_buffer_def, emit_op_def, emit_void_def, emit_inst_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
          fresh_var_def, emit_def] >>
     strip_tac >> gvs[cs_extends_def, IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `eval_stmt cx (Return (SOME e)) es =
     bind (do raw <- eval_expr cx e; read_result cx raw od)
       (\v. raise (ReturnException v)) es` by
    (simp[NoAsms, Once evaluate_def, bind_def] >>
     Cases_on `eval_expr cx e es` >> rename1 `_ = (raw,est)` >>
     Cases_on `raw` >> simp[]) >>
  qpat_x_assum `eval_stmt _ _ _ = (res,es')` mp_tac >>
  asm_rewrite_tac[] >>
  Cases_on `(do raw <- eval_expr cx e; read_result cx raw od) es` >>
  rename1 `_ = (r1,es1)` >> simp[Once bind_def, raise_def] >> strip_tac >>
  `expr_res_ok r1` by
    (Cases_on `r1` >- gvs[expr_res_ok_def] >>
     qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
     simp[bind_def] >> Cases_on `eval_expr cx e es` >>
     rename1 `_ = (raw,est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
     imp_res_tac read_result_no_control >>
     imp_res_tac (cj 1 eval_expr_no_control) >>
     gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]) >>
  `r1 <> INR (Error (RuntimeError "convert empty bytes to signed"))` by
    (Cases_on `r1` >> gvs[]) >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`,`sm`,`op`,`r1`,`es1`,`s0`,`G0`,`tn0`] mp_tac) >>
  impl_tac >- simp[] >>
  simp[frag_exec_ptr_def] >>
  disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (gvs[expr_post_def, ptr_val_ok_def, expr_val_rel_def] >>
      `!y. op = Var y ==> not_fresh_at sm y` by
        metis_tac[compile_lower_value_var] >>
      `stor_taint_ok cx tn' s''` by gvs[ghost_inv_def] >>
      drule_all compile_external_return_word_state_rel_run_ptr >>
      disch_then (qspecl_then [`PG`,`G'`,`0`] strip_assume_tac) >>
      qpat_x_assum `!fuel. (!e. run_from fuel ctx func s'' <> Error e) ==> _`
        (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
      qexists `fuel'` >> simp[exit_result_def, stmt_exit_ptr_def]) >>
  qexists `fuel` >> Cases_on `r1` >> gvs[stmt_exit_ptr_def] >>
  disj1_tac >> metis_tac[expr_exit_INR_type]
QED

Theorem compile_external_return_copy_state_rel_run_ptr:
  compile_external_return (SOME (Var src)) F F (AbiCopy m) m
    nr nkey ut iv sa = (x,sb) /\
  (nr ==> iv) /\ not_fresh_at sa src /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s /\
  ptr_covers G tn src s m /\
  (!i. w2n w <= i /\ i < w2n w + m ==> i NOTIN tn.t_mem) /\
  stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx /\
  expr_val_at cenv cx ty ea eb es v (Var src) s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand (Var src) s = SOME w /\ m <= val_footprint tv v ==>
  !fuel. ptr_safe_run (cx_dead cx) 0 fuel ctx func PG G tn s
Proof
  strip_tac >>
  drule_all compile_external_return_copy_parts >> strip_tac >>
  `src <> buf` by metis_tac[] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id ALLOCA [Lit (n2w m)] [buf]) /\
   get_instruction bb (s.vs_inst_idx+1) =
     SOME (mk_inst (sa.cs_next_id+1) MCOPY [Var buf;Var src;Lit (n2w m)] []) /\
   get_instruction bb (s.vs_inst_idx+2) =
     SOME (mk_inst (sa.cs_next_id+2) RETURN [Var buf;Lit (n2w m)] [])` by
    (qpat_x_assum `!i. _` (fn th =>
       map_every (fn j => mp_tac (Q.SPEC j th)) [`0`,`1`,`2`]) >> simp[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w m)] [buf]) (fn_insts func)` by
    (irule lookup_block_fn_insts >> qexistsl [`bb`,`sa.cs_current_bb`] >>
     simp[] >> gvs[get_instruction_def] >>
     `LENGTH sa.cs_current_insts < LENGTH bb.bb_instructions` by decide_tac >>
     metis_tac[EL_MEM]) >>
  qabbrev_tac `n = w2n (n2w m : 256 word)` >>
  `n < dimword (:256) /\ n <= m /\ (n2w n : 256 word) = n2w m` by
    simp[Abbr `n`, w2n_n2w, MOD_LESS_EQ] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [buf]) (fn_insts func)` by
    metis_tac[] >>
  qpat_x_assum `MEM (mk_inst _ ALLOCA [Lit (n2w m)] _) _` kall_tac >>
  `?base. FLOOKUP (abi_builtin_allocate_state sa.cs_next_id n s).vs_allocas
      sa.cs_next_id = SOME (base,n) /\ base < dimword (:256)` by
    (Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
     >- (drule_all stmt_state_rel_alloca_fresh_bound >> strip_tac >>
         qexists `s.vs_alloca_next` >>
         simp[abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >> decide_tac) >>
     rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME slot` >>
     PairCases_on `slot` >>
     drule_all stmt_state_rel_alloca_site_bound >> strip_tac >>
     qexists `slot0` >> simp[abi_builtin_allocate_state_def] >> decide_tac) >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [buf]` >>
  qabbrev_tac `t = update_var buf (n2w base)
    (abi_builtin_allocate_state sa.cs_next_id n s)` >>
  `step_inst_base inst s = OK t` by
    (simp[NoAsms, Abbr `inst`, Abbr `t`] >>
     irule step_alloca_site >> simp[]) >>
  qunabbrev_tac `inst` >>
  drule_all alloca_step_ptr_covers >>
  disch_then (qspecl_then [`PG`,`G`,`tn`] assume_tac) >>
  drule_all alloca_step_old_ptr_covers >>
  disch_then (qspec_then `PG` assume_tac) >>
  drule_all alloca_step_stor_taint_ok >> strip_tac >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [buf]` >>
  qabbrev_tac `G1 = step_prov PG G inst t` >>
  qabbrev_tac `tn1 = step_taint inst s t tn` >>
  `!i. w2n w <= i /\ i < w2n w + n ==> i NOTIN tn1.t_mem` by
    (rpt strip_tac >>
     `i < w2n w + val_footprint tv v /\ i NOTIN tn.t_mem` by
       (conj_tac >- decide_tac >> first_x_assum irule >> decide_tac) >>
     qunabbrev_tac `tn1` >> qunabbrev_tac `inst` >>
     drule_all alloca_step_expr_read_clean >> simp[]) >>
  `t.vs_current_bb = s.vs_current_bb /\ lookup_var src t = SOME w` by
    (Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id = NONE` >>
     gvs[Abbr `t`, update_var_def, abi_builtin_allocate_state_def,
         eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  qabbrev_tac `s1 = t with vs_inst_idx := s.vs_inst_idx + 1` >>
  `ptr_covers G1 tn1 buf s1 n /\ ptr_covers G1 tn1 src s1 n /\
   stor_taint_ok cx tn1 s1` by
    (simp[Abbr `s1`, ptr_covers_def, stor_taint_ok_def, lookup_var_def] >>
     gvs[ptr_covers_def, stor_taint_ok_def, lookup_var_def] >>
     metis_tac[LESS_EQ_TRANS]) >>
  gen_tac >>
  `ptr_safe_run (cx_dead cx) 0 fuel ctx func PG G1 tn1 s1` by
    (irule ptr_safe_run_copy_return >> simp[] >>
     qexistsl [`bb`,`buf`,`sa.cs_next_id+1`,`n2w m`,`src`] >>
     simp[Abbr `s1`, GSYM ADD_ASSOC] >>
     gvs[Abbr `n`, lookup_var_def]) >>
  `step_inst fuel ctx inst s = OK t` by
    simp[Abbr `inst`, step_inst_non_invoke] >>
  `ptr_inst_ok (cx_dead cx) 0 fuel ctx func G tn inst s` by
    (simp[Abbr `inst`] >> irule ptr_inst_ok_alloca >> simp[]) >>
  qunabbrev_tac `inst` >> gvs[mk_inst_def] >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def, ptr_safe_step_def,
       is_terminator_def, ghost_step_def, ADD1] >>
  gvs[ptr_safe_run_def, Abbr `n`, Abbr `s1`, Abbr `G1`, Abbr `tn1`, n2w_mod]
QED
