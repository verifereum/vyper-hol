(* Selected pre-dispatch visits of the minimal proxy. No dispatch is run. *)
Theory entryCreateProxyVisitWalk
Ancestors
  entryCreateAdminSequence entryCreateFocusSpec entryCreateBodyCut
  createExprSizeExitDefs createSizeCutCode createSizeItinerary createSizeDispatch
  bodyFullCreateHeld createSizeCopyReplay exprSimFullBundleProps exprBodyPreProps
  vyperStorageTrace vyperStorageFootprint s1PrefixDefs emitHelperProps
  gasShadowCompile gasShadowState builtinCreate context
  vyperLocalAccessFrame vyperInterpreter vyperCreate vyperState
  fragGasOriginPtr fragExec venomInst list emitHelper compileEnv exprLoweringProps
  exprSimHypsDefs gasExplicitSites bodyInvCodeProps exprLowering
  exprSimSend vyperAST gasShadow externalEntryShape loweringShapeDefs
  bodyFullPreds exprSimSource

Overload proxy_entry[local] = ``\DF lo d ctx fn ce cx st0 a es s G tn.
  local_ptrs_reserved ce a /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  return_buf_frame d ce a s /\ alloca_history fn s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx fn s f i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx fn ce cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G tn s) /\
  ~s.vs_halted /\ create_operand_at a s``

Overload proxy_child[local] = ``\tops ctx shctx ce cx env DF lo d PG fn shfn st0 e a m sha shm op es s G tn.
  expr_body_pre ce cx env e es /\ body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx (expr_type e) e es
    (st0,a,m,sha,shm,op,s,G,tn) ==>
  expr_sim_scoped (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx (expr_type e) e es /\
  create_operand_cut a m (gas_explicit_sites ctx shctx) ctx fn tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s)``

Overload proxy_row[local] = ``\DF lo d ctx shctx PG fn ce cx st0 e a m op es s G0 tn0 marks v mid G tn t.
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,fn,PG)
      (s,G0,tn0) marks (OK t,G,tn) /\
    expr_sim_full_post (DF,lo,d,ctx,fn) ce cx e (es,a,m,s,op,G0,tn0)
      H (INL v : value + exception) (mid with gas_obs := []) G tn t)``

Overload proxy_scalar_law[local] = ``\tops ctx shctx ce cx env DF lo d PG fn shfn st0.
  !e a m b sha shm op es s G0 tn0 (next:value -> evaluation_state -> (eval_result + exception) # evaluation_state).
    body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    proxy_entry DF lo d ctx fn ce cx st0 a es s G0 tn0 /\
    (!H. dead_lo_ok H (DF H) lo ce cx) /\
    lower_value compile_expr ce (expr_type e) e a = (op,m) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (op,shm) /\
    expr_sim_full_code (ctx,shctx,fn,shfn) (a,m,sha,shm) /\
    create_cut_code {} a m /\ create_cut_code {} m b /\ fn_has_code m b fn /\
    (expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx (expr_type e) e es
       (st0,a,m,sha,shm,op,s,G0,tn0) ==>
     expr_sim_scoped (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx (expr_type e) e es /\
     create_operand_cut a m (gas_explicit_sites ctx shctx) ctx fn tops cx st0
       (bind (eval_expr cx e) (read_result cx)) (es,s)) /\
    (!v. storage_trace_frame (next v)) /\
    (!H0 marks v mid G tn t.
       valid_horizon cx st0 H0 mid.storage_trace /\
       expr_sim_inv ce cx env (mid with gas_obs := []) /\
       body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := []) /\
       expr_result_typed env e (Value v) /\
       proxy_entry DF lo d ctx fn ce cx st0 m (mid with gas_obs := []) t G tn /\
       proxy_row DF lo d ctx shctx PG fn ce cx st0 e a m op es s G0 tn0 marks v mid G tn t ==>
       create_operand_cut m b (gas_explicit_sites ctx shctx) ctx fn tops cx st0
         (next v) (mid with gas_obs := [],t)) ==>
    create_operand_cut a b (gas_explicit_sites ctx shctx) ctx fn tops cx st0
      (bind (bind (eval_expr cx e) (read_result cx)) next) (es,s)``

Overload proxy_admin_band[local] = ``\b c.
  c.cs_current_bb = b.cs_current_bb /\
  c.cs_current_insts = b.cs_current_insts ++ emitted_insts b c /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts b c)``

Theorem proxy_buffer_admin_band[local]:
  compile_create_proxy_buf x b = (buf,c) ==> proxy_admin_band b c
Proof
  simp_tac (srw_ss()) [compile_create_proxy_buf_def, compile_alloc_buffer_def,
    emit_op_def, emit_void_def, emit_inst_def, fresh_var_def, fresh_id_def,
    emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM,
    pairTheory.UNCURRY] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND,
       mk_inst_def, is_terminator_def]
QED

Overload proxy_neutral_law[local] = ``\tops ctx ce cx fn E st0.
  !a m b s u es (source:evaluation_state -> (eval_result + exception) # evaluation_state).
    body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
    create_cut_code {} a m /\ fn_has_code a m fn /\
    create_cut_code {} m b /\ fn_has_code m b fn /\
    proxy_admin_band a m /\ create_operand_at a s /\ ~s.vs_halted /\
    (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    create_operand_full_scope a m E ctx fn s [] (OK u) /\
    create_operand_cut m b E ctx fn tops cx st0 source (es,u) ==>
    create_operand_cut a b E ctx fn tops cx st0 source (es,s)``

(* Inputs describe the same two normal returns as the scalar callbacks.
   The adapter, not this walk, supplies the physical buffer observation. *)
Overload proxy_window_law[local] = ``\tops ctx shctx ce cx env DF lo d PG fn st0.
  !target amount sa a b c x y buf es s G0 tn0.
    expr_type target = BaseT AddressT /\ expr_type amount = BaseT (UintT 256) /\
    expr_body_pre ce cx env target es /\
    lower_value compile_expr ce (expr_type target) target sa = (x,a) /\
    lower_value compile_expr ce (expr_type amount) amount a = (y,b) /\
    compile_create_proxy_buf x b = (buf,c) /\ fn_has_code b c fn /\
    ci_mono sa a /\ ci_mono a b /\ ci_mono b c /\
    proxy_entry DF lo d ctx fn ce cx st0 sa es s G0 tn0 ==>
    !target_marks tv et Gt tnt st amount_marks av ea Ga tna samt H0.
      expr_body_pre ce cx env amount (et with gas_obs := []) /\
      expr_result_typed env target (Value tv) /\ expr_result_typed env amount (Value av) /\
      valid_horizon cx st0 H0 ea.storage_trace /\
      proxy_entry DF lo d ctx fn ce cx st0 b (ea with gas_obs := []) samt Ga tna /\
      proxy_row DF lo d ctx shctx PG fn ce cx st0 target sa a x es s G0 tn0 target_marks tv et Gt tnt st /\
      proxy_row DF lo d ctx shctx PG fn ce cx st0 amount a b y (et with gas_obs := []) st Gt tnt
        amount_marks av ea Ga tna samt ==>
      ?u Gu tnu.
        create_operand_full_scope b c (gas_explicit_sites ctx shctx) ctx fn samt [] (OK u) /\
        proxy_entry DF lo d ctx fn ce cx st0 c (ea with gas_obs := []) u Gu tnu``

Theorem proxy_visit_child_pre[local]:
  proxy_entry DF lo d ctx fn ce cx st0 a es s G tn /\
  expr_body_pre ce cx env e es /\ (!H. dead_lo_ok H (DF H) lo ce cx) /\
  lower_value compile_expr ce (expr_type e) e a = (op,m) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (op,shm) /\
  expr_sim_full_code (ctx,shctx,fn,shfn) (a,m,sha,shm) ==>
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx (expr_type e) e es
     (st0,a,m,sha,shm,op,s,G,tn)
Proof
  simp[expr_sim_full_pre_def, expr_sim_full_code_def, create_operand_at_def] >>
  metis_tac[expr_body_pre_gas_admissible]
QED

Theorem proxy_visit_bind_left[local]:
  create_operand_cut a b E C f tops cx st0 source (es,s) /\
  (!v. storage_trace_frame (next v)) ==>
  create_operand_cut a b E C f tops cx st0 (bind source next) (es,s)
Proof
  simp[create_operand_cut_def] >> metis_tac[create_cut_bind_left]
QED

(* Use the salt IH only when the selected visit has passed the buffer. *)
Theorem proxy_visit_salt[local]:
  proxy_neutral_law tops ctx ce cx fn (gas_explicit_sites ctx shctx) st0 /\
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_cut_code {} b c /\ fn_has_code b c fn /\
  create_cut_code {} c sc /\ fn_has_code c sc fn /\
  proxy_admin_band b c /\ create_operand_at b s /\ ~s.vs_halted /\
  create_operand_full_scope b c (gas_explicit_sites ctx shctx) ctx fn s [] (OK u) /\
  proxy_entry DF lo d ctx fn ce cx st0 c es u G tn /\
  expr_body_pre ce cx env salt es /\ body_const_cells_agree [(NONE,tops)] cx env es /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  lower_value compile_expr ce (expr_type salt) salt c = (op,sc) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type salt) (gas_shadow_expr salt) shc = (op,shsc) /\
  expr_sim_full_code (ctx,shctx,fn,shfn) (c,sc,shc,shsc) /\
  proxy_child tops ctx shctx ce cx env DF lo d PG fn shfn st0 salt c sc shc shsc op es u G tn /\
  (!vs. storage_trace_frame (k vs : evaluation_state -> (eval_result + exception) # evaluation_state)) ==>
  create_operand_cut b sc (gas_explicit_sites ctx shctx) ctx fn tops cx st0
     (bind (eval_exprs cx [salt]) k) (es,s)
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "neutral") (map_every assume_tac o CONJUNCTS)) >>
  asm_x "neutral" irule >> qexists_tac `c` >> qexists_tac `u` >> simp[] >>
  simp[create_copy_source_cons, cj 49 vyperInterpreterTheory.evaluate_def, bind_return] >>
  irule proxy_visit_bind_left >> simp[] >>
  drule_all (SIMP_RULE bool_ss [] proxy_visit_child_pre) >> strip_tac >>
  first_x_assum irule >> simp[]
QED

(* Ordinary and shadow code have already been paired at these cuts. *)
Theorem proxy_visit_two_scalars[local]:
  proxy_scalar_law tops ctx shctx ce cx env DF lo d PG fn shfn st0 /\
  proxy_window_law tops ctx shctx ce cx env DF lo d PG fn st0 /\
  proxy_neutral_law tops ctx ce cx fn (gas_explicit_sites ctx shctx) st0 /\
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (Call ann (CreateTarget CreateMinimalProxy salted rof ks)
    (target::amount::salts) opt) es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  (!e a m sha shm op es s G tn. MEM e (target::amount::salts) ==>
    proxy_child tops ctx shctx ce cx env DF lo d PG fn shfn st0 e a m sha shm op es s G tn) /\
  expr_type target = BaseT AddressT /\ expr_type amount = BaseT (UintT 256) /\
  proxy_entry DF lo d ctx fn ce cx st0 sa es s G0 tn0 /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  lower_value compile_expr ce (expr_type target) target sa = (x,a) /\
  lower_value compile_expr ce (expr_type amount) amount a = (y,b) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type target) (gas_shadow_expr target) sha = (x,sha1) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type amount) (gas_shadow_expr amount) sha1 = (y,shb) /\
  expr_sim_full_code (ctx,shctx,fn,shfn) (sa,a,sha,sha1) /\
  expr_sim_full_code (ctx,shctx,fn,shfn) (a,b,sha1,shb) /\
  compile_create_proxy_buf x b = (buf,c) /\ fn_has_code b c fn /\
  create_cut_code {} sa a /\ create_cut_code {} a b /\ create_cut_code {} b c /\
  create_cut_code {} c sc /\ fn_has_code a sc fn /\ fn_has_code b sc fn /\ fn_has_code c sc fn /\
  ci_mono sa a /\ ci_mono a b /\ ci_mono b c /\
  (if salted then
     ?salt sop shc shsc. salts = [salt] /\
       lower_value compile_expr ce (expr_type salt) salt c = (sop,sc) /\
       lower_value compile_expr (gas_shadow_env T ce) (expr_type salt) (gas_shadow_expr salt) shc = (sop,shsc) /\
       expr_sim_full_code (ctx,shctx,fn,shfn) (c,sc,shc,shsc)
   else salts = [] /\ c = sc) /\
  (!vs. storage_trace_frame (k vs : evaluation_state -> (eval_result + exception) # evaluation_state)) ==>
  create_operand_cut sa sc (gas_explicit_sites ctx shctx) ctx fn tops cx st0
    (bind (eval_exprs cx (target::amount::salts)) k) (es,s)
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "scalar") (CONJUNCTS_THEN2 (mk_asm "window")
    (CONJUNCTS_THEN2 (mk_asm "neutral") (map_every assume_tac o CONJUNCTS)))) >>
  `expr_body_pre ce cx env target es` by
    (irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
     fs[expr_body_pre_def]) >>
  `create_cut_code {} b sc /\ create_cut_code {} a sc` by
    metis_tac[create_cut_code_join] >>
  drule proxy_buffer_admin_band >> CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >>
  once_rewrite_tac[create_copy_source_cons] >>
  asm "scalar" irule >>
  qpat_assum `lower_value _ _ _ target sa = (x,a)` (irule_at Any) >>
  qpat_assum `expr_sim_full_code _ (sa,a,sha,sha1)` (irule_at Any) >>
  simp[] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  conj_tac >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame] >>
  map_every qx_gen_tac [`Ht`,`mt`,`tv`,`et`,`Gt`,`tnt`,`st`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre ce cx env amount (et with gas_obs := [])` by
    (irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  once_rewrite_tac[create_copy_source_cons] >>
  asm_x "scalar" irule >>
  qpat_assum `lower_value _ _ _ amount a = (y,b)` (irule_at Any) >>
  qpat_assum `expr_sim_full_code _ (a,b,sha1,shb)` (irule_at Any) >>
  simp[] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  conj_tac >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame] >>
  map_every qx_gen_tac [`Ha`,`ma`,`av`,`ea`,`Ga`,`tna`,`samt`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `salted` >> fs[]
  >- (asm "window" (mp_then Any mp_tac proxy_buffer_admin_band) ORELSE all_tac >>
      FAIL_TAC "salted midpoint") >>
  irule create_admin_sequence_cut >> simp[]
QED
