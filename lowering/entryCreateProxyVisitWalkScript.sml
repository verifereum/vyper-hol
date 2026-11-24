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

Theorem proxy_admin_band_join[local]:
  !b. proxy_admin_band a b /\ proxy_admin_band b c ==> proxy_admin_band a c
Proof
  gen_tac >> disch_then strip_assume_tac >>
  qabbrev_tac `xs = emitted_insts a b` >>
  qabbrev_tac `ys = emitted_insts b c` >>
  `c.cs_current_insts = a.cs_current_insts ++ (xs ++ ys)` by
    (qpat_assum `c.cs_current_insts = _` (fn th => once_rewrite_tac[th]) >>
     simp[GSYM APPEND_ASSOC]) >>
  `emitted_insts a c = xs ++ ys` by
    (pure_rewrite_tac[emitted_insts_def] >>
     qpat_assum `c.cs_current_insts = a.cs_current_insts ++ _` (fn th => once_rewrite_tac[th]) >>
     pure_rewrite_tac[rich_listTheory.DROP_LENGTH_APPEND] >> REFL_TAC) >>
  simp[EVERY_APPEND]
QED

Theorem proxy_emit_admin_band[local]:
  (emit_op opc args a = (out,b) \/ emit_void opc args a = ((),b)) /\
  ~is_terminator opc /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2 ==>
  proxy_admin_band a b
Proof
  simp[emit_op_def, emit_void_def, emit_inst_def, fresh_var_def, fresh_id_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt strip_tac >> gvs[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem proxy_admin_band_primitives[local]:
  (!opc args a out b. emit_op opc args a = (out,b) ==>
    ~is_terminator opc /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2 ==>
    proxy_admin_band a b) /\
  (!opc args a b. emit_void opc args a = ((),b) ==>
    ~is_terminator opc /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2 ==>
    proxy_admin_band a b)
Proof
  metis_tac[proxy_emit_admin_band]
QED

Theorem proxy_alloc_admin_band[local]:
  compile_alloc_buffer n a = (buf,b) ==> proxy_admin_band a b
Proof
  strip_tac >> drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem proxy_buffer_admin_band[local]:
  compile_create_proxy_buf x b = (buf,c) ==> proxy_admin_band b c
Proof
  simp[compile_create_proxy_buf_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer 96 b = (al,b1)` >>
  rename1 `emit_void MSTORE [al.buf_operand; _] b1 = ((),b2)` >>
  rename1 `emit_op SHL _ b2 = (aligned,b3)` >>
  rename1 `emit_op ADD [al.buf_operand; Lit 19w] b3 = (dst,b4)` >>
  rename1 `emit_void MSTORE [dst;aligned] b4 = ((),b5)` >>
  rename1 `emit_op ADD [al.buf_operand; Lit 39w] b5 = (last,b6)` >>
  `proxy_admin_band b b1` by (drule proxy_alloc_admin_band >> simp[]) >>
  `proxy_admin_band b1 b2` by
    (irule (cj 2 proxy_admin_band_primitives) >> first_assum (irule_at Any) >> simp[is_terminator_def]) >>
  `proxy_admin_band b2 b3` by
    (irule (cj 1 proxy_admin_band_primitives) >> first_assum (irule_at Any) >> simp[is_terminator_def]) >>
  `proxy_admin_band b3 b4` by
    (irule (cj 1 proxy_admin_band_primitives) >> first_assum (irule_at Any) >> simp[is_terminator_def]) >>
  `proxy_admin_band b4 b5` by
    (irule (cj 2 proxy_admin_band_primitives) >> first_assum (irule_at Any) >> simp[is_terminator_def]) >>
  `proxy_admin_band b5 b6` by
    (irule (cj 1 proxy_admin_band_primitives) >> first_assum (irule_at Any) >> simp[is_terminator_def]) >>
  `proxy_admin_band b6 c` by
    (irule (cj 2 proxy_admin_band_primitives) >> first_assum (irule_at Any) >> simp[is_terminator_def]) >>
  map_every (fn tm => match_mp_tac (Q.SPEC tm proxy_admin_band_join) >> conj_tac >- simp[])
    [`b1`,`b2`,`b3`,`b4`,`b5`,`b6`] >> simp[]
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
  asm_x "neutral" irule >> simp[] >> qexists_tac `c` >> qexists_tac `u` >> simp[] >>
  simp[create_copy_source_cons, cj 49 vyperInterpreterTheory.evaluate_def, bind_return] >>
  irule proxy_visit_bind_left >> simp[] >>
  qpat_x_assum `proxy_child tops ctx shctx ce cx env DF lo d PG fn shfn st0 salt c sc shc shsc op es u G tn` mp_tac >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> simp[] >>
  `expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx (expr_type salt) salt es
     (st0,c,sc,shc,shsc,op,u,G,tn)` by
    (irule proxy_visit_child_pre >>
     qpat_assum `expr_body_pre ce cx env salt es` (irule_at Any) >> simp[] >> metis_tac[]) >>
  simp[]
QED

(* Ordinary and shadow code have already been paired at these cuts. *)
Theorem proxy_visit_two_scalars[local]:
  proxy_scalar_law tops ctx shctx ce cx env DF lo d PG fn shfn st0 /\
  proxy_window_law tops ctx shctx ce cx env DF lo d PG fn st0 /\
  proxy_neutral_law tops ctx ce cx fn (gas_explicit_sites ctx shctx) st0 /\
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
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
  `create_cut_code {} b sc` by
    (irule create_cut_code_join >> qexists `c` >> simp[]) >>
  `create_cut_code {} a sc` by
    (irule create_cut_code_join >> qexists `b` >> simp[]) >>
  drule proxy_buffer_admin_band >> CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >>
  once_rewrite_tac[create_copy_source_cons] >>
  asm "scalar" irule >>
  qpat_assum `lower_value _ _ _ target sa = (x,a)` (irule_at Any) >>
  qpat_assum `expr_sim_full_code _ (sa,a,sha,sha1)` (irule_at Any) >>
  simp[] >> map_every qexists_tac [`tn0`,`G0`] >> simp[] >>
  conj_tac >- (rpt strip_tac >> first_assum (fn th => drule th >> simp[] >> NO_TAC)) >>
  conj_tac >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame] >>
  reverse conj_tac
  >- (strip_tac >> qpat_assum `!e a m sha shm op es s G tn. _` (qspec_then `target` mp_tac) >>
      CONV_TAC (REDEPTH_CONV BETA_CONV) >> simp[] >>
      disch_then (qspecl_then [`sa`,`a`,`sha`,`sha1`,`x`,`es`,`s`,`G0`,`tn0`] mp_tac) >> simp[]) >>
  map_every qx_gen_tac [`Ht`,`mt`,`tv`,`et`,`Gtar`,`tnt`,`st`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre ce cx env amount (et with gas_obs := [])` by
    (irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  once_rewrite_tac[create_copy_source_cons] >>
  asm_x "scalar" irule >>
  qpat_assum `lower_value _ _ _ amount a = (y,b)` (irule_at Any) >>
  qpat_assum `expr_sim_full_code _ (a,b,sha1,shb)` (irule_at Any) >>
  simp[] >> map_every qexists_tac [`tnt`,`Gtar`] >> simp[] >>
  conj_tac >- (rpt strip_tac >> first_assum (fn th => drule th >> simp[] >> NO_TAC)) >>
  conj_tac >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame] >>
  reverse conj_tac
  >- (strip_tac >> qpat_assum `!e a m sha shm op es s G tn. _` (qspec_then `amount` mp_tac) >>
      CONV_TAC (REDEPTH_CONV BETA_CONV) >> simp[] >>
      disch_then (qspecl_then [`a`,`b`,`sha1`,`shb`,`y`,`et with gas_obs := []`,`st`,`Gtar`,`tnt`] mp_tac) >> simp[]) >>
  map_every qx_gen_tac [`Ha`,`ma`,`av`,`ea`,`Gamt`,`tna`,`samt`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `salted` >> fs[]
  >- (`expr_body_pre ce cx env salt (ea with gas_obs := [])` by
        (irule create_operand_pre >>
         qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
      asm "window" (qspecl_then [`target`,`amount`,`sa`,`a`,`b`,`c`,`x`,`y`,`buf`,`es`,`s`,`G0`,`tn0`] mp_tac) >>
      impl_tac >- (simp[] >> rpt strip_tac >> qpat_assum `!f i z. frag_reachable ctx fn s f i z ==> _` drule >> simp[]) >>
      disch_then (qspecl_then [`mt`,`tv`,`et`,`Gtar`,`tnt`,`st`,`ma`,`av`,`ea`,`Gamt`,`tna`,`samt`,`Ha`] mp_tac) >>
      impl_tac >- (CONV_TAC (REDEPTH_CONV BETA_CONV) >> simp[] >> rpt strip_tac >>
                   first_assum (fn th => drule th >> simp[] >> NO_TAC)) >>
      CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >>
      fs[stmt_state_rel_start_gas_obs] >>
      irule proxy_visit_salt >> CONV_TAC (REDEPTH_CONV BETA_CONV) >> simp[] >>
      map_every qexists_tac [`DF`,`Gu`,`PG`,`c`,`ce`,`d`,`env`,`lo`,`sop`,`shc`,`shfn`,`shsc`,`tnu`,`u`] >>
      simp[] >>
      conj_tac >- (rpt strip_tac >> qpat_assum `!f i z. frag_reachable ctx fn u f i z ==> _` drule >> simp[]) >>
      conj_tac >- (asm "neutral" mp_tac >> CONV_TAC (REDEPTH_CONV BETA_CONV) >> simp[]) >>
      strip_tac >> qpat_assum `!e a m sha shm op es s G tn. _` (qspec_then `salt` mp_tac) >>
      CONV_TAC (REDEPTH_CONV BETA_CONV) >> simp[] >>
      disch_then (qspecl_then [`c`,`sc`,`shc`,`shsc`,`sop`,`ea with gas_obs := []`,`u`,`Gu`,`tnu`] mp_tac) >> simp[]) >>
  simp[cj 49 vyperInterpreterTheory.evaluate_def, bind_return] >>
  irule create_admin_sequence_cut >> simp[] >>
  irule proxy_buffer_admin_band >> first_assum (irule_at Any)
QED

(* Pair one ordinary interval with its shadow using the enclosing code. *)
Theorem proxy_visit_subcode[local]:
  expr_sim_full_code (ctx,shctx,fn,shfn) (sa,sb,sha,shb) /\
  fn_has_code a b fn /\ fn_has_code ha hb shfn /\
  gas_shadow_state a ha /\ gas_shadow_state b hb ==>
  expr_sim_full_code (ctx,shctx,fn,shfn) (a,b,ha,hb)
Proof
  simp[expr_sim_full_code_def]
QED

Theorem proxy_visit_salt_compile[local]:
  create_itinerary_salt ce e a salt b <=>
  compile_create_salt compile_expr ce e a = (salt,b)
Proof
  Cases_on `e` >>
  simp[create_itinerary_salt_def,compile_create_salt_def,comp_return_def,comp_bind_def]
  >- metis_tac[] >>
  pairarg_tac >> gvs[] >> metis_tac[]
QED

Theorem proxy_visit_installed_suffixes[local]:
  ci_mono sa a /\ ci_mono a b /\ ci_mono b c /\ ci_mono c sc /\
  compile_create_dispatch buf (Lit 54w) value salt rof sc = (result,sb) /\
  fn_has_code sa sb fn ==>
  fn_has_code a sc fn /\ fn_has_code b sc fn /\ fn_has_code c sc fn
Proof
  strip_tac >>
  `cs_extends sc sb` by
    metis_tac[compile_create_dispatch_labels,pairTheory.SND] >>
  fs[ci_mono_def] >>
  metis_tac[fn_has_code_mid,cs_extends_trans]
QED

(* Consume the geometry of the supplied itinerary, not a new visit. The
   itinerary projection is taken by statement so this walk builds independently. *)
Theorem proxy_predispatch_visit_walk:
  let e = Call ann (CreateTarget CreateMinimalProxy salted rof ks) args opt in
  let E = gas_explicit_sites ctx shctx in
  proxy_scalar_law tops ctx shctx ce cx env DF lo d PG fn shfn st0 /\
  proxy_window_law tops ctx shctx ce cx env DF lo d PG fn st0 /\
  proxy_neutral_law tops ctx ce cx fn E st0 /\
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env e es /\ body_const_cells_agree [(NONE,tops)] cx env es /\
  (!e a m sha shm op es s G tn. MEM e args ==>
    proxy_child tops ctx shctx ce cx env DF lo d PG fn shfn st0 e a m sha shm op es s G tn) /\
  proxy_entry DF lo d ctx fn ce cx st0 sa es s G0 tn0 /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  lower_value compile_expr ce ty e sa = (result,sb) /\
  lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha = (result,shb) /\
  expr_sim_full_code (ctx,shctx,fn,shfn) (sa,sb,sha,shb) /\
  (!xs value salt buf len.
     create_call_itinerary ce CreateMinimalProxy salted args sa xs value salt buf len ==>
     ?target amount salts x a b c sc.
       args = target::amount::salts /\
       lower_value compile_expr ce (expr_type target) target sa = (x,a) /\
       lower_value compile_expr ce (expr_type amount) amount a = (value,b) /\
       compile_create_proxy_buf x b = (buf,c) /\
       create_itinerary_salt ce (if salted then SOME (HD salts) else NONE) c salt sc /\
       xs = [a;b;c;sc] /\ len = Lit 54w) /\
  create_call_itinerary ce CreateMinimalProxy salted args sa cuts value salt buf len /\
  create_itinerary_code sa cuts sc /\
  create_interior_visit sa sc E ctx fn (p,depth,fuel) s (before,hit,after) ==>
  create_body_cut E tops cx st0 (eval_expr cx e) (es,s) (before,hit)
Proof
  simp_tac bool_ss [LET_THM] >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "scalar") (CONJUNCTS_THEN2 (mk_asm "window")
    (CONJUNCTS_THEN2 (mk_asm "neutral") (map_every assume_tac o CONJUNCTS)))) >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  drule proxy_pre_args >> strip_tac >>
  qpat_x_assum `!xs value salt buf len. _` (drule_then strip_assume_tac) >>
  gvs[create_itinerary_code_def,proxy_visit_salt_compile] >>
  `LENGTH salts = (if salted then 1 else 0)` by (Cases_on `salted` >> gvs[]) >>
  drule expr_sim_full_code_fields >> strip_tac >>
  drule_all proxy_compile_cuts >> strip_tac >> gvs[] >>
  rename1 `create_interior_visit sa sc _ _ _ _ _ _` >>
  rename1 `gas_shadow_state a ha` >> rename1 `gas_shadow_state b hb` >>
  rename1 `gas_shadow_state c hc` >> rename1 `gas_shadow_state sc hsc` >>
  drule_all proxy_visit_installed_suffixes >> strip_tac >>
  `fn_has_code sa a fn /\ fn_has_code a b fn /\ fn_has_code b c fn` by
    (qpat_x_assum `fn_has_code sha shb shfn` kall_tac >> drule_all proxy_cut_code >> simp[]) >>
  `fn_has_code sha ha shfn /\ fn_has_code ha hb shfn /\ fn_has_code hc hsc shfn` by
    (qpat_x_assum `fn_has_code sa sb fn` kall_tac >> drule_all proxy_cut_code >> simp[]) >>
  `expr_sim_full_code (ctx,shctx,fn,shfn) (sa,a,sha,ha) /\
   expr_sim_full_code (ctx,shctx,fn,shfn) (a,b,ha,hb)` by
    (conj_tac >> irule proxy_visit_subcode >>
     qpat_assum `expr_sim_full_code _ (sa,sb,sha,shb)` (irule_at Any) >> simp[]) >>
  `(if salted then ?sl sop shc shsc. salts = [sl] /\
      lower_value compile_expr ce (expr_type sl) sl c = (sop,sc) /\
      lower_value compile_expr (gas_shadow_env T ce) (expr_type sl) (gas_shadow_expr sl) shc = (sop,shsc) /\
      expr_sim_full_code (ctx,shctx,fn,shfn) (c,sc,shc,shsc)
    else salts = [] /\ c = sc)` by
    (Cases_on `salted` >> gvs[GSYM proxy_visit_salt_compile,create_itinerary_salt_def] >>
     map_every qexists_tac [`hc`,`hsc`] >> simp[] >>
     irule proxy_visit_subcode >>
     qpat_assum `expr_sim_full_code _ (sa,sb,sha,shb)` (irule_at Any) >> simp[]) >>
  `!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule bodyFullIfExpReachTheory.body_inv_no_phi >>
     qpat_assum `body_inv tops ctx ce cx` (irule_at Any) >> qexists_tac `fn` >> simp[]) >>
  once_rewrite_tac[evaluate_def] >> simp[create_operand_order_def] >>
  `create_operand_cut sa sc (gas_explicit_sites ctx shctx) ctx fn tops cx st0
     (bind (eval_exprs cx (target::amount::salts))
       (eval_create_operands cx CreateMinimalProxy salted rof (MAP expr_type (target::amount::salts))
         (blueprint_literal_offset cx salted (target::amount::salts)))) (es,s)` by
    (irule (BETA_RULE proxy_visit_two_scalars) >>
     qpat_assum `compile_create_proxy_buf x b = (buf,c)` (irule_at Any) >>
     qpat_assum `expr_sim_full_code _ (a,b,ha,hb)` (irule_at Any) >>
     qpat_assum `expr_sim_full_code _ (sa,a,sha,ha)` (irule_at Any) >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
     map_every qexists_tac [`value`,`tn0`,`lo`,`d`,`PG`,`G0`,`DF`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     CONV_TAC (REDEPTH_CONV BETA_CONV) >>
     TRY (FIRST (map (fn tag => asm tag (ACCEPT_TAC o CONV_RULE (REDEPTH_CONV BETA_CONV)))
       ["neutral","scalar","window"])) >>
     qpat_assum `expr_type target = BaseT AddressT` (fn th1 =>
       qpat_assum `expr_type amount = BaseT (UintT 256)` (fn th2 =>
         simp_tac (srw_ss()) [th1,th2,storage_trace_frame_create_operands])) >>
     TRY (first_assum ACCEPT_TAC) >>
     TRY (asm "window" (ACCEPT_TAC o SIMP_RULE (srw_ss()) [] o CONV_RULE (REDEPTH_CONV BETA_CONV))) >>
     TRY (qpat_assum `!e a m sha shm op es s G tn. _`
       (ACCEPT_TAC o SIMP_RULE (srw_ss()) [] o CONV_RULE (REDEPTH_CONV BETA_CONV)))) >>
  qhdtm_x_assum `create_operand_cut` (mp_tac o REWRITE_RULE[create_operand_cut_def]) >>
  disch_then (qspecl_then [`p`,`depth`,`fuel`,`before`,`hit`,`after`] mp_tac) >>
  CONV_TAC (REDEPTH_CONV ETA_CONV) >> simp[]
QED
