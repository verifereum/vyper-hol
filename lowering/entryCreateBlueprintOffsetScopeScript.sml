(* The offset contributes one source operand even when no instruction is
   emitted.  Its normal continuation is at the actual check entry. *)
Theory entryCreateBlueprintOffsetScope
Ancestors
  entryCreateFocusSpec bodyFullCreateHeld[qualified] blueprintLiteralOffsetProps
  bodyFullPreds createSizeOperandPre exprSimHypsDefs exprSimWordArgs[qualified]
  loweringPosts vyperStorageTrace vyperState vyperInterpreter vyperAST
  gasExplicitSites gasSummary gasSummaryCompose fragGasOriginPtr
  wordArgsPtr[qualified] venomInst venomState ptrDiscipline compileEnv allocLimits abiEncoderProps
  vyperOriginFold vyperPinFold integer_word list

Overload offset_normal[local] = ``\DF lo d ctx hctx func PG ce cx env tops st0 e off n b en s Gn tn mo ov ee G1 tn1 t.
  storage_trace_domain cx st0 ee.storage_trace /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (en with gas_obs := gas_explicit mo s.vs_gas_readings ++ tail) =
    (INL ov,ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
      (s,Gn,tn) mo (OK t,G1,tn1)) /\
  create_operand_full_scope n b (gas_explicit_sites ctx hctx) ctx func s mo (OK t) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func ce cx e en n b s ee ov off t /\
    ghost_inv_at (DF H) lo d ce cx ee G1 tn1 t) /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  ~t.vs_halted /\ alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  ptr_val_ok cx (post_value_type ce e) ov off G1 tn1 t /\
  ghost_kept_at lo ce en n Gn tn s G1 tn1 /\ return_buf_frame d ce b t /\
  (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z) /\
  body_const_cells_agree [(NONE,tops)] cx env ee /\ expr_sim_inv ce cx env ee /\
  expr_result_typed env e (Value ov) /\
  (?p tv q p' v' q'. eval_expr cx e p = (INL tv,q) /\ read_result cx tv p' = (INL v',q')) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H en.storage_trace)``

Overload offset_scope_joins[local] = ``\a m b E ctx func s.
  (!marks. create_operand_focus_scope a m E ctx func s marks ==>
           create_operand_focus_scope a b E ctx func s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E ctx func s marks r ==>
             create_operand_full_scope a b E ctx func s marks r) /\
  (!left t right. create_operand_full_scope a m E ctx func s left (OK t) /\
                  create_operand_focus_scope m b E ctx func t right ==>
                  create_operand_focus_scope a b E ctx func s (left ++ right)) /\
  (!left t right r. create_operand_full_scope a m E ctx func s left (OK t) /\
                    create_operand_full_scope m b E ctx func t right r ==>
                    create_operand_full_scope a b E ctx func s (left ++ right) r)``

Overload offset_typed[local] = ``\DF lo d ctx hctx func PG ce cx env st0 e off n b en s Gn tn mo ov ow ee G1 tn1 t.
  storage_trace_domain cx st0 ee.storage_trace /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (en with gas_obs := gas_explicit mo s.vs_gas_readings ++ tail) =
    (INL ov,ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    valid_horizon cx st0 H en.storage_trace /\
    stmt_state_rel H ctx func ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G1 tn1 t /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
      (s,Gn,tn) mo (OK t,G1,tn1)) /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  ~t.vs_halted /\ alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s.vs_alloca_next <= t.vs_alloca_next /\ wb_frame ce en ee n s t /\
  ghost_kept_at lo ce en n Gn tn s G1 tn1 /\ return_buf_frame d ce b t /\
  (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z) /\
  expr_sim_inv ce cx env ee /\
  dest_NumV ov = SOME (w2n ow) /\ eval_operand off t = SOME ow /\
  op_taint tn1 off = {} /\ op_prov G1 off = NONE /\
  (!x. off = Var x ==> not_fresh_at b x)``

Overload offset_scalar_intro[local] = ``\DF lo d ctx hctx PG func hfunc ce cx env tops st0 e off n b hn hb en s Gn tn
  (k : value -> evaluation_state -> ('result + exception) # evaluation_state).
  !next z Q.
    body_inv tops ctx ce cx /\ body_const_cells_agree [(NONE,tops)] cx env en /\
    expr_body_pre ce cx env e en /\
    expr_sim_full_pre (DF,lo,d,ctx,hctx,PG,func,hfunc) ce cx (expr_type e) e en
      (st0,n,b,hn,hb,off,s,Gn,tn) /\
    expr_sim_scoped (DF,lo,d,ctx,hctx,PG,func,hfunc) ce cx (expr_type e) e en /\
    (!ov. storage_trace_frame (next ov : evaluation_state -> ('result + exception) # evaluation_state)) /\
    offset_scope_joins n b z (gas_explicit_sites ctx hctx) ctx func s /\
    (!mo ov ee G1 tn1 t.
      offset_normal DF lo d ctx hctx func PG ce cx env tops st0 e off n b en s Gn tn mo ov ee G1 tn1 t ==>
      scoped_operand_outcome (DF,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
        (cx_tops cx) cx st0 b z (next ov) (ee,t,G1,tn1) Q (create_operand_exit_post ctx cx)) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx hctx,ctx,func,PG) (cx_tops cx) cx st0 n z
      (bind (bind (eval_expr cx e) (read_result cx)) next) (en,s,Gn,tn) Q (create_operand_exit_post ctx cx)``

Theorem blueprint_offset_scoped_value[local]:
  body_inv tops ctx ce cx /\ body_const_cells_agree [(NONE,tops)] cx env en /\
  expr_body_pre ce cx env e en /\ expr_type e = BaseT (UintT 256) /\
  expr_sim_inv ce cx env en /\
  (case expr_int_literal (origin_fold_value e) of
     SOME i => comp_return (Lit (i2w i))
   | NONE => lower_value compile_expr ce (expr_type e) e) n = (off,b) /\
  (case expr_int_literal (origin_fold_value e) of
     SOME i => comp_return (Lit (i2w i))
   | NONE => lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e)) hn = (off,hb) /\
  (expr_int_literal (origin_fold_value e) = NONE ==>
    expr_sim_full_pre (DF,lo,d,ctx,hctx,PG,func,hfunc) ce cx (expr_type e) e en
      (st0,n,b,hn,hb,off,s,Gn,tn)) /\
  (expr_body_pre ce cx env e en /\ body_const_cells_agree [(NONE,tops)] cx env en ==>
    expr_sim_scoped (DF,lo,d,ctx,hctx,PG,func,hfunc) ce cx (expr_type e) e en) /\
  offset_scalar_intro DF lo d ctx hctx PG func hfunc ce cx env tops st0 e off n b hn hb en s Gn tn k /\
  offset_scope_joins n b z (gas_explicit_sites ctx hctx) ctx func s /\
  storage_trace_domain cx st0 en.storage_trace /\
  (!H. valid_horizon cx st0 H en.storage_trace ==>
    stmt_state_rel H ctx func ce cx en s /\ storage_well_formed_on cx en (FST H) /\
    ghost_inv_at (DF H) lo d ce cx en Gn tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = n.cs_current_bb /\ s.vs_inst_idx = LENGTH n.cs_current_insts /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  return_buf_frame d ce n s /\
  (!fn i u. frag_reachable ctx func s fn i u ==> dalloca_fmp_headroom i u) /\
  (!ov. storage_trace_frame (k ov : evaluation_state -> ('result + exception) # evaluation_state)) /\
  (!mo ov ow ee G1 tn1 t.
    offset_typed DF lo d ctx hctx func PG ce cx env st0 e off n b en s Gn tn mo ov ow ee G1 tn1 t ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
      (cx_tops cx) cx st0 b z (k ov) (ee,t,G1,tn1) Q (create_operand_exit_post ctx cx)) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
    (cx_tops cx) cx st0 n z (bind (bind (eval_expr cx e) (read_result cx)) k)
    (en,s,Gn,tn) Q (create_operand_exit_post ctx cx)
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `expr_int_literal (origin_fold_value e)`
  >- (`expr_sim_scoped (DF,lo,d,ctx,hctx,PG,func,hfunc) ce cx (expr_type e) e en`
        by simp[] >>
      qpat_assum `!next z Q. _ ==> scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
        (qspecl_then [`k`,`z`,`Q`] mp_tac) >>
      reverse impl_tac >- simp_tac bool_ss [] >>
      fs[] >> conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
      map_every qx_gen_tac [`mo`,`ov`,`ee`,`G1`,`tn1`,`t`] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      drule_all bodyFullCreateHeldTheory.blueprint_offset_word_return >> strip_tac >>
      qpat_assum `!mo ov ow ee G1 tn1 t. _ ==> scoped_operand_outcome _ _ _ _ _ _ _ _ _ _` irule >>
      simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
      qexists_tac `mo` >> simp[]) >>
  rename1 `expr_int_literal (origin_fold_value e) = SOME i` >>
  `bind (eval_expr cx e) (read_result cx) = return (IntV i)` by
    simp[FUN_EQ_THM,blueprint_literal_offset_read,return_def] >>
  `dest_NumV (IntV i) = SOME (w2n (i2w i : bytes32))` by
    metis_tac[blueprint_literal_offset_word] >>
  gvs[comp_return_def,bind_return] >>
  qpat_assum `!mo ov ow ee G1 tn1 t. _ ==> scoped_operand_outcome _ _ _ _ _ _ _ _ _ _` irule >>
  simp[eval_operand_def,op_taint_def,op_prov_def,exprSimWordArgsTheory.wb_frame_refl,
       wordArgsPtrTheory.ghost_kept_at_refl] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `[]` >> simp[return_def,gas_explicit_def,gas_origin_ptr_path_rules]
QED

(* At an actual normal offset return, use the earlier amount/salt replay
   (not another evaluation of them) to recover the constructor window. *)
Theorem blueprint_offset_scoped_bind:
  body_inv tops ctx ce cx /\ body_const_cells_agree [(NONE,tops)] cx env en /\
  expr_body_pre ce cx env offset en /\ expr_type offset = BaseT (UintT 256) /\ expr_sim_inv ce cx env en /\
  (case expr_int_literal (origin_fold_value offset) of
     SOME i => comp_return (Lit (i2w i))
   | NONE => lower_value compile_expr ce (expr_type offset) offset) sn = (off,sb) /\
  (case expr_int_literal (origin_fold_value offset) of
     SOME i => comp_return (Lit (i2w i))
   | NONE => lower_value compile_expr (gas_shadow_env T ce) (expr_type offset)
                (gas_shadow_expr offset)) hn = (off,hb) /\
  (expr_int_literal (origin_fold_value offset) = NONE ==>
    expr_sim_full_pre (DF,lo,d,ctx,hctx,PG,func,hfunc) ce cx (expr_type offset) offset en
      (st0,sn,sb,hn,hb,off,n,Gn,tnn)) /\
  (expr_body_pre ce cx env offset en /\ body_const_cells_agree [(NONE,tops)] cx env en ==>
    expr_sim_scoped (DF,lo,d,ctx,hctx,PG,func,hfunc) ce cx (expr_type offset) offset en) /\
  offset_scalar_intro DF lo d ctx hctx PG func hfunc ce cx env tops st0 offset off sn sb hn hb en n Gn tnn k /\
  offset_scope_joins sn sb z (gas_explicit_sites ctx hctx) ctx func n /\
  (!ov. storage_trace_frame (k ov : evaluation_state -> ('result + exception) # evaluation_state)) /\
  storage_trace_domain cx st0 en.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func ce cx es s) /\
  (!H. valid_horizon cx st0 H en.storage_trace ==>
    valid_horizon cx st0 H es.storage_trace /\
    stmt_state_rel H ctx func ce cx en n /\ storage_well_formed_on cx en (FST H) /\
    ghost_inv_at (DF H) lo d ce cx en Gn tnn n /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx hctx,ctx,func,PG) (s,G,tn) mn (OK n,Gn,tnn)) /\
  ~n.vs_halted /\ n.vs_current_bb = sn.cs_current_bb /\ n.vs_inst_idx = LENGTH sn.cs_current_insts /\
  alloca_history func n /\ (ctx_has_dalloca ctx ==> allocas_below_fmp n) /\
  return_buf_frame d ce sn n /\
  (!fn i u. frag_reachable ctx func n fn i u ==> dalloca_fmp_headroom i u) /\
  local_ptrs_reserved ce sa /\ ci_mono sa sn /\ ci_mono sn sb /\
  wb_frame ce es en sa s n /\ ghost_kept_at lo ce es sa G tn s Gn tnn /\ s.vs_alloca_next <= n.vs_alloca_next /\
  dest_NumV av = SOME (w2n yw) /\ dest_optional_salt sv = SOME sw /\ IS_SOME sv = salted /\
  LENGTH salts = (if salted then 1 else 0) /\
  eval_operand target s = SOME aw /\ op_taint tn target = {} /\
  (!x. target = Var x ==> not_fresh_at sa x) /\ (!l. target <> Label l) /\
  (!x. args_ptr = Var x \/ cnt = Var x ==> not_fresh_at sa x) /\
  eval_operand y n = SOME yw /\ op_taint tnn y = {} /\
  (!x. y = Var x ==> not_fresh_at sn x) /\ (!l. y <> Label l) /\
  OPTREL (\op w. eval_operand op n = SOME w /\ op_taint tnn op = {} /\
    (!x. op = Var x ==> not_fresh_at sn x) /\ (!l. op <> Label l)) sop sw /\
  (!ov ee go.
    (!tail. eval_exprs cx [offset] (en with gas_obs := go ++ tail) = (INL [ov],ee with gas_obs := tail)) ==>
    !tail. eval_exprs cx (amount::(salts ++ [offset]))
      (es with gas_obs := gas_explicit mn s.vs_gas_readings ++ go ++ tail) =
      (INL (av::((case sv of NONE => [] | SOME v => [v]) ++ [ov])),ee with gas_obs := tail)) /\
  (!ov ee G1 tn1 t gs.
    (!tail. eval_exprs cx (amount::(salts ++ [offset])) (es with gas_obs := gs ++ tail) =
      (INL (av::((case sv of NONE => [] | SOME v => [v]) ++ [ov])),ee with gas_obs := tail)) /\
    wb_frame ce es ee sa s t /\ ghost_kept_at lo ce es sa G tn s G1 tn1 /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ s.vs_alloca_next <= t.vs_alloca_next /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d ce cx ee G1 tn1 t) ==>
    eval_operand cnt t = SOME (n2w (LENGTH args)) /\ op_taint tn1 cnt = {} /\ op_prov G1 cnt = NONE /\
    (cnt <> Lit 0w ==> ?q a. args_ptr = Var q /\ lookup_var q t = SOME a /\
      ptr_covers G1 tn1 q t (LENGTH args) /\ (args = [] \/ w2n a + LENGTH args <= t.vs_alloca_next) /\
      (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tn1.t_mem) /\
      read_memory (w2n a) (LENGTH args) t = args)) /\
  (!mo ov ow ee G1 tn1 t.
    offset_typed DF lo d ctx hctx func PG ce cx env st0 offset off sn sb en n Gn tnn mo ov ow ee G1 tn1 t /\
    blueprint_literal_offset cx salted (target_e::amount::(salts ++ offset::ctor)) =
      IS_SOME (expr_int_literal (origin_fold_value offset)) /\
    (!tail. eval_exprs cx (amount::(salts ++ [offset]))
      (es with gas_obs := gas_explicit (mn ++ mo) s.vs_gas_readings ++ tail) =
      (INL (av::((case sv of NONE => [] | SOME v => [v]) ++ [ov])),ee with gas_obs := tail)) /\
    eval_operand target t = SOME aw /\ op_taint tn1 target = {} /\
    eval_operand y t = SOME yw /\ op_taint tn1 y = {} /\
    OPTREL (\op w. eval_operand op t = SOME w /\ op_taint tn1 op = {}) sop sw /\
    (!x. MEM (Var x) [target;off;args_ptr;cnt;y] \/ sop = SOME (Var x) ==> not_fresh_at sb x) /\
    eval_operand cnt t = SOME (n2w (LENGTH args)) /\ op_taint tn1 cnt = {} /\ op_prov G1 cnt = NONE /\
    (cnt <> Lit 0w ==> ?q a. args_ptr = Var q /\ lookup_var q t = SOME a /\
      ptr_covers G1 tn1 q t (LENGTH args) /\ (args = [] \/ w2n a + LENGTH args <= t.vs_alloca_next) /\
      (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tn1.t_mem) /\
      read_memory (w2n a) (LENGTH args) t = args) /\
    wb_frame ce es ee sa s t /\ ghost_kept_at lo ce es sa G tn s G1 tn1 /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d ce cx ee G1 tn1 t /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
        (s,G,tn) (mn ++ mo) (OK t,G1,tn1)) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
      (cx_tops cx) cx st0 sb z (k ov) (ee,t,G1,tn1) Q (create_operand_exit_post ctx cx)) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
    (cx_tops cx) cx st0 sn z (bind (eval_exprs cx [offset]) (\vs. k (HD vs)))
    (en,n,Gn,tnn) Q (create_operand_exit_post ctx cx)
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `bind (eval_exprs cx [offset]) (\vs. k (HD vs)) =
   bind (bind (eval_expr cx offset) (read_result cx)) k` by
    (once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
     simp[Once vyperInterpreterTheory.evaluate_def,bind_assoc,bind_return,ETA_THM]) >>
  pop_assum SUBST1_TAC >> irule blueprint_offset_scoped_value >>
  rpt (goal_assum (drule_at Any)) >> asm_rewrite_tac[] >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!H. _ ==> _ /\ stmt_state_rel _ _ _ _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`mo`,`ov`,`ow`,`ee`,`G1`,`tn1`,`t`] >>
  disch_then (fn th => assume_tac th >> map_every assume_tac (CONJUNCTS th)) >>
  `blueprint_literal_offset cx salted (target_e::amount::(salts ++ offset::ctor)) =
      IS_SOME (expr_int_literal (origin_fold_value offset))` by
    (irule blueprint_offset_literal_bit >> rpt (goal_assum (drule_at Any))) >>
  drule bodyFullCreateHeldTheory.blueprint_offset_eval_singleton >> strip_tac >>
  qpat_assum `!ov ee go. _ ==> !tail. eval_exprs _ _ _ = _` (drule_then assume_tac) >>
  `gas_path ctx func s (LENGTH mn) (OK n)` by
    (`valid_horizon cx st0 (storage_trace_horizon en.storage_trace) en.storage_trace`
       by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     qpat_assum `!H. _ ==> _ /\ stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     drule gas_origin_ptr_path_projections >> strip_tac >>
     drule fragGasOriginTheory.gas_origin_path_erase >>
     disch_then assume_tac >> irule fragGasModeTheory.gas_marked_path_exec >>
     qexists_tac `T` >> first_assum ACCEPT_TAC) >>
  `!tail. eval_exprs cx (amount::(salts ++ [offset]))
     (es with gas_obs := gas_explicit (mn ++ mo) s.vs_gas_readings ++ tail) =
     (INL (av::((case sv of NONE => [] | SOME v => [v]) ++ [ov])),ee with gas_obs := tail)` by
    (drule gas_explicit_append_path >> disch_then (qspec_then `mo` SUBST1_TAC) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!ov ee G1 tn1 t gs. _ ==> eval_operand cnt _ = _ /\ _`
    (qspecl_then [`ov`,`ee`,`G1`,`tn1`,`t`] assume_tac) >>
  `!go. (!tail. eval_exprs cx [offset] (en with gas_obs := go ++ tail) =
        (INL [ov],ee with gas_obs := tail)) ==>
      ?gs. !tail. eval_exprs cx (amount::(salts ++ [offset])) (es with gas_obs := gs ++ tail) =
        (INL (av::((case sv of NONE => [] | SOME v => [v]) ++ [ov])),ee with gas_obs := tail)` by
    (rpt strip_tac >> qexists_tac `gas_explicit mn s.vs_gas_readings ++ go` >>
     qpat_assum `!ov ee go. _ ==> !tail. eval_exprs _ _ _ = _` (drule_then mp_tac) >>
     simp[APPEND_ASSOC]) >>
  `!H. valid_horizon cx st0 H en.storage_trace ==>
     valid_horizon cx st0 H es.storage_trace /\
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
       (s,G,tn) mn (OK n,Gn,tnn)` by
    (rpt strip_tac >> qpat_assum `!H. _ ==> _ /\ stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `eval_operand target t = SOME aw /\ op_taint tn1 target = {} /\
   eval_operand y t = SOME yw /\ op_taint tn1 y = {} /\
   OPTREL (\op w. eval_operand op t = SOME w /\ op_taint tn1 op = {}) sop sw /\
   (!x. MEM (Var x) [target;args_ptr;cnt;y] \/ sop = SOME (Var x) ==> not_fresh_at sb x) /\
   eval_operand cnt t = SOME (n2w (LENGTH args)) /\ op_taint tn1 cnt = {} /\ op_prov G1 cnt = NONE /\
   (cnt <> Lit 0w ==> ?q a. args_ptr = Var q /\ lookup_var q t = SOME a /\
     ptr_covers G1 tn1 q t (LENGTH args) /\ (args = [] \/ w2n a + LENGTH args <= t.vs_alloca_next) /\
     (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tn1.t_mem) /\
     read_memory (w2n a) (LENGTH args) t = args) /\
   wb_frame ce es ee sa s t /\ ghost_kept_at lo ce es sa G tn s G1 tn1 /\
   MAP FDOM es.scopes = MAP FDOM ee.scopes /\ s.vs_alloca_next <= t.vs_alloca_next /\
   (!H. valid_horizon cx st0 H ee.storage_trace ==>
     valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func ce cx ee t /\
     storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d ce cx ee G1 tn1 t /\
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
       (s,G,tn) (mn ++ mo) (OK t,G1,tn1))` by
    (irule bodyFullCreateHeldTheory.blueprint_offset_finish_handoff >>
     rpt (goal_assum (drule_at Any)) >> asm_rewrite_tac[]) >>
  `!x. MEM (Var x) [target; off; args_ptr; cnt; y] \/ sop = SOME (Var x) ==>
       not_fresh_at sb x` by
    (qpat_assum `!x. MEM _ [target;args_ptr;cnt;y] \/ _ ==> _` mp_tac >>
     qpat_assum `!x. off = Var x ==> not_fresh_at sb x` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[MEM,DISJ_IMP_THM,FORALL_AND_THM] >>
     metis_tac[]) >>
  qpat_assum `!mo ov ow ee G1 tn1 t. _ ==> scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (qspecl_then [`mo`,`ov`,`ow`,`ee`,`G1`,`tn1`,`t`] mp_tac) >>
  simp_tac bool_ss [] >> (impl_tac >- asm_rewrite_tac[]) >> simp[]
QED
