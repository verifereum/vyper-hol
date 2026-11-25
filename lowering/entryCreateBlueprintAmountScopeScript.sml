(* Enter the keyword suffix at the selected constructor return. *)
Theory entryCreateBlueprintAmountScope
Ancestors
  entryCreateFocusSpec bodyFullCreateHeld[qualified] bodyFullPreds
  createSizeOperandPre exprSimSource exprSimHypsDefs exprSimWordArgs[qualified]
  exprSimSend[qualified] s1PrefixDefs loweringPosts vyperStorageTrace vyperState
  vyperInterpreter vyperAST gasExplicitSites gasSummary fragGasOriginPtr
  venomInst allocLimits abiEncoderProps compileEnv list

Overload amount_normal[local] = ``\DF lo d ctx hctx func PG ce cx env tops st0 amount y a m es s G tn ma av em Gm tm t.
  storage_trace_domain cx st0 em.storage_trace /\
  (!tail. bind (eval_expr cx amount) (read_result cx)
    (es with gas_obs := gas_explicit ma s.vs_gas_readings ++ tail) =
    (INL av,em with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
      (s,G,tn) ma (OK t,Gm,tm)) /\
  create_operand_full_scope a m (gas_explicit_sites ctx hctx) ctx func s ma (OK t) /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
    expr_post H ctx func ce cx amount es a m s em av y t /\
    ghost_inv_at (DF H) lo d ce cx em Gm tm t) /\
  t.vs_current_bb = m.cs_current_bb /\ t.vs_inst_idx = LENGTH m.cs_current_insts /\
  ~t.vs_halted /\ alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  ptr_val_ok cx (post_value_type ce amount) av y Gm tm t /\
  ghost_kept_at lo ce es a G tn s Gm tm /\ return_buf_frame d ce m t /\
  (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z) /\
  body_const_cells_agree [(NONE,tops)] cx env em /\ expr_sim_inv ce cx env em /\
  expr_result_typed env amount (Value av) /\
  (?p tv q p' v' q'. eval_expr cx amount p = (INL tv,q) /\ read_result cx tv p' = (INL v',q')) /\
  (!H. valid_horizon cx st0 H em.storage_trace ==> valid_horizon cx st0 H es.storage_trace)``

Overload amount_scope_joins[local] = ``\a m b E ctx func s.
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

(* The scalar introduction premise is the ordinary-return specialization of
   the common scoped scalar bind, at this amount's ordinary and shadow cuts. *)
Theorem blueprint_amount_scoped_bind:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env
    (Call ann (CreateTarget (CreateFromBlueprint raw) salted rof ks)
      (target::amount::args) df) root /\
  expr_sim_inv ce cx env es /\ body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_type amount = BaseT (UintT 256) /\
  expr_sim_full_pre (DF,lo,d,ctx,hctx,PG,func,hfunc) ce cx (expr_type amount) amount es
    (st0,a,m,ha,hm,y,s,G,tn) /\
  (expr_body_pre ce cx env amount es /\ body_const_cells_agree [(NONE,tops)] cx env es ==>
    expr_sim_scoped (DF,lo,d,ctx,hctx,PG,func,hfunc) ce cx (expr_type amount) amount es) /\
  (!next b Q.
    body_inv tops ctx ce cx /\ body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre ce cx env amount es /\
    expr_sim_full_pre (DF,lo,d,ctx,hctx,PG,func,hfunc) ce cx (expr_type amount) amount es
      (st0,a,m,ha,hm,y,s,G,tn) /\
    expr_sim_scoped (DF,lo,d,ctx,hctx,PG,func,hfunc) ce cx (expr_type amount) amount es /\
    (!av. storage_trace_frame
      (next av : evaluation_state -> ('result + exception) # evaluation_state)) /\
    amount_scope_joins a m b (gas_explicit_sites ctx hctx) ctx func s /\
    (!ma av em Gm tm t.
      amount_normal DF lo d ctx hctx func PG ce cx env tops st0 amount y a m es s G tn ma av em Gm tm t ==>
      scoped_operand_outcome (DF,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
        (cx_tops cx) cx st0 m b (next av) (em,t,Gm,tm) Q (create_operand_exit_post ctx cx)) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx hctx,ctx,func,PG) (cx_tops cx) cx st0 a b
      (bind (bind (eval_expr cx amount) (read_result cx)) next) (es,s,G,tn) Q
      (create_operand_exit_post ctx cx)) /\
  amount_scope_joins a m b (gas_explicit_sites ctx hctx) ctx func s /\
  (!vs. storage_trace_frame
    (k vs : evaluation_state -> ('result + exception) # evaluation_state)) /\
  (!ma av em Gm tm t yw.
    amount_normal DF lo d ctx hctx func PG ce cx env tops st0 amount y a m es s G tn ma av em Gm tm t /\
    dest_NumV av = SOME (w2n yw) /\ eval_operand y t = SOME yw /\ op_taint tm y = {} /\
    (!x. y = Var x ==> not_fresh_at m x) /\ (!l. y <> Label l) /\
    wb_frame ce es em a s t /\
    (!H. valid_horizon cx st0 H em.storage_trace ==>
      stmt_state_rel H ctx func ce cx em t /\ storage_well_formed_on cx em (FST H) /\
      ghost_inv_at (DF H) lo d ce cx em Gm tm t) /\
    (!op w. (!x. op = Var x ==> not_fresh_at a x) /\ (!l. op <> Label l) /\
      eval_operand op s = SOME w /\ op_taint tn op = {} ==>
      eval_operand op t = SOME w /\ op_taint tm op = {}) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx hctx,ctx,func,PG) (cx_tops cx) cx st0 m b
      (bind (eval_exprs cx rest) (\vs. k (av::vs))) (em,t,Gm,tm) Q (create_operand_exit_post ctx cx)) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx hctx,ctx,func,PG) (cx_tops cx) cx st0 a b
    (bind (eval_exprs cx (amount::rest)) k) (es,s,G,tn) Q (create_operand_exit_post ctx cx)
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre ce cx env amount es` by
    (irule create_call_operand_body_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  `expr_sim_scoped (DF,lo,d,ctx,hctx,PG,func,hfunc) ce cx (expr_type amount) amount es` by simp[] >>
  `bind (eval_exprs cx (amount::rest)) k =
   bind (bind (eval_expr cx amount) (read_result cx))
     (\av. bind (eval_exprs cx rest) (\vs. k (av::vs)))` by
    (once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
     simp[bind_assoc,bind_return]) >>
  pop_assum SUBST1_TAC >>
  qpat_assum `!next b Q. _ ==> scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (qspecl_then [`\av. bind (eval_exprs cx rest) (\vs. k (av::vs))`, `b`, `Q`] mp_tac) >>
  reverse impl_tac >- simp_tac bool_ss [] >>
  simp_tac bool_ss [] >> asm_rewrite_tac[] >> conj_tac
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame] >>
  map_every qx_gen_tac [`ma`,`av`,`em`,`Gm`,`tm`,`t`] >>
  disch_then (fn th => assume_tac th >> map_every assume_tac (CONJUNCTS th)) >>
  `lower_value compile_expr ce (expr_type amount) amount a = (y,m)` by fs[expr_sim_full_pre_def] >>
  `is_word_type (BaseT (UintT 256))` by simp[is_word_type_def] >>
  qpat_assum `!H. _ ==> expr_post H _ _ _ _ amount _ _ _ _ _ _ _ _ /\ _`
    (mp_then Any (drule_all_then strip_assume_tac) bodyFullCreateHeldTheory.create_word_cut_frame_facts) >>
  `!op w. (!x. op = Var x ==> not_fresh_at a x) /\ (!l. op <> Label l) /\
      eval_operand op s = SOME w /\ op_taint tn op = {} ==>
      eval_operand op t = SOME w /\ op_taint tm op = {}` by
    (rpt gen_tac >> strip_tac >>
     drule_all_then ACCEPT_TAC bodyFullCreateHeldTheory.create_operand_cut_frame) >>
  qpat_assum `!ma av em Gm tm t yw. _ ==> scoped_operand_outcome _ _ _ _ m b _ _ _ _` irule >>
  asm_rewrite_tac[] >> conj_tac
  >- (qexists_tac `typed_val_to_w256 (BaseTV (UintT 256)) av` >>
      simp[exprSimSendTheory.uint256_typed_dest]) >>
  qexists_tac `ma` >> asm_rewrite_tac[]
QED
