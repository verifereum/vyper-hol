(* A selected scalar operand, with the same normal row at every horizon. *)
Theory entryCreateScalarVisitBind
Ancestors
  entryCreateFocusSpec entryCreateBodyCut createExprSizeExitDefs createSizeCutCode
  bodyFullPreds bodyMemoryDefs bodyInvCodeProps exprBodyPreProps exprSimSource
  exprSimFullBundleProps exprOperandVar fragGasOriginPtrExec fragGasOriginPtr
  loweringPosts vyperStorageTrace vyperStorageFootprint vyperState
  bodyFullIfExpReach fragExec exprLoweringProps venomExecSemantics
  list pair s1PrefixDefs gasExplicitSites

Overload scalar_visit_split[local] = ``\tops ctx ce cx fn E.
  !a m b s p d k before hit after.
    body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
    create_cut_code {} a m /\ fn_has_code a m fn /\
    create_cut_code {} m b /\ fn_has_code m b fn /\
    create_interior_visit a b E ctx fn (p,d,k) s (before,hit,after) ==>
    create_interior_visit a m E ctx fn (p,d,k) s (before,hit,after) \/
    ?t d1 k1 front back.
      before = front ++ back /\ create_operand_at m t /\
      create_expr_prefix a m E ctx fn s (create_cut_marks E front) t /\
      create_interior_visit m b E ctx fn (p,d1,k1) t (back,hit,after)``

Overload scalar_visit_replay[local] = ``\tops cx ctx fn E st0 DF lo (PG : (num # num) option list).
  !a m b s es G0 tn0 (source : evaluation_state -> (value + exception) # evaluation_state)
   (next : value -> evaluation_state -> (eval_result + exception) # evaluation_state) Q.
  (!p d k before hit after.
    create_interior_visit a b E ctx fn (p,d,k) s (before,hit,after) ==>
    create_interior_visit a m E ctx fn (p,d,k) s (before,hit,after) \/
    ?t d1 k1 front back.
      before = front ++ back /\ create_operand_at m t /\
      create_expr_prefix a m E ctx fn s (create_cut_marks E front) t /\
      create_interior_visit m b E ctx fn (p,d1,k1) t (back,hit,after)) /\
  ~s.vs_halted /\
  create_operand_cut a m E ctx fn tops cx st0 source (es,s) /\
  gas_completed_operand (DF,lo,E,ctx,fn,PG) tops cx st0 a m source (es,s,G0,tn0) Q /\
  (!H r mid G tn t. Q H r mid G tn t ==> ?v. r = INL v) /\
  (!v. storage_trace_frame (next v)) /\
  (!H0 front v mid G tn t.
    valid_horizon cx st0 H0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,E,ctx,fn,PG) (s,G0,tn0)
        (create_cut_marks E front) (OK t,G,tn) /\
      Q H (INL v : value + exception) (mid with gas_obs := []) G tn t) ==>
    create_operand_cut m b E ctx fn tops cx st0 (next v) (mid with gas_obs := [],t)) ==>
  create_operand_cut a b E ctx fn tops cx st0 (bind source next) (es,s)``

Overload scalar_visit_entry[local] = ``\DF lo d ctx fn ce cx st0 a es s G tn.
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

Overload scalar_visit_source_post[local] = ``\tops ce cx env e r mid.
  expr_sim_inv ce cx env mid /\ body_const_cells_agree [(NONE,tops)] cx env mid /\
  (!v. r = INL v ==> expr_result_typed env e (Value v) /\
    ?a tv b a' v' b'. eval_expr cx e a = (INL tv,b) /\
                        read_result cx tv a' = (INL v',b'))``

Theorem selected_scalar_replay_source[local]:
  expr_body_pre ce cx env e es /\ body_const_cells_agree [(NONE,tops)] cx env es /\
  gas_completed_operand (DF,lo,E,ctx,fn,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0) Q ==>
  gas_completed_operand (DF,lo,E,ctx,fn,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0)
    (\H r mid G tn t. Q H r mid G tn t /\
      scalar_visit_source_post tops ce cx env e r mid /\
      (!h. valid_horizon cx st0 h mid.storage_trace ==>
           valid_horizon cx st0 h es.storage_trace))
Proof
  simp[gas_completed_operand_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  rfs[] >> first_x_assum drule_all >> strip_tac
  >- (disj1_tac >> qexistsl [`G`,`tn`] >> simp[] >> rpt strip_tac >>
      qmatch_asmsub_abbrev_tac `bind (eval_expr cx e) (read_result cx) start = _` >>
      `expr_body_pre ce cx env e start /\
       body_const_cells_agree [(NONE,tops)] cx env start` by simp[Abbr `start`] >>
      drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimSourceTheory.expr_body_pre_eval) >>
      strip_tac >>
      `body_const_cells_agree [(NONE,tops)] cx env ee` by
        (irule body_const_cells_agree_expr_read >>
         qpat_assum `bind (eval_expr cx e) _ start = _` (irule_at Any) >>
         drule expr_body_pre_static_facts >> simp[]) >>
      `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
        simp[storage_trace_frame_bind_all, cj 5 evaluate_storage_trace_frame,
             storage_trace_frame_read_result] >>
      `!h. valid_horizon cx st0 h ee.storage_trace ==>
           valid_horizon cx st0 h es.storage_trace` by
        (rpt strip_tac >> drule_all valid_horizon_frame >> simp[Abbr `start`]) >>
      simp[] >> gvs[] >>
      drule (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimSourceTheory.eval_expr_read_INL) >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem scalar_visit_frame_advance[local]:
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,E,ctx,fn,PG) (s,G0,tn0) marks (OK t,G,tn) /\
    expr_sim_full_post (DF,lo,d,ctx,fn) ce cx e (es,a,m,s,op,G0,tn0)
      H (INL v : value + exception) (mid with gas_obs := []) G tn t) ==>
  scalar_visit_entry DF lo d ctx fn ce cx st0 a es s G0 tn0 /\
  ci_mono a m /\
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  valid_horizon cx st0 H0 mid.storage_trace ==>
  scalar_visit_entry DF lo d ctx fn ce cx st0 m (mid with gas_obs := []) t G tn
Proof
  simp_tac bool_ss [vyperStateTheory.evaluation_state_accessors] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  fs[expr_sim_full_post_def, expr_sim_full_endpoint_def] >>
  `~t.vs_halted` by (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  `return_buf_frame d ce m t` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d ce a s` (irule_at Any) >>
     fs[ci_mono_def, loweringPostsTheory.expr_post_def]) >>
  `!f i z. frag_reachable ctx fn t f i z ==> dalloca_fmp_headroom i z` by
    (rpt gen_tac >> strip_tac >> drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]) >>
  simp[create_operand_at_def] >> rpt conj_tac
  >- metis_tac[compiler_ci_mono_reserved]
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `a` >>
      fs[ci_mono_def])
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `a` >>
      fs[ci_mono_def]) >>
  rpt strip_tac >> res_tac >> fs[loweringPostsTheory.expr_post_def]
QED

Theorem scalar_visit_return[local]:
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,E,ctx,fn,PG) (s,G0,tn0) marks (OK t,G,tn) /\
    expr_sim_full_post (DF,lo,d,ctx,fn) ce cx e (es,a,m,s,op,G0,tn0)
      H (INL v : value + exception) (mid with gas_obs := []) G tn t /\
    scalar_visit_source_post tops ce cx env e (INL v) (mid with gas_obs := []) /\
    (!h. valid_horizon cx st0 h mid.storage_trace ==>
         valid_horizon cx st0 h es.storage_trace)) ==>
  valid_horizon cx st0 H0 mid.storage_trace /\
  scalar_visit_entry DF lo d ctx fn ce cx st0 a es s G0 tn0 /\
  ci_mono a m /\
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) ==>
  scalar_visit_source_post tops ce cx env e (INL v) (mid with gas_obs := []) /\
  scalar_visit_entry DF lo d ctx fn ce cx st0 m (mid with gas_obs := []) t G tn /\
  (!h. valid_horizon cx st0 h mid.storage_trace ==>
       valid_horizon cx st0 h es.storage_trace) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,E,ctx,fn,PG) (s,G0,tn0) marks (OK t,G,tn) /\
    expr_sim_full_post (DF,lo,d,ctx,fn) ce cx e (es,a,m,s,op,G0,tn0)
      H (INL v : value + exception) (mid with gas_obs := []) G tn t)
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  disch_then (mk_asm "row") >> strip_tac >>
  asm "row" (qspec_then `H0` mp_tac) >> simp[] >> strip_tac >>
  simp[] >> reverse conj_asm2_tac
  >- (qx_gen_tac `h` >> strip_tac >>
      asm "row" (qspec_then `h` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  drule scalar_visit_frame_advance >>
  disch_then (qspec_then `H0` mp_tac) >> simp[] >>
  impl_tac >- first_assum ACCEPT_TAC >> simp[]
QED

Theorem scalar_visit_cons_horizon:
  scalar_visit_split tops ctx ce cx fn E /\
  scalar_visit_replay tops cx ctx fn E st0 DF lo PG /\
  E = gas_explicit_sites ctx shctx /\
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  scalar_visit_entry DF lo d ctx fn ce cx st0 a es s G0 tn0 /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  lower_value compile_expr ce (expr_type e) e a = (op,m) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (op,shm) /\
  expr_sim_full_code (ctx,shctx,fn,shfn) (a,m,sha,shm) /\
  create_cut_code {} a m /\ create_cut_code {} m b /\ fn_has_code m b fn /\
  (expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx (expr_type e) e es
       (st0,a,m,sha,shm,op,s,G0,tn0) ==>
    expr_sim_scoped (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx (expr_type e) e es /\
    create_operand_cut a m E ctx fn tops cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s)) /\
  (!v. storage_trace_frame (next v : evaluation_state -> (eval_result + exception) # evaluation_state)) /\
  (!H0 marks v mid G tn t.
     valid_horizon cx st0 H0 mid.storage_trace /\
     scalar_visit_source_post tops ce cx env e (INL v : value + exception) (mid with gas_obs := []) /\
     scalar_visit_entry DF lo d ctx fn ce cx st0 m (mid with gas_obs := []) t G tn /\
     (!h. valid_horizon cx st0 h mid.storage_trace ==>
          valid_horizon cx st0 h es.storage_trace) /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,E,ctx,fn,PG) (s,G0,tn0) marks (OK t,G,tn) /\
       expr_sim_full_post (DF,lo,d,ctx,fn) ce cx e (es,a,m,s,op,G0,tn0)
         H (INL v : value + exception) (mid with gas_obs := []) G tn t) ==>
     create_operand_cut m b E ctx fn tops cx st0 (next v) (mid with gas_obs := [],t)) ==>
  create_operand_cut a b E ctx fn tops cx st0
    (bind (bind (eval_expr cx e) (read_result cx)) next) (es,s)
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "split")
    (CONJUNCTS_THEN2 (mk_asm "replay") (map_every assume_tac o CONJUNCTS))) >>
  `expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx (expr_type e) e es
      (st0,a,m,sha,shm,op,s,G0,tn0)` by
    (simp[expr_sim_full_pre_def] >>
     fs[expr_sim_full_code_def, create_operand_at_def] >>
     metis_tac[expr_body_pre_gas_admissible]) >>
  qpat_x_assum `expr_sim_full_pre _ _ _ _ _ _ _ ==> _` drule >> strip_tac >>
  drule expr_sim_full_code_fields >> strip_tac >>
  `!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
     metis_tac[body_inv_no_phi] >>
  `cx_tops cx = tops` by metis_tac[body_inv_main_code] >>
  `gas_completed_operand (DF,lo,E,ctx,fn,PG) tops cx st0 a m
     (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0)
     (expr_sim_full_post (DF,lo,d,ctx,fn) ce cx e (es,a,m,s,op,G0,tn0))` by
    (qpat_assum `cx_tops cx = tops` (SUBST1_TAC o SYM) >>
     qpat_assum `E = _` SUBST1_TAC >> irule expr_sim_scoped_completed >> simp[] >> metis_tac[]) >>
  drule_all selected_scalar_replay_source >> strip_tac >>
  qpat_x_assum `E = _` SUBST_ALL_TAC >>
  asm_x "replay" irule >>
  qpat_assum `gas_completed_operand _ _ _ _ _ _ _ _ (\H r mid G tn t. _)`
    (irule_at Any) >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> asm "split" irule >> simp[]) >>
  TRY (rpt strip_tac >> fs[expr_sim_full_post_def] >> NO_TAC) >>
  rpt gen_tac >> strip_tac >>
  `ci_mono a m` by metis_tac[ci_mono_lower_value_compile_expr,SND] >>
  drule (SIMP_RULE (srw_ss()) [] scalar_visit_return) >>
  disch_then (qspec_then `H0` mp_tac) >>
  impl_tac >- (simp[] >> first_assum ACCEPT_TAC) >> strip_tac >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem scalar_visit_cons:
  scalar_visit_split tops ctx ce cx fn E /\
  scalar_visit_replay tops cx ctx fn E st0 DF lo PG /\
  E = gas_explicit_sites ctx shctx /\
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  scalar_visit_entry DF lo d ctx fn ce cx st0 a es s G0 tn0 /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  lower_value compile_expr ce (expr_type e) e a = (op,m) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (op,shm) /\
  expr_sim_full_code (ctx,shctx,fn,shfn) (a,m,sha,shm) /\
  create_cut_code {} a m /\ create_cut_code {} m b /\ fn_has_code m b fn /\
  (expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx (expr_type e) e es
       (st0,a,m,sha,shm,op,s,G0,tn0) ==>
    expr_sim_scoped (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx (expr_type e) e es /\
    create_operand_cut a m E ctx fn tops cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s)) /\
  (!v. storage_trace_frame (next v : evaluation_state -> (eval_result + exception) # evaluation_state)) /\
  (!H0 marks v mid G tn t.
     valid_horizon cx st0 H0 mid.storage_trace /\
     scalar_visit_source_post tops ce cx env e (INL v : value + exception) (mid with gas_obs := []) /\
     scalar_visit_entry DF lo d ctx fn ce cx st0 m (mid with gas_obs := []) t G tn /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,E,ctx,fn,PG) (s,G0,tn0) marks (OK t,G,tn) /\
       expr_sim_full_post (DF,lo,d,ctx,fn) ce cx e (es,a,m,s,op,G0,tn0)
         H (INL v : value + exception) (mid with gas_obs := []) G tn t) ==>
     create_operand_cut m b E ctx fn tops cx st0 (next v) (mid with gas_obs := [],t)) ==>
  create_operand_cut a b E ctx fn tops cx st0
    (bind (bind (eval_expr cx e) (read_result cx)) next) (es,s)
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >>
  irule (CONV_RULE (REDEPTH_CONV BETA_CONV) scalar_visit_cons_horizon) >>
  simp[] >>
  qpat_assum `expr_sim_full_code _ _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr ce _ e a = _` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame d ce a s` (irule_at Any) >>
  qexistsl [`tn0`, `lo`, `PG`, `G0`, `DF`] >>
  gvs[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qpat_x_assum `!H0 marks v mid G tn t. _ ==> create_operand_cut _ _ _ _ _ _ _ _ _ _`
    mp_tac >>
  rpt (pop_assum kall_tac) >> metis_tac[]
QED
