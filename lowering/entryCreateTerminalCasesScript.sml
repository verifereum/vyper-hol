(* Discharge the terminal-specific introductions before handing the two
   scoped cases to the expression induction. *)
Theory entryCreateTerminalCases
Ancestors
  entryCreateRawRevertCase entryCreateSelfdestructCase entryCreateTerminalVV
  entryCreateTerminalBind entryCreateTerminalCut entryCreateRawRevertSelected
  entryCreateSelfdestructOperand entryCreateSelfdestructOverflow
  entryCreateSelfdestructExit entryCreateNativeFirstExit selfdestructHalt
  exprSimFullBundleProps exprSimDefs entryCreateFocusSpec fragExec
  vyperStorageTrace vyperState list

Theorem create_raw_revert_scoped_case:
  body_inv (cx_tops cx) ctx ce cx /\
  expr_body_pre ce cx env (Call ann RawRevert args dflt) es /\
  (!e st0 a m ha hm op s G tn.
    MEM e args /\ create_layout a m /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,hf) ce cx (expr_type e) e es
      (st0,a,m,ha,hm,op,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 a m (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
      (expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s,op,G,tn))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut a m (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
      (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s)) ==>
  (!st0 a b ha hb op s G tn.
    create_layout a b /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,hf) ce cx ty (Call ann RawRevert args dflt) es
      (st0,a,b,ha,hb,op,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 a b
      (vyperState$bind (eval_expr cx (Call ann RawRevert args dflt)) (read_result cx)) (es,s,G,tn)
      (expr_sim_full_post (DF,lo,d,ctx,f) ce cx (Call ann RawRevert args dflt) (es,a,b,s,op,G,tn))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut a b (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
      (vyperState$bind (eval_expr cx (Call ann RawRevert args dflt)) (read_result cx)) (es,s)) /\
  (!st0 a b ha hb vv s G tn.
    create_layout a b /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,hf) ce cx ty (Call ann RawRevert args dflt) es
      (st0,a,b,ha,hb,vv,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 a b (eval_expr cx (Call ann RawRevert args dflt)) (es,s,G,tn)
      (\H res ee G' tn' t.
         create_operand_vv_post (DF,lo,d,ctx,f) ce cx (Call ann RawRevert args dflt)
           (es,a,b,s,vv,G,tn) H res ee G' tn' t /\
         t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts)
      (create_operand_exit_post ctx cx) /\
    create_operand_cut a b (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
      (eval_expr cx (Call ann RawRevert args dflt)) (es,s))
Proof
  strip_tac >> match_mp_tac raw_revert_scoped_from_terminal_interfaces >>
  asm_simp_tac bool_ss [] >>
  conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC scoped_terminal_bind_at_child) >>
  conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC terminal_child_suffix_cut) >>
  conj_tac >-
    (rpt gen_tac >> CONV_TAC (DEPTH_CONV ETA_CONV) >> MATCH_ACCEPT_TAC
      (CONV_RULE (DEPTH_CONV ETA_CONV) raw_revert_selected_terminal_exit)) >>
  conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC terminal_no_success_vv_pointwise_site) >>
  first_assum ACCEPT_TAC
QED

Theorem create_selfdestruct_scoped_case:
  body_inv (cx_tops cx) ctx ce cx /\
  expr_body_pre ce cx env (Call ann SelfDestructTarget args dflt) es /\
  (!e st0 a m ha hm op s G tn. MEM e args /\ expr_body_pre ce cx env e es /\
    create_layout a m /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx (expr_type e) e es
      (st0,a,m,ha,hm,op,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 a m (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
      (expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s,op,G,tn))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut a m (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
      (bind (eval_expr cx e) (read_result cx)) (es,s)) ==>
  (!st0 a b ha hb op s G tn. create_layout a b /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty
      (Call ann SelfDestructTarget args dflt) es (st0,a,b,ha,hb,op,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 a b (bind (eval_expr cx (Call ann SelfDestructTarget args dflt)) (read_result cx))
      (es,s,G,tn) (expr_sim_full_post (DF,lo,d,ctx,f) ce cx (Call ann SelfDestructTarget args dflt)
        (es,a,b,s,op,G,tn)) (create_operand_exit_post ctx cx) /\
    create_operand_cut a b (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
      (bind (eval_expr cx (Call ann SelfDestructTarget args dflt)) (read_result cx)) (es,s)) /\
  (!st0 a b ha hb vv s G tn. create_layout a b /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty
      (Call ann SelfDestructTarget args dflt) es (st0,a,b,ha,hb,vv,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 a b (eval_expr cx (Call ann SelfDestructTarget args dflt)) (es,s,G,tn)
      (\H res ee G' tn' t.
        create_operand_vv_post (DF,lo,d,ctx,f) ce cx (Call ann SelfDestructTarget args dflt)
          (es,a,b,s,vv,G,tn) H res ee G' tn' t /\
        t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts)
      (create_operand_exit_post ctx cx) /\
    create_operand_cut a b (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
      (eval_expr cx (Call ann SelfDestructTarget args dflt)) (es,s))
Proof
  strip_tac >> match_mp_tac selfdestruct_scoped_from_terminal_interfaces >>
  asm_simp_tac bool_ss [] >>
  conj_tac >-
    (simp[selfdestruct_address_intro_def] >> rpt gen_tac >> strip_tac >>
     drule_all selfdestruct_selected_address_prefix >> simp[]) >>
  conj_tac >-
    (rewrite_tac[selfdestruct_physical_intro_def] >> rpt gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qmatch_goalsub_rename_tac `gas_origin_ptr_path (_,_,explicit,_,_,callee_pg) _ [] _` >>
     drule_all selfdestruct_selected_terminal_exit >>
     disch_then (qspecl_then [`explicit`,`callee_pg`]
       (qx_choosel_then [`exc`,`ee`,`r`] strip_assume_tac)) >>
     qexistsl_tac [`exc`,`ee`,`r`] >> simp[]) >>
  conj_tac >-
    (simp[selfdestruct_overflow_intro_def] >> rpt gen_tac >> strip_tac >>
     rename1 `valid_horizon source_cx st0 H source_es.storage_trace` >>
     `storage_trace_domain source_cx st0 source_es.storage_trace ==>
        valid_horizon source_cx st0 H source_es.storage_trace` by simp[] >>
     drule_all selfdestruct_boundary_exemption >> simp[]) >>
  conj_tac >-
    (rewrite_tac[selfdestruct_terminal_fold_def] >> rpt gen_tac >>
     MATCH_ACCEPT_TAC scoped_terminal_bind_at_child) >>
  conj_tac >-
    (simp[selfdestruct_terminal_cut_def] >> rpt gen_tac >> strip_tac >>
     irule terminal_child_suffix_cut >>
     simp[storage_trace_frame_bind_all, storage_trace_frame_selfdestruct_tail,
          storage_trace_frame_read_result] >>
     qpat_assum `lower_value _ _ _ _ _ = _` (irule_at Any) >>
     simp[] >> conj_tac
     >- (rpt gen_tac >> strip_tac >> irule create_interior_visit_first_exit >> simp[] >>
         qpat_assum `body_inv tops _ _ _` (irule_at Any)) >>
     strip_tac >> irule fn_has_code_split >> simp[]) >>
  conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC terminal_no_success_vv_pointwise_site) >>
  first_assum ACCEPT_TAC
QED
