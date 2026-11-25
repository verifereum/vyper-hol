Theory entryCreateBopWordVisit
Ancestors
  entryCreateFocusSpec entryCreateNativeFirstExit entryCreateReplayBind
  entryCreateAdminSequence entryCreateIntervalLayout exprBopSimProps
  exprBopSimDefs exprSimHyps exprSimSource bodyMemoryDefs vyperStorageTrace
  vyperStorageFootprint vyperState createExprSizeExitDefs createSizeCutCode
  createSizePrefixReplay entryCreateCompletedCut entryCreateBodyCut
  bodyFullIfExpReach exprSimFullBundleProps s1PrefixDefs fragGasOriginPtr
  exprLoweringProps gasExplicitSites venomInst fragExec list

Overload bop_visit_read[local] = ``\cx e. bind (eval_expr cx e) (read_result cx)``

(* Keep the single source equation supplied by the replay query. *)
Triviality bop_visit_replay_equation:
  gas_completed_operand (DF,lo,E,ctx,f,PG) tops cx st0 a m source
    (es,s,G0,tn0) Q ==>
  gas_completed_operand (DF,lo,E,ctx,f,PG) tops cx st0 a m source
    (es,s,G0,tn0)
    (\H r mid G tn t. Q H r mid G tn t /\
       ?incoming outgoing.
         source (es with gas_obs := incoming) = (r,mid with gas_obs := outgoing))
Proof
  simp[gas_completed_operand_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac
  >- (disj1_tac >> qexistsl [`G`,`tn`] >> simp[] >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >> simp[] >>
      qexistsl [`gas_explicit marks s.vs_gas_readings ++ tail`,`tail`] >>
      simp[evaluation_state_component_equality]) >>
  metis_tac[]
QED

Triviality bop_visit_child_bind:
  body_inv (cx_tops cx) ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\ ~s.vs_halted /\
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 a m
    (bop_visit_read cx e) (es,s,G0,tn0)
    (expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s,op,G0,tn0))
    (create_operand_exit_post ctx cx) /\
  create_operand_cut a m E ctx f (cx_tops cx) cx st0 (bop_visit_read cx e) (es,s) /\
  (!v. storage_trace_frame (next v : evaluation_state -> value evaluation_result)) /\
  (!H0 front v mid G tn t.
    mid.gas_obs = [] /\ valid_horizon cx st0 H0 mid.storage_trace /\
    (?incoming outgoing. bop_visit_read cx e (es with gas_obs := incoming) =
       (INL v,mid with gas_obs := outgoing)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (s,G0,tn0)
        (create_cut_marks E front) (OK t,G,tn) /\
      expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s,op,G0,tn0)
        H (INL v : value + vyperState$exception) mid G tn t) ==>
    create_operand_cut m b E ctx f (cx_tops cx) cx st0 (next v) (mid,t)) ==>
  create_operand_cut a b E ctx f (cx_tops cx) cx st0 (bind (bop_visit_read cx e) next) (es,s)
Proof
  strip_tac >>
  `!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  drule_all scoped_outcome_completed_operand >>
  disch_then (assume_tac o MATCH_MP bop_visit_replay_equation) >>
  irule create_operand_cut_bind_replay >>
  qpat_assum `gas_completed_operand _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> drule_all create_interior_visit_first_exit >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (qspec_then `H0` mp_tac) >> simp[] >> strip_tac >>
      qpat_assum `!H0 front v mid G tn t. _ ==> create_operand_cut _ _ _ _ _ _ _ _ _ _`
        irule >> simp[] >> rpt conj_tac
      >- (qexistsl [`G`,`front`,`tn`] >> qx_gen_tac `h` >> strip_tac >>
          qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
            (qspec_then `h` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
          disch_then (map_every assume_tac o CONJUNCTS) >>
          conj_tac >> first_assum ACCEPT_TAC)
      >- (qexistsl [`incoming`,`outgoing`] >> simp[]) >>
      qexists_tac `H0` >> simp[]) >>
  rpt strip_tac >> fs[expr_sim_full_post_def]
QED

Theorem create_bop_word_operand_cut:
  body_inv (cx_tops cx) ctx ce cx /\
  expr_body_pre ce cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  body_const_cells_agree [(NONE,cx_tops cx)] cx env es /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty
    (Builtin ann (Bop bop) [e1;e2]) es (st0,sa,sb,sha,shb,op,s0,G0,tn0) /\
  E = gas_explicit_sites ctx shctx /\
  create_layout sa s1 /\ create_layout s1 s2 /\
  lower_value compile_expr ce (expr_type e1) e1 sa = (x,s1) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type e1)
    (gas_shadow_expr e1) sha = (x,sh1) /\
  gas_shadow_state s1 sh1 /\ fn_has_code sha sh1 shf /\
  create_cut_code {} sa s1 /\ fn_has_code sa s1 f /\
  create_cut_code {} s1 sb /\ fn_has_code s1 sb f /\
  create_cut_code {} s1 s2 /\ fn_has_code s1 s2 f /\
  create_cut_code {} s2 sb /\ fn_has_code s2 sb f /\
  sb.cs_current_bb = s2.cs_current_bb /\
  sb.cs_current_insts = s2.cs_current_insts ++ emitted_insts s2 sb /\
  EVERY (\i. i.inst_id IN frag_ids s2 sb /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2) (emitted_insts s2 sb) /\
  (expr_body_pre ce cx env e1 es /\ body_const_cells_agree [(NONE,cx_tops cx)] cx env es /\
   create_layout sa s1 /\
   expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx (expr_type e1) e1 es
     (st0,sa,s1,sha,sh1,x,s0,G0,tn0) ==>
   scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 sa s1
     (bop_visit_read cx e1) (es,s0,G0,tn0)
     (expr_sim_full_post (DF,lo,d,ctx,f) ce cx e1 (es,sa,s1,s0,x,G0,tn0))
     (create_operand_exit_post ctx cx) /\
   create_operand_cut sa s1 E ctx f (cx_tops cx) cx st0 (bop_visit_read cx e1) (es,s0)) /\
  (!H0 marks v mid G tn t.
    mid.gas_obs = [] /\ valid_horizon cx st0 H0 mid.storage_trace /\
    (?incoming outgoing. bop_visit_read cx e1 (es with gas_obs := incoming) =
      (INL v,mid with gas_obs := outgoing)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_sim_full_post (DF,lo,d,ctx,f) ce cx e1 (es,sa,s1,s0,x,G0,tn0)
        H (INL v : value + vyperState$exception) mid G tn t /\
      gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (s0,G0,tn0) marks (OK t,G,tn)) ==>
    (?a tv b a' v' b'. eval_expr cx e1 a = (INL tv,b) /\
                       read_result cx tv a' = (INL v',b')) /\
    expr_body_pre ce cx env e2 mid /\ body_const_cells_agree [(NONE,cx_tops cx)] cx env mid /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx (expr_type e1) e2 mid
      (st0,s1,s2,sh1,sh2,y,t,G,tn)) /\
  (!mid t G tn.
    (?a tv b a' v' b'. eval_expr cx e1 a = (INL tv,b) /\
                       read_result cx tv a' = (INL v',b')) /\
    expr_body_pre ce cx env e2 mid /\ body_const_cells_agree [(NONE,cx_tops cx)] cx env mid /\
    create_layout s1 s2 /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx (expr_type e1) e2 mid
      (st0,s1,s2,sh1,sh2,y,t,G,tn) ==>
    scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 s1 s2
      (bop_visit_read cx e2) (mid,t,G,tn)
      (expr_sim_full_post (DF,lo,d,ctx,f) ce cx e2 (mid,s1,s2,t,y,G,tn))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut s1 s2 E ctx f (cx_tops cx) cx st0 (bop_visit_read cx e2) (mid,t)) ==>
  create_operand_cut sa sb E ctx f (cx_tops cx) cx st0
    (bop_visit_read cx (Builtin ann (Bop bop) [e1;e2])) (es,s0)
Proof
  strip_tac >>
  drule expr_body_pre_bop >> strip_tac >>
  `expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx (expr_type e1) e1 es
     (st0,sa,s1,sha,sh1,x,s0,G0,tn0) /\ MEM f ctx.ctx_functions /\ ~s0.vs_halted` by
    (qpat_assum `expr_sim_full_pre _ _ _ _ (Builtin _ _ _) _ _`
       (strip_assume_tac o REWRITE_RULE [expr_sim_full_pre_def]) >>
     simp[expr_sim_full_pre_def] >> conj_tac
     >- (irule expr_body_pre_gas_admissible >> goal_assum (drule_at Any)) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `_ ==> scoped_operand_outcome _ _ _ _ sa s1 _ _ _ _ /\ _`
    (drule_all_then strip_assume_tac) >>
  rewrite_tac[REWRITE_RULE [ETA_THM] eval_expr_bop_bind] >>
  irule bop_visit_child_bind >>
  qpat_assum `scoped_operand_outcome _ _ _ _ sa s1 _ _ _ _`
    (irule_at Any) >> simp[] >> conj_tac
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
           storage_trace_frame_read_result, storage_trace_frame_def, bop_result_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `E = gas_explicit_sites _ _` SUBST_ALL_TAC >>
  qpat_x_assum `!H0 marks v mid G tn t. _ ==> _`
    (qspecl_then [`H0`,`create_cut_marks (gas_explicit_sites ctx shctx) front`,
                  `v`,`mid`,`G`,`tn`,`t`] mp_tac) >>
  (impl_tac >- (simp[] >> qexistsl [`incoming`,`outgoing`] >> first_assum ACCEPT_TAC)) >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qpat_x_assum `!mid t G tn. _ ==> _`
    (qspecl_then [`mid`,`t`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> simp[])) >> strip_tac >>
  `~t.vs_halted` by fs[expr_sim_full_pre_def] >>
  irule bop_visit_child_bind >>
  qpat_assum `scoped_operand_outcome _ _ _ _ s1 s2 _ _ _ _`
    (irule_at Any) >> simp[] >> conj_tac
  >- simp[storage_trace_frame_def,bop_result_def] >>
  rpt gen_tac >> strip_tac >> irule create_admin_sequence_cut >> simp[] >> conj_tac
  >- fs[EVERY_MEM] >>
  first_x_assum drule >> simp[expr_sim_full_post_def,expr_sim_full_endpoint_def,
    create_operand_at_def]
QED
