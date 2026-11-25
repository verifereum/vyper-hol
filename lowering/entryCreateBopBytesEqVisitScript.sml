(* A comparison visit belongs to one of the two operand bands or to the
   non-invoking comparison suffix, without a success premise on that suffix. *)
Theory entryCreateBopBytesEqVisit
Ancestors
  entryCreateReplayBind entryCreateNativeFirstExit entryCreateAdminSequence
  entryCreateFocusSpec entryCreateCompletedCut createExprSizeExitDefs
  exprBopSimProps exprBopSimDefs exprSimFullBundleProps s1PrefixDefs
  bodyFullIfExpReach gasSummary gasExplicitSites fragGasOriginPtrExec fragExec
  vyperStorageTrace vyperStorageFootprint vyperState vyperInterpreter venomExecSemantics

Overload read_operand[local] = ``\cx e. bind (eval_expr cx e) (read_result cx)``

(* Keep a single equation for the actual replay query. In particular, the
   successful source state here is normalized only after noting its tail. *)
Theorem operand_replay_source_equation[local]:
  gas_completed_operand (DF,lo,E,C,f,PG) tops cx st a m source (es,s,G,tn) Q ==>
  gas_completed_operand (DF,lo,E,C,f,PG) tops cx st a m source (es,s,G,tn)
    (\H r mid G1 tn1 t. Q H r mid G1 tn1 t /\
       (?incoming outgoing. source (es with gas_obs := incoming) =
                              (r,mid with gas_obs := outgoing)))
Proof
  simp_tac (srw_ss()) [gas_completed_operand_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum drule_all >> strip_tac
  >- (disj1_tac >> qexistsl_tac [`G'`,`tn'`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >> simp[] >> strip_tac >>
      qexistsl_tac [`gas_explicit marks s.vs_gas_readings ++ tail`,`tail`] >>
      gvs[evaluation_state_component_equality]) >>
  metis_tac[]
QED

Theorem bytes_eq_visit_bind[local]:
  body_inv (cx_tops cx) C ce cx /\ MEM f C.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\ ~s.vs_halted /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) (cx_tops cx) cx st a m
    (read_operand cx e) (es,s,G,tn)
    (expr_sim_full_post (DF,lo,d,C,f) ce cx e (es,a,m,s,x,G,tn))
    (create_operand_exit_post C cx) /\
  create_operand_cut a m E C f (cx_tops cx) cx st (read_operand cx e) (es,s) /\
  (!v. storage_trace_frame (next v)) /\
  (!H0 marks v mid G1 tn1 t.
    valid_horizon cx st H0 mid.storage_trace /\ mid.gas_obs = [] /\
    (?incoming outgoing. read_operand cx e (es with gas_obs := incoming) =
                             (INL v,mid with gas_obs := outgoing)) /\
    create_operand_at m t /\ ~t.vs_halted /\
    (!H. valid_horizon cx st H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) marks (OK t,G1,tn1) /\
      expr_sim_full_post (DF,lo,d,C,f) ce cx e (es,a,m,s,x,G,tn) H (INL v) mid G1 tn1 t) ==>
    create_operand_cut m b E C f (cx_tops cx) cx st (next v) (mid,t)) ==>
  create_operand_cut a b E C f (cx_tops cx) cx st (bind (read_operand cx e) next) (es,s)
Proof
  strip_tac >>
  `!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (gen_tac >> strip_tac >> irule body_inv_no_phi >> simp[] >> metis_tac[]) >>
  drule_all scoped_outcome_completed_operand >> strip_tac >>
  drule operand_replay_source_equation >> strip_tac >>
  irule create_operand_cut_bind_replay >>
  qpat_assum `gas_completed_operand _ _ _ _ _ _ _ _ (\H r mid G1 tn1 t. _)` (irule_at Any) >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> drule_all create_interior_visit_first_exit >> metis_tac[])
  >- (qx_genl_tac [`H0`,`front`,`v`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
      `~t.vs_halted` by (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
      `create_operand_at m t` by
        fs[expr_sim_full_post_def,expr_sim_full_endpoint_def,create_operand_at_def] >>
      qpat_assum `!H0 marks v mid G1 tn1 t. _ ==> _`
        (qspecl_then [`H0`,`create_cut_marks E front`,`v`,`mid with gas_obs := []`,`G1`,`tn1`,`t`] mp_tac) >>
      simp[] >> (impl_tac >- (conj_tac >- (qexistsl_tac [`incoming`,`outgoing`] >> simp[]) >>
        qx_gen_tac `h` >>
        qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `h` mp_tac) >>
        rpt (pop_assum kall_tac) >> simp[expr_sim_full_post_def] >> metis_tac[])) >> simp[]) >>
  rpt gen_tac >> simp[expr_sim_full_post_def] >> strip_tac >> goal_assum (drule_at Any)
QED

Theorem create_bop_bytes_eq_visit:
  let E = gas_explicit_sites C shC in
  let P1 = expr_sim_full_post (DF,lo,d,C,f) ce cx e1 (es,a,m,s,x,G,tn) in
  body_inv (cx_tops cx) C ce cx /\ MEM f C.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\
  create_cut_code {} m n /\ fn_has_code m n f /\
  create_cut_code {} n b /\ fn_has_code n b f /\
  b.cs_current_bb = n.cs_current_bb /\ b.cs_current_insts = n.cs_current_insts ++ emitted_insts n b /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts n b) /\
  ~s.vs_halted /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) (cx_tops cx) cx st a m
       (read_operand cx e1) (es,s,G,tn) P1 (create_operand_exit_post C cx) /\
  create_operand_cut a m E C f (cx_tops cx) cx st (read_operand cx e1) (es,s) /\
  (!H0 marks v mid G1 tn1 t.
    valid_horizon cx st H0 mid.storage_trace /\ mid.gas_obs = [] /\
    (?incoming outgoing. read_operand cx e1 (es with gas_obs := incoming) =
                             (INL v,mid with gas_obs := outgoing)) /\
    (!H. valid_horizon cx st H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) marks (OK t,G1,tn1) /\
      P1 H (INL v) mid G1 tn1 t) ==>
    expr_body_pre ce cx env e2 mid /\ body_const_cells_agree [(NONE,cx_tops cx)] cx env mid /\
    (?p tv q p' v' q'. eval_expr cx e1 p = (INL tv,q) /\
                       read_result cx tv p' = (INL v',q')) /\
    expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx (expr_type e1) e2 mid
      (st,m,n,shm,shn,y,t,G1,tn1)) /\
  (!mid t G1 tn1.
    expr_body_pre ce cx env e2 mid /\ body_const_cells_agree [(NONE,cx_tops cx)] cx env mid /\
    (?p tv q p' v' q'. eval_expr cx e1 p = (INL tv,q) /\
                       read_result cx tv p' = (INL v',q')) /\
    expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx (expr_type e1) e2 mid
      (st,m,n,shm,shn,y,t,G1,tn1) ==>
    scoped_operand_outcome (DF,lo,E,C,f,PG) (cx_tops cx) cx st m n
      (read_operand cx e2) (mid,t,G1,tn1)
      (expr_sim_full_post (DF,lo,d,C,f) ce cx e2 (mid,m,n,t,y,G1,tn1))
      (create_operand_exit_post C cx) /\
    create_operand_cut m n E C f (cx_tops cx) cx st (read_operand cx e2) (mid,t)) ==>
  create_operand_cut a b E C f (cx_tops cx) cx st
    (read_operand cx (Builtin ann (Bop bop) [e1;e2])) (es,s)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
  irule bytes_eq_visit_bind >>
  qpat_assum `scoped_operand_outcome _ _ _ _ a m _ _ _ _` (irule_at Any) >> simp[] >>
  conj_tac
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
           storage_trace_frame_read_result,storage_trace_frame_def,bop_result_def]) >>
  qx_genl_tac [`H0`,`marks`,`v`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  qpat_assum `!H0 marks v mid G1 tn1 t. _ ==> _`
    (qspecl_then [`H0`,`marks`,`v`,`mid`,`G1`,`tn1`,`t`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac
    >- (qexistsl_tac [`incoming`,`outgoing`] >> simp[]) >>
    qx_gen_tac `h` >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `h` mp_tac) >>
    rpt (pop_assum kall_tac) >> simp[expr_sim_full_post_def] >> metis_tac[])) >>
  strip_tac >>
  qpat_assum `!mid t G1 tn1. _ ==> _`
    (qspecl_then [`mid`,`t`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- (simp[] >> goal_assum (drule_at Any) >> metis_tac[])) >>
  strip_tac >>
  irule bytes_eq_visit_bind >>
  qpat_assum `scoped_operand_outcome _ _ _ _ m n _ _ _ _` (irule_at Any) >> simp[] >>
  conj_tac >- simp[storage_trace_frame_def,bop_result_def] >>
  rpt gen_tac >> strip_tac >> irule create_admin_sequence_cut >> simp[]
QED
