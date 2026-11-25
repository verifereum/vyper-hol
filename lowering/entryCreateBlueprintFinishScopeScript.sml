(* Confine the executed blueprint check and append before entering dispatch.
   The runs and all-horizon pointer paths refer to the same branch landings. *)
Theory entryCreateBlueprintFinishScope
Ancestors
  bodyFullCreateHeld entryCreateAdminSequence entryCreatePathScope
  entryCreateFocusSpec entryCreateCompletedCut entryIntCallStageNeutral
  createSizePrefixReplay createSizeItinerary createSizeCutRegion createSizeCutCode
  exprSimFullBundleProps exprSimDefs exprSimSource exprLoweringProps
  builtinCreate vyperCreate vyperState vyperStorageTrace
  fragGasOrigin fragGasOriginPtr fragExec venomInst venomState
  externalEntryShape list arithmetic words

Theorem blueprint_check_abort_scoped[local]:
  storage_trace_domain cx st0 ee.storage_trace /\ create_operand_at sm s /\
  ~s.vs_halted /\
  fn_has_code sm m func /\ m.cs_current_bb = sm.cs_current_bb /\
  m.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm m /\
  EVERY (\i. i.inst_id IN frag_ids sm m /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm m) /\
  run_inst_seq (emitted_insts sm m) s = OK u /\
  z = u with vs_inst_idx := LENGTH m.cs_current_insts /\
  ~create_operand_at sb z /\
  (!v ms w. create_prefix_step sm m E ctx func v ms w ==>
             create_prefix_step sm sb E ctx func v ms w) /\
  gas_origin_edge T E ctx func z [] (Abort Revert_abort t) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (s,G,tn) [] (Abort Revert_abort t,Gabort,tnt)) /\
  (!tail. source (ee with gas_obs := tail) =
    (INR (Error (RuntimeError "create source has no deployable code")),ee with gas_obs := tail)) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sm sb
    source (ee,s,G,tn) Q (create_operand_exit_post ctx cx)
Proof
  strip_tac >>
  `create_operand_full_scope sm m E ctx func s [] (OK z)` by
    (qpat_assum `z = _` SUBST1_TAC >> irule create_admin_sequence_scope >> simp[]) >>
  `create_expr_prefix sm sb E ctx func s [] z` by
    (irule create_expr_prefix_mono >> qexistsl_tac [`sm`,`m`] >>
     fs[create_operand_full_scope_def]) >>
  `create_operand_full_scope sm sb E ctx func s [] (Abort Revert_abort t)` by
    (irule (SIMP_RULE (srw_ss()) []
      (Q.INST [`left` |-> `[]`,`last` |-> `[]`] create_operand_full_scope_terminal)) >>
     simp[exit_result_def] >> qexists_tac `z` >> fs[create_operand_at_def]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR (Error (RuntimeError "create source has no deployable code"))`,
                `ee`,`Abort Revert_abort t`,`Gabort`,`tnt`] >>
  simp[create_operand_exit_post_def,expr_exit_def,halt_exit_def,exit_result_def]
QED

Theorem blueprint_finish_ok_scope[local]:
  fn_has_code sm sn func /\ fn_has_code sn sc func /\
  sn.cs_current_bb = sm.cs_current_bb /\
  sn.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sn /\
  EVERY (\i. i.inst_id IN frag_ids sm sn /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) (emitted_insts sm sn) /\
  sc.cs_current_bb = sn.cs_current_bb /\
  sc.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sc /\
  EVERY (\i. i.inst_id IN frag_ids sn sc /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) (emitted_insts sn sc) /\
  sm.cs_next_id <= sn.cs_next_id /\ sn.cs_next_id <= sc.cs_next_id /\
  (!bb i. lookup_block sc.cs_current_bb func.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH sc.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids sm sn) /\
  create_operand_at sm s /\ ~s.vs_halted /\ ~u.vs_halted /\
  run_inst_seq (emitted_insts sm sn) s = OK raw /\
  u = raw with vs_inst_idx := LENGTH sn.cs_current_insts /\
  run_inst_seq (emitted_insts sn sc) u = OK raw' /\
  t = raw' with vs_inst_idx := LENGTH sc.cs_current_insts ==>
  create_operand_full_scope sm sc E ctx func s [] (OK t)
Proof
  strip_tac >>
  `create_operand_full_scope sm sn E ctx func s [] (OK u)` by
    (qpat_assum `u = _` SUBST1_TAC >> irule create_admin_sequence_scope >> simp[]) >>
  `create_operand_full_scope sn sc E ctx func u [] (OK t)` by
    (qpat_assum `create_operand_full_scope sm sn _ _ _ _ [] (OK u)`
       (strip_assume_tac o REWRITE_RULE[create_operand_full_scope_def]) >>
     qpat_assum `t = _` SUBST1_TAC >> irule create_admin_sequence_scope >> fs[create_operand_at_def]) >>
  irule (SIMP_RULE (srw_ss()) []
      (Q.INST [`left` |-> `[]`,`right` |-> `[]`] create_operand_full_scope_prepend)) >>
  qexistsl_tac [`sn`,`u`] >> simp[]
QED

(* The schematic dispatch rule is at the prepared CREATE cursor, not at
   the start of the check. Its result can be a focus as well as a full run. *)
Theorem blueprint_finish_scoped_from_parts:
  compile_create_blueprint_check lit target off sm = (codep,sn) /\
  compile_create_blueprint_append target amount sop off codep args_ptr cnt rof sn = (result,sb) /\
  fn_has_code sm sb func /\ body_inv (cx_tops cx) ctx cenv cx /\ MEM func ctx.ctx_functions /\
  ctx_has_dalloca ctx /\ fn_inst_ids_distinct func /\
  storage_trace_domain cx st0 ee.storage_trace /\ storage_trace_frame source /\
  stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx es s0 /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  wb_frame cenv es ee sa s0 s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  return_buf_frame d cenv sm s /\ create_operand_at sm s /\ ~s.vs_halted /\
  outcomes_accounts_typed ee.outcomes /\
  eval_operand amount s = SOME aw /\ op_taint tn amount = {} /\
  OPTREL (\op w. eval_operand op s = SOME w /\ op_taint tn op = {}) sop sw /\
  (!x. amount = Var x \/ sop = SOME (Var x) ==> not_fresh_at sm x) /\
  n = blueprint_copy_size (w2n ow) code /\ N = n + LENGTH args /\
  good = (if lit then blueprint_size_ok n else w2n ow < LENGTH code) /\
  initcode = blueprint_initcode n (w2n ow) code args /\
  post_value_type cenv e = BaseT AddressT /\ expr_has_effect e /\
  (!tail. source (ee with gas_obs := tail) =
    if ~good then
      (INR (Error (RuntimeError "create source has no deployable code")),ee with gas_obs := tail)
    else if N > 2 * max_code_size then
      (INR (Error (RuntimeError "create initcode too large")),ee with gas_obs := tail)
    else bind (ignore_bind (check_not_static cx)
      (create_oracle_result sw (w2n aw) initcode rof)) (read_result cx) (ee with gas_obs := tail)) /\
  (if good then
    ?u raw sc p lenop t Gmat tt raw' app.
      run_inst_seq (emitted_insts sm sn) s = OK raw /\
      u = (raw with vs_inst_idx := LENGTH sn.cs_current_insts) /\ ~u.vs_halted /\
      create_blueprint_append_itinerary target off codep args_ptr cnt sn app (Var p) lenop /\
      LAST app = sc /\
      run_inst_seq (emitted_insts sn sc) u = OK raw' /\
      t = (raw' with vs_inst_idx := LENGTH sc.cs_current_insts) /\
      compile_create_dispatch (Var p) lenop amount sop rof sc = (result,sb) /\
      fn_has_code sc sb func /\ cs_extends sm sc /\ sm.cs_next_var <= sc.cs_next_var /\
      (!D E'. gas_origin_ptr_path (D,lo,E',ctx,func,PG) (s,G,tn) [] (OK t,Gmat,tt)) /\
      ~t.vs_halted /\ create_operand_at sc t /\
      (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
                vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>) = s /\
      eval_operand (Var p) t = SOME s.vs_fmp /\ ptr_covers Gmat tt p t N /\
      eval_operand lenop t = SOME (n2w N) /\ op_taint tt (Var p) = {} /\ op_taint tt lenop = {} /\
      N < dimword (:256) /\ w2n t.vs_initial_fmp <= w2n s.vs_fmp /\
      w2n t.vs_fmp = w2n s.vs_fmp + venomLayout$ceil32 N /\
      w2n s.vs_fmp + N <= w2n t.vs_fmp /\ w2n s.vs_fmp + N <= LENGTH t.vs_memory /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\ allocas_below_fmp t /\
      read_memory (w2n s.vs_fmp) N t = initcode /\
      (!j k. j+k <= w2n s.vs_fmp ==> read_memory j k t = read_memory j k s) /\
      (!i. w2n s.vs_fmp <= i /\ i < w2n s.vs_fmp + N ==> i NOTIN tt.t_mem) /\
      (!i. i < w2n s.vs_fmp /\ i IN tt.t_mem ==> i IN tn.t_mem) /\
      tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
      (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP Gmat x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x))
  else
    ?t Gabort tnt pre i raw.
      emitted_insts sm sn = pre ++ [i] /\ run_inst_seq pre s = OK raw /\
      gas_origin_edge T E ctx func
        (raw with vs_inst_idx := LENGTH sm.cs_current_insts + LENGTH pre) [] (Abort Revert_abort t) /\
      (!D E'. gas_origin_ptr_path (D,lo,E',ctx,func,PG) (s,G,tn) [] (Abort Revert_abort t,Gabort,tnt))) /\
  (sn.cs_current_bb = sm.cs_current_bb /\
   sn.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sn /\
   EVERY (\i. i.inst_id IN frag_ids sm sn /\ i.inst_opcode <> INVOKE /\
              i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) (emitted_insts sm sn)) /\
  (!app p lenop. create_blueprint_append_itinerary target off codep args_ptr cnt sn app (Var p) lenop ==>
    (LAST app).cs_current_bb = sn.cs_current_bb /\
    (LAST app).cs_current_insts = sn.cs_current_insts ++ emitted_insts sn (LAST app) /\
    EVERY (\i. i.inst_id IN frag_ids sn (LAST app) /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) (emitted_insts sn (LAST app))) /\
  (!pre i raw. emitted_insts sm sn = pre ++ [i] /\ run_inst_seq pre s = OK raw ==>
    ?m. fn_has_code sm m func /\ m.cs_current_bb = sm.cs_current_bb /\
      m.cs_current_insts = sm.cs_current_insts ++ pre /\ emitted_insts sm m = pre /\
      EVERY (\j. j.inst_id IN frag_ids sm m /\ j.inst_opcode <> INVOKE /\
                 j.inst_opcode <> GAS /\ ~is_terminator j.inst_opcode) pre /\
      ~create_operand_at sb (raw with vs_inst_idx := LENGTH m.cs_current_insts) /\
      (!v ms w. create_prefix_step sm m E ctx func v ms w ==>
                 create_prefix_step sm sb E ctx func v ms w)) /\
  (!sc app p lenop t.
    create_blueprint_append_itinerary target off codep args_ptr cnt sn app (Var p) lenop /\
    LAST app = sc /\ compile_create_dispatch (Var p) lenop amount sop rof sc = (result,sb) /\
    fn_has_code sc sb func /\ create_operand_at sc t /\ ~t.vs_halted ==>
    fn_has_code sn sc func /\ sm.cs_next_id <= sn.cs_next_id /\ sn.cs_next_id <= sc.cs_next_id /\
    sc.cs_next_id <= sb.cs_next_id /\
    (!bb i. lookup_block sc.cs_current_bb func.fn_blocks = SOME bb /\
            get_instruction bb (LENGTH sc.cs_current_insts) = SOME i ==>
            i.inst_id NOTIN frag_ids sm sn) /\
    (!bb i. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
            get_instruction bb (LENGTH sb.cs_current_insts) = SOME i ==>
            i.inst_id NOTIN frag_ids sm sc) /\
    create_cut_code {} sc sb /\ create_cut_region sc sb t /\ ~create_operand_at sb t) /\
  (!sc p lenop t Gmat tt pv sz.
    compile_create_dispatch (Var p) lenop amount sop rof sc = (result,sb) /\
    fn_has_code sc sb func /\ ~create_operand_at sb t /\
    local_ptrs_reserved cenv sc /\ sa.cs_next_var <= sc.cs_next_var /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sc x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sc x) /\
    ~t.vs_halted /\ create_operand_at sc t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee Gmat tt t) /\
    wb_frame cenv es ee sa s0 t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gmat tt /\
    eval_operand (Var p) t = SOME pv /\ eval_operand lenop t = SOME sz /\
    (sz <> 0w ==> ptr_covers Gmat tt p t (w2n sz)) /\
    (sz <> 0w ==> w2n pv + w2n sz <= t.vs_alloca_next \/
      (ctx_has_dalloca ctx /\ w2n t.vs_initial_fmp <= w2n pv /\ w2n pv + w2n sz <= w2n t.vs_fmp)) /\
    read_memory (w2n pv) (w2n sz) t = initcode /\
    (!i. w2n pv <= i /\ i < w2n pv + w2n sz ==> i NOTIN tt.t_mem) /\
    op_taint tt (Var p) = {} /\ op_taint tt lenop = {} /\
    eval_operand amount t = SOME aw /\ op_taint tt amount = {} /\
    (case sop of NONE => sw = NONE | SOME op =>
       ?w. sw = SOME w /\ eval_operand op t = SOME w /\ op_taint tt op = {}) /\
    (!tail. source (ee with gas_obs := tail) =
      if w2n sz > 2 * max_code_size then
        (INR (Error (RuntimeError "create initcode too large")),ee with gas_obs := tail)
      else bind (ignore_bind (check_not_static cx)
        (create_oracle_result sw (w2n aw) initcode rof)) (read_result cx) (ee with gas_obs := tail)) ==>
    scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sc sb source (ee,t,Gmat,tt)
      (expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sb,s0,result,G0,tn0))
      (create_operand_exit_post ctx cx)) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sm sb source (ee,s,G,tn)
    (expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sb,s0,result,G0,tn0))
    (create_operand_exit_post ctx cx)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `good`
  >- (qpat_x_assum `if T then _ else _` (strip_assume_tac o PURE_REWRITE_RULE[COND_CLAUSES]) >>
      qpat_x_assum `!tail. source _ = _` (assume_tac o PURE_REWRITE_RULE[NOT_CLAUSES,COND_CLAUSES]) >>
      suspend "ok") >>
  qpat_x_assum `if F then _ else _` (strip_assume_tac o PURE_REWRITE_RULE[COND_CLAUSES]) >>
  qpat_x_assum `!tail. source _ = _` (assume_tac o PURE_REWRITE_RULE[NOT_CLAUSES,COND_CLAUSES]) >>
  suspend "abort"
QED

Resume blueprint_finish_scoped_from_parts[ok]:
  `fn_has_code sm sn func` by
    (irule (cj 1 (REWRITE_RULE[IMP_CONJ_THM,FORALL_AND_THM] (SPEC_ALL fn_has_code_split))) >>
     first_assum (irule_at Any) >>
     metis_tac[compile_create_blueprint_check_labels,compile_create_blueprint_append_labels,pairTheory.SND]) >>
  qpat_assum `!app p lenop. _ ==> (LAST app).cs_current_bb = _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!sc app p lenop t. _ ==> fn_has_code sn sc func /\ _`
    (drule_all_then (map_every assume_tac o CONJUNCTS)) >>
  `create_operand_full_scope sm sc E ctx func s [] (OK t)` by
    (irule blueprint_finish_ok_scope >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`raw`,`raw'`,`sn`,`u`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `LAST app = sc` (once_rewrite_tac o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!D E'. gas_origin_ptr_path _ _ _ (OK t,Gmat,tt)`
    (qspecl_then [`DF (storage_trace_horizon ee.storage_trace)`,`E`] assume_tac) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) create_blueprint_finish_dispatch_inputs >>
  `w2n (n2w N:bytes32) = N` by simp[wordsTheory.w2n_n2w,LESS_MOD] >>
  irule stage_scoped_zero_prefix >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists_tac `cenv` >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Gmat`,`sc`,`t`,`tt`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- simp[]
  >- decide_tac >>
  qpat_assum `!sc p lenop t Gmat tt pv sz. _ ==> scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (qspecl_then [`sc`,`p`,`lenop`,`t`,`Gmat`,`tt`,`s.vs_fmp`,`n2w N:bytes32`] mp_tac) >>
  impl_tac >-
    (qpat_assum `w2n (n2w N:bytes32) = N` (pure_rewrite_tac o single) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     strip_tac >> simp[IgnAsm `N = _`, IgnAsm `n = _`, IgnAsm `T = _`, ADD_COMM]) >>
  disch_then ACCEPT_TAC
QED

Resume blueprint_finish_scoped_from_parts[abort]:
  qpat_assum `!pre i raw. _ ==> ?m. _` (drule_all_then strip_assume_tac) >>
  irule blueprint_check_abort_scoped >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Gabort`,`m`,`t`,`tnt`,`raw`,`raw with vs_inst_idx := LENGTH m.cs_current_insts`] >>
  qpat_x_assum `F = (if lit then _ else _)` kall_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[] >>
  pure_once_rewrite_tac[ADD_COMM] >> first_assum ACCEPT_TAC
QED

Finalise blueprint_finish_scoped_from_parts
