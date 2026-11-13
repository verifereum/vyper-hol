Theory typedOperandsPtr
Ancestors
  wordOperandsPtr bodyPtrPreds exprSimPrecompiles gasSummaryComposePtr
  gasSummaryComposePtrAll gasOutcomeMarkedPtr gasOutcomeMapPtr
  gasStorage vyperStorageTrace vyperStorageFootprint stmtSimProps vyperState list

(* A recursive readiness interface is needed because facts about later
   operands are available only when the preceding operand can evaluate.
   This mirrors typed_args_ready, without assuming ghost-state existence. *)
Definition typed_args_ready_ptr_def:
  typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv [] = T /\
  typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv (e::args) =
    ((!es. Inv es ==>
       expr_sim_ptr d ctx PG func cenv cx (arg_ty e) e es /\
       is_word_type (expr_type e) /\
       IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
       (!res es'. (do r <- eval_expr cx e; read_result cx r od) es = (res, es') ==> expr_res_ok res) /\
       (!v es'. (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
         Inv es')) /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv args))
End

Theorem typed_args_ready_ptr_head:
  typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv (e::args) /\ Inv es ==>
    expr_sim_ptr d ctx PG func cenv cx (arg_ty e) e es /\
    is_word_type (expr_type e) /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
    (!res es'. (do r <- eval_expr cx e; read_result cx r od) es = (res, es') ==> expr_res_ok res) /\
    (!v es'. (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==> Inv es')
Proof
  simp[typed_args_ready_ptr_def] >> metis_tac[]
QED

Theorem typed_args_ready_ptr_tail:
  typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv (e::args) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) ==>
  typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv args
Proof
  simp[typed_args_ready_ptr_def, bind_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem body_exprs_typed_args_ready_ptr:
  body_exprs_ptr_ok cx args /\
  typed_args_ready ctx func cenv cx arg_ty Inv args /\
  body_inv tops ctx cenv cx /\
  (!e es. MEM e args /\ Inv es ==> expr_body_pre cenv cx env e es) ==>
  typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv args
Proof
  Induct_on `args`
  >- simp[typed_args_ready_ptr_def] >>
  simp_tac pure_ss [typed_args_ready_ptr_def, typed_args_ready_def,
    body_exprs_ptr_ok_def, MEM] >> gen_tac >> strip_tac >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      fs[body_expr_ptr_ok_def] >> metis_tac[]) >>
  strip_tac >> first_x_assum irule >> metis_tac[]
QED

Theorem typed_args_post_cons_ptr:
  expr_post H ctx func cenv cx e es sa s1 s0 es1 v x t /\
  typed_args_post H ctx func cenv cx es1 s1 t es' args xs vs u /\
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv es1 s1 G1 tn1 t G2 tn2 /\
  op_taint tn1 x = {} /\ EVERY (\z. op_taint tn2 z = {}) xs ==>
  typed_args_post H ctx func cenv cx es sa s0 es' (e::args) (x::xs) (v::vs) u /\
  EVERY (\z. op_taint tn2 z = {}) (x::xs) /\
  ghost_kept cenv es sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >> conj_tac
  >- (irule typed_args_post_cons >> metis_tac[]) >>
  conj_tac
  >- (Cases_on `x` >> gvs[ptrDisciplineTheory.op_taint_def,
        bodyPtrDefsTheory.ghost_kept_def] >> metis_tac[]) >>
  irule ghost_kept_trans >>
  drule exprSimWordArgsTheory.expr_post_frame >> strip_tac >>
  fs[exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  metis_tac[]
QED

Theorem lower_typed_args_nil_sim_ptr:
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv H d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (\H. cx_dead H cx) (cx_tops cx) (ctx, func) PG cx st0
    (eval_exprs cx []) (es, s0, G0, tn0)
    (\H rr ee G tn t. ?vs. rr = INL vs /\
       typed_args_post H ctx func cenv cx es sa s0 ee [] [] vs t /\
       MAP FDOM es.scopes = MAP FDOM ee.scopes /\
       t.vs_current_bb = sa.cs_current_bb /\
       t.vs_inst_idx = LENGTH sa.cs_current_insts /\
       ghost_inv H d cenv cx ee G tn t /\
       EVERY (\x. op_taint tn x = {}) [] /\
       ghost_kept cenv es sa G0 tn0 s0 G tn)
    (\H rr ee gt r. wb_args_exit rr r)
Proof
  strip_tac >>
  simp[fragGasPathPtrTheory.gas_outcome_ptr_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  simp[fragGasPathPtrTheory.gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL []`, `es`, `G0`, `tn0`, `OK s0`] >>
  simp[exprSimWordArgsTheory.eval_exprs_nil, return_def,
       gasSummaryTheory.gas_explicit_def,
       fragGasPathPtrTheory.gas_path_ptr_rules,
       typed_args_post_def, loweringPostsTheory.wb_frame_def,
       bodyPtrDefsTheory.ghost_kept_def, stmtFragPtrTheory.ghost_inv_gas_obs] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
      `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
        (`(es with gas_obs := []).accounts = es.accounts /\
          (es with gas_obs := []).tStorage = es.tStorage` by simp[] >>
         metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends]) >>
  fs[exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_gas_obs,
     vyperStorageFootprintTheory.storage_well_formed_on_def, vyperStorageBackendTheory.get_storage_def]
QED

Theorem typed_args_ready_ptr_admissible:
  typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!ee gs. Inv ee ==> Inv (ee with gas_obs := gs)) ==>
  gas_admissible (do r <- eval_expr cx e; read_result cx r od) expr_res_ok es
Proof
  simp[gasContextTheory.gas_admissible_def, typed_args_ready_ptr_def] >>
  metis_tac[]
QED

Theorem typed_args_ready_ptr_marked_facts:
  typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!ee gs. Inv ee ==> Inv (ee with gas_obs := gs)) /\
  gas_marked_exec F (ctx,func)
    (do r <- eval_expr cx e; read_result cx r od) (es,s0) marks (INL v) mid r ==>
  Inv (mid with gas_obs := []) /\
  typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv args /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  strip_tac >>
  `(do r <- eval_expr cx e; read_result cx r od)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, mid with gas_obs := [])` by
    (fs[gasSummaryTheory.gas_marked_exec_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[combinTheory.o_DEF]) >>
  `Inv (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[] >>
  drule_all typed_args_ready_ptr_head >> strip_tac >>
  drule typed_args_ready_ptr_tail >>
  drule exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom >>
  simp[] >> metis_tac[]
QED

Theorem forced_eval_bind_action[local]:
  monad_bind (eval_expr cx e) (read_result cx) =
    (do r <- eval_expr cx e; read_result cx r od)
Proof
  simp[FUN_EQ_THM, bind_def]
QED

Theorem operand_path_not_halted[local]:
  !ctx fn s n r. gas_path ctx fn s n r ==> !t. r = OK t ==> ~t.vs_halted
Proof
  Induct_on `gas_path` >> rw[] >> gvs[fragExecTheory.exit_result_def]
QED

Theorem operand_marked_exec_not_halted[local]:
  gas_marked_exec F (ctx,func) source (es,s0) marks res ee (OK t) ==>
  ~t.vs_halted
Proof
  simp[gasSummaryTheory.gas_marked_exec_def,
    fragGasModeTheory.gas_marked_path_def] >>
  metis_tac[operand_path_not_halted]
QED

Theorem typed_args_head_outcome_ptr[local]:
  typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!ee gs. Inv ee ==> Inv (ee with gas_obs := gs)) /\
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0
    (do r <- eval_expr cx e; read_result cx r od) (es,s0,G0,tn0) Q R /\
  (!H res ee G tn t. Q H res ee G tn t ==> ?v. res = INL v) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0
    (do r <- eval_expr cx e; read_result cx r od) (es,s0,G0,tn0)
    (\H res ee G tn t. Q H res ee G tn t /\ ~t.vs_halted /\ Inv ee /\
      typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv args /\
      MAP FDOM es.scopes = MAP FDOM ee.scopes) R
Proof
  strip_tac >> irule gas_outcome_ptr_marked_conseq >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!H res ee G tn t. Q H res ee G tn t ==> _`
    (drule_then strip_assume_tac) >> gvs[] >>
  drule gas_marked_exec_ptr_exec >> strip_tac >>
  drule_all typed_args_ready_ptr_marked_facts >>
  drule operand_marked_exec_not_halted >> simp[]
QED

Theorem lower_typed_args_sim_ptr:
  !args ctx func cenv cx st0 arg_ty Inv es sa xs sb s0 G0 tn0.
    typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv args /\ Inv es /\
    (!es gs. Inv es ==> Inv (es with gas_obs := gs)) /\
    wb_args_shape cenv arg_ty args /\
    lower_word_args cenv arg_ty args sa = (xs,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv H d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
     ~ctx_has_dalloca ctx /\
    ~cenv.ce_is_ctor /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
    gas_outcome_ptr (\H. cx_dead H cx) (cx_tops cx) (ctx,func) PG cx st0
      (eval_exprs cx args) (es,s0,G0,tn0)
      (\H rr ee G tn t. ?vs. rr = INL vs /\
        typed_args_post H ctx func cenv cx es sa s0 ee args xs vs t /\
        MAP FDOM es.scopes = MAP FDOM ee.scopes /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        ghost_inv H d cenv cx ee G tn t /\
        EVERY (\x. op_taint tn x = {}) xs /\
        ghost_kept cenv es sa G0 tn0 s0 G tn)
      (\H rr ee gt r. wb_args_exit rr r)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[exprSimWordArgsTheory.lower_word_args_nil] >>
      drule_all lower_typed_args_nil_sim_ptr >> simp[]) >>
  gvs[exprSimWordArgsTheory.lower_word_args_cons] >>
  rename1 `lower_value compile_expr cenv (arg_ty h) h sa = (x,s1)` >>
  drule_all typed_args_ready_ptr_head >> strip_tac >>
  drule_all typed_args_ready_ptr_admissible >> strip_tac >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
   sa.cs_next_id <= s1.cs_next_id /\
   (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l)` by
    (fs[exprSimWordArgsTheory.wb_args_shape_def] >> metis_tac[]) >>
  `wb_args_shape cenv arg_ty args` by
    metis_tac[exprSimWordArgsTheory.wb_args_shape_tail] >>
  drule_all exprSimWordArgsTheory.lower_word_args_shape_ready >> strip_tac >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac pure_ss [bodyPtrDefsTheory.expr_sim_ptr_def, forced_eval_bind_action] >>
  disch_then (drule_all_then assume_tac) >>
  drule typed_args_head_outcome_ptr >>
  disch_then (drule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  disch_then assume_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _ (\H res ee G tn t. ?v. _) _` kall_tac >>
  rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action, forced_eval_bind_action] >>
  irule gas_outcome_ptr_bind_all >>
  first_assum (irule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _ _ _`)) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_return] >> rpt conj_tac
  >- suspend "tail_cert"
  >- suspend "head_cert"
  >- suspend "head_bind"
  >- (rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> Cases_on `res` >>
  fs[exprSimWordArgsTheory.wb_args_exit_def] >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type]

QED

Resume lower_typed_args_sim_ptr[head_bind]:
  qx_genl_tac [`left`, `v`, `mid`, `t`, `G1`, `tn1`] >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` drule >>
  strip_tac >> gvs[] >>
  `local_ptrs_reserved cenv s1` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z)` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     expr_post H ctx func cenv cx h es sa s1 s0
       (mid with gas_obs := []) v x t /\
     stmt_state_rel H ctx func cenv cx es s0` by
    (qx_gen_tac `H1` >> disch_tac >>
     `valid_horizon cx st0 H1 es.storage_trace` by
       (drule gas_marked_exec_valid_prefix >>
        simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
             storage_trace_frame_read_result] >> metis_tac[]) >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `H1` mp_tac) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H1` mp_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H (mid with gas_obs := []).storage_trace ==>
     stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) t /\
     storage_well_formed_on cx (mid with gas_obs := []) (FST H) /\
     ghost_inv H d cenv cx (mid with gas_obs := []) G1 tn1 t` by
    (qx_gen_tac `H1` >> disch_tac >>
     `valid_horizon cx st0 H1 mid.storage_trace` by fs[] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H1` mp_tac) >> simp[] >> strip_tac >>
     fs[loweringPostsTheory.expr_post_def]) >>
  qpat_x_assum `!ctx func cenv cx st0 arg_ty Inv es sa xs sb s0 G0 tn0. _`
    (drule_all_then assume_tac) >>
  qmatch_assum_abbrev_tac
    `gas_outcome_ptr _ _ _ _ _ _ (eval_exprs cx args) _ TailQ TailR` >>
  `gas_outcome_ptr (\H. cx_dead H cx) (cx_tops cx) (ctx,func) PG cx st0
     (eval_exprs cx args) (mid with gas_obs := [],t,G1,tn1)
     (\H res ee G tn u. TailQ H res ee G tn u /\
       valid_horizon cx st0 H mid.storage_trace) TailR` by
    (irule gasOutcomeMarkedPtrTheory.gas_outcome_ptr_marked_conseq >>
     goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
     drule gas_marked_exec_ptr_exec >> strip_tac >>
     drule gas_marked_exec_valid_prefix >>
     simp[evaluate_storage_trace_frame] >> metis_tac[]) >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _ TailQ TailR` kall_tac >>
  irule gas_outcome_ptr_map_return >>
  first_assum (irule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _ _ _`)) >>
  conj_tac
  >- suspend "tail_post" >>
  simp[exprSimWordArgsTheory.wb_args_exit_def] >>
  rpt strip_tac >> Cases_on `res` >> gvs[Abbr`TailR`, exprSimWordArgsTheory.wb_args_exit_def]
QED

Resume lower_typed_args_sim_ptr[tail_post]:
  qx_genl_tac [`H2`, `rr`, `ee`, `G2`, `tn2`, `u`] >>
  strip_tac >> gvs[Abbr`TailQ`] >>
  Cases_on `evaluate_type (get_tenv cx) (expr_type h)` >> gvs[] >>
  fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
    expr_post H ctx func cenv cx h es sa s1 s0
      (mid with gas_obs := []) v x t /\ _`
    (qspec_then `H2` (drule_then strip_assume_tac)) >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by simp[] >>
  drule_all typed_args_post_cons_ptr >> simp[]
QED

Resume lower_typed_args_sim_ptr[tail_cert]:
  POP_ASSUM_LIST (K all_tac) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rewrite_tac[ignore_bind_map_return, GSYM forced_eval_bind_action,
    GSYM exprSimWordArgsTheory.eval_exprs_cons_ignore_action] >>
  rpt strip_tac >> irule exprSimWordArgsTheory.wb_args_tail_exempt_cert >>
  goal_assum (drule_at Any) >>
  qexists_tac `v` >> fs[forced_eval_bind_action]
QED

Resume lower_typed_args_sim_ptr[head_cert]:
  POP_ASSUM_LIST (K all_tac) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rewrite_tac[ignore_bind_map_return, GSYM forced_eval_bind_action,
    GSYM exprSimWordArgsTheory.eval_exprs_cons_ignore_action] >>
  metis_tac[exprSimWordArgsTheory.wb_args_head_exempt_cert]
QED

Finalise lower_typed_args_sim_ptr
