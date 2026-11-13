(* Memory simulation composition for EC arithmetic, on the finite-storage
   horizon interface: the posts are indexed by a horizon H and hold for every
   horizon valid for the final storage trace. *)
Theory bodyMemEcArithSimulation
Ancestors
  bodyMemEcArithCompose bodyMemEcArithPaths exprSimCalldataSlice
  bodyExprForceMemory gasOutcome gasSummary exprSimECArith
  exprSimMemDefs fragExec compileEnv exprSimDefs exprLoweringProps
  bodyMemTbEmptyMemory exprSimWordArgs exprSimProps loweringPosts
  gasStorage vyperStorageTrace vyperStorageFootprint

(* Instantiate a guarded assumption `!H. valid_horizon .. H tr ==> X` at h,
   discharging the validity premise from an assumption, and strip X. *)
fun at_horizon pat h =
  qpat_assum pat (qspec_then h mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac;

(* ec_source_tail never touches the storage trace, so it is a trace frame. *)
Theorem ec_source_tail_storage_frame[local]:
  storage_trace_frame (ec_source_tail cx ann bt tys vs)
Proof
  `!v. storage_trace_frame
         (do precompile_call_success bt; return (Value v) od)` by
    (gen_tac >> irule storage_trace_frame_ignore_bind >>
     simp[storage_trace_frame_precompile_call_success,
          storage_trace_frame_return]) >>
  rewrite_tac[storage_trace_frame_def] >> rpt gen_tac >>
  rewrite_tac[ec_source_tail_def] >> simp[] >>
  Cases_on `exprSimWordArgs$builtin_result cx st.accounts ann bt tys vs` >>
  simp[] >> fs[storage_trace_frame_def]
QED

Theorem ec_source_tail_trace[local]:
  (bt = ECAdd \/ bt = ECMul) /\
  ec_source_tail cx ann bt tys vs es = (r,es') ==>
  es'.storage_trace = es.storage_trace
Proof
  rpt strip_tac >> gvs[ec_source_tail_cases, AllCaseEqs()]
QED

Theorem ec_two_operand_post[local]:
  lower_value compile_expr cenv (expr_type a) a sa = (p,s1) /\
  lower_value compile_expr cenv (expr_type b) b s1 = (q,sm) /\
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  expr_post H ctx func cenv cx a es sa s1 s0 es1 v1 p t /\
  expr_post H ctx func cenv cx b es1 s1 sm t es2 v2 q u /\
  MAP FDOM es.scopes = MAP FDOM es2.scopes /\
  MAP FDOM es1.scopes = MAP FDOM es2.scopes /\
  (~expr_has_effect e ==> ~expr_has_effect a /\ ~expr_has_effect b) /\
  vv_post H ctx func cenv cx e es2 sm sb u ee tv vv t' ==>
  vv_post H ctx func cenv cx e es sa sb s0 ee tv vv t'
Proof
  strip_tac >>
  `sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
   s1.cs_next_var <= sm.cs_next_var /\ s1.cs_next_id <= sm.cs_next_id` by
    metis_tac[cj 2 compile_expr_grows] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    decide_tac >>
  `wb_frame cenv es es1 sa s0 t /\ wb_frame cenv es1 es2 s1 t u` by
    metis_tac[expr_post_frame] >>
  `wb_frame cenv es es2 sa s0 u` by
    (irule wb_frame_trans >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[expr_post_frame]) >>
  `~expr_has_effect e ==> pure_frame cenv func es sa s0 u` by
    (strip_tac >> fs[] >>
     `pure_frame cenv func es sa s0 t /\ pure_frame cenv func es1 s1 t u` by
       metis_tac[expr_post_pure_frame] >>
     match_mp_tac pure_frame_trans >>
     qexistsl_tac [`es1`, `s1`, `t`] >> fs[wb_frame_def]) >>
  irule vv_post_prefix_frame >> rpt conj_tac >- simp[] >- simp[] >>
  qexistsl_tac [`es2`, `sm`, `u`] >> simp[]
QED

(* The tail from the operand end state: the counted target path is fixed by
   one valid horizon; the posts are then read off per horizon, the endpoint
   being determined by the (horizon-free) execution of the emitted code. *)
Theorem ec_tail_lift_mem[local]:
  (bt = ECAdd \/ bt = ECMul) /\
  lower_value compile_expr cenv (expr_type a) a sa = (p,s1) /\
  lower_value compile_expr cenv (expr_type b) b s1 = (q,sm) /\
  local_ptrs_reserved cenv sa /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\
  (!H. valid_horizon cx st0 H es2.storage_trace ==>
     valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es2.storage_trace ==>
     expr_post H ctx func cenv cx a es sa s1 s0 es1 v1 p t /\
     expr_post H ctx func cenv cx b es1 s1 sm t es2 v2 q u /\
     stmt_state_rel H ctx func cenv cx es2 u) /\
  valid_horizon cx st0 H0 es2.storage_trace /\
  MAP FDOM es.scopes = MAP FDOM es2.scopes /\
  MAP FDOM es1.scopes = MAP FDOM es2.scopes /\
  (~expr_has_effect e ==> ~expr_has_effect a /\ ~expr_has_effect b) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  ec_source_tail cx ann bt tys vs es2 = (res,ee) /\
  (!H. valid_horizon cx st0 H es2.storage_trace ==>
     ?n k. gas_marked_path T ctx func u n k /\
       ((?t0 tv.
           k = OK (t0 with vs_inst_idx := LENGTH sb.cs_current_insts) /\
           run_inst_seq (emitted_insts sm sb) u = OK t0 /\ res = INL tv /\
           vv_post H ctx func cenv cx e es2 sm sb u ee tv
             (FST (as_ptr_val ty LocMemory (op,sb)))
             (t0 with vs_inst_idx := LENGTH sb.cs_current_insts) /\
           vv_store_bound cx ty lt ee tv
             (FST (as_ptr_val ty LocMemory (op,sb)))
             (t0 with vs_inst_idx := LENGTH sb.cs_current_insts) /\
           (t0 with vs_inst_idx := LENGTH sb.cs_current_insts).vs_current_bb =
             sb.cs_current_bb /\
           (t0 with vs_inst_idx := LENGTH sb.cs_current_insts).vs_inst_idx =
             LENGTH sb.cs_current_insts /\
           alloca_history func
             (t0 with vs_inst_idx := LENGTH sb.cs_current_insts) /\
           u.vs_alloca_next <=
             (t0 with vs_inst_idx := LENGTH sb.cs_current_insts).vs_alloca_next) \/
        (exit_result k /\ expr_exit res k))) ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0 (ec_source_tail cx ann bt tys vs) (es2,u)
    (\H r ee' t'. ?tv. r = INL tv /\
       vv_post H ctx func cenv cx e es sa sb s0 ee' tv
         (FST (as_ptr_val ty LocMemory (op,sb))) t' /\
       vv_store_bound cx ty lt ee' tv
         (FST (as_ptr_val ty LocMemory (op,sb))) t' /\
       t'.vs_current_bb = sb.cs_current_bb /\
       t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func t' /\ s0.vs_alloca_next <= t'.vs_alloca_next)
    (\H r ee' k'. expr_exit r k')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ee.storage_trace = es2.storage_trace` by
    (irule ec_source_tail_trace >> metis_tac[]) >>
  `!g. ec_source_tail cx ann bt tys vs (es2 with gas_obs := g) =
       (res, ee with gas_obs := g)` by
    (gen_tac >> irule ec_source_tail_gas_obs >> metis_tac[]) >>
  `!n k. gas_marked_path T ctx func u n k ==>
     gas_marked_exec T (ctx,func) (ec_source_tail cx ann bt tys vs) (es2,u)
       (REPLICATE n F) res ee k` by
    (rpt strip_tac >> irule gas_marked_exec_no_source_read >> conj_tac
     >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC) >>
  `!H t0 tv. valid_horizon cx st0 H es2.storage_trace /\
       run_inst_seq (emitted_insts sm sb) u = OK t0 /\ res = INL tv ==>
     vv_post H ctx func cenv cx e es2 sm sb u ee tv
       (FST (as_ptr_val ty LocMemory (op,sb)))
       (t0 with vs_inst_idx := LENGTH sb.cs_current_insts) /\
     vv_store_bound cx ty lt ee tv (FST (as_ptr_val ty LocMemory (op,sb)))
       (t0 with vs_inst_idx := LENGTH sb.cs_current_insts) /\
     (t0 with vs_inst_idx := LENGTH sb.cs_current_insts).vs_current_bb =
       sb.cs_current_bb /\
     (t0 with vs_inst_idx := LENGTH sb.cs_current_insts).vs_inst_idx =
       LENGTH sb.cs_current_insts /\
     alloca_history func (t0 with vs_inst_idx := LENGTH sb.cs_current_insts) /\
     u.vs_alloca_next <=
       (t0 with vs_inst_idx := LENGTH sb.cs_current_insts).vs_alloca_next` by
    (rpt gen_tac >> strip_tac >>
     at_horizon `!H. valid_horizon cx st0 H es2.storage_trace ==> ?n k. _` `H` >>
     gvs[expr_exit_def]) >>
  qpat_assum `!H. valid_horizon cx st0 H es2.storage_trace ==> ?n k. _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `n` (qx_choose_then `k`
    (fn th => assume_tac (CONJUNCT1 th) >> assume_tac (CONJUNCT2 th)))) >>
  rewrite_tac[gas_outcome_def] >>
  qexists_tac `REPLICATE n F` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`res`,`ee`,`k`] >>
  conj_tac
  >- (qpat_assum `!n k. gas_marked_path _ _ _ _ _ _ ==> _` irule >>
      first_assum ACCEPT_TAC) >>
  qpat_x_assum `_ \/ (exit_result _ /\ _)` strip_assume_tac
  >| [
    (* success *)
    (disj1_tac >>
     `?rv. tv = Value rv` by
       (qpat_x_assum `ec_source_tail _ _ _ _ _ _ = (INL tv, _)` mp_tac >>
        simp[ec_source_tail_cases, AllCaseEqs()] >> metis_tac[]) >>
     qexists_tac `t0 with vs_inst_idx := LENGTH sb.cs_current_insts` >>
     conj_tac >- REFL_TAC >>
     qx_gen_tac `H` >> strip_tac >>
     `valid_horizon cx st0 H es2.storage_trace` by
       (qpat_x_assum `valid_horizon cx st0 H _` mp_tac >> simp[]) >>
     `valid_horizon cx st0 H es.storage_trace` by
       (qpat_assum `!H. valid_horizon cx st0 H es2.storage_trace ==>
                        valid_horizon cx st0 H es.storage_trace` irule >>
        first_assum ACCEPT_TAC) >>
     at_horizon `!H. valid_horizon cx st0 H es.storage_trace ==>
                     stmt_state_rel H ctx func cenv cx es s0 /\ _` `H` >>
     at_horizon `!H. valid_horizon cx st0 H es2.storage_trace ==>
                     expr_post H ctx func cenv cx a es sa s1 s0 es1 v1 p t /\ _`
       `H` >>
     qpat_assum `!H t0 tv. valid_horizon cx st0 H es2.storage_trace /\ _ ==> _`
       (qspecl_then [`H`, `t0`, `Value rv`] mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     `vv_post H ctx func cenv cx e es sa sb s0 ee (Value rv)
        (FST (as_ptr_val ty LocMemory (op,sb)))
        (t0 with vs_inst_idx := LENGTH sb.cs_current_insts)` by
       FIRST [drule_all ec_two_operand_post >> simp[],
              metis_tac[ec_two_operand_post]] >>
     qexists_tac `Value rv` >> rpt conj_tac
     >- REFL_TAC
     >- (simp[exprLoweringTheory.as_ptr_val_def] >>
         irule memory_value_post_gas_obs >> conj_tac
         >- simp[contextTheory.mk_ptr_def] >> conj_tac
         >- (first_assum (fn th =>
               ACCEPT_TAC (SRULE[exprLoweringTheory.as_ptr_val_def] th)))
         >- (simp[] >>
             first_assum (fn th =>
               ACCEPT_TAC (CONJUNCT1 (REWRITE_RULE [vv_post_def] th)))))
     >- (rewrite_tac[value_store_bound_gas_obs] >> first_assum ACCEPT_TAC)
     >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC
     >- (irule arithmeticTheory.LESS_EQ_TRANS >>
         qexists_tac `u.vs_alloca_next` >> conj_tac >>
         first_assum ACCEPT_TAC)),
    (* exit *)
    (disj2_tac >> simp[])
  ]
QED

Theorem ecmul_vv_sim_mem:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann ECMul [a;b]) es /\
  body_exprs_mem_ok cx [a;b] ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin ann ECMul [a;b]) es
Proof
  strip_tac >> drule (cj 2 ec_pre_types) >> strip_tac >> gvs[] >>
  rewrite_tac[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule (cj 1 compile_ec_operands) >> strip_tac >>
  `cs_extends sm sb` by
    (drule (cj 2 ec_points_code_shape) >>
     simp[same_blocks_def, cs_extends_def, rich_listTheory.IS_PREFIX_APPEND] >>
     metis_tac[listTheory.APPEND]) >>
  simp[ec_eval_bind] >>
  ho_match_mp_tac (Q.INST [`ann` |-> `ArrayT (BaseT (UintT 256)) (Fixed 2)`,
    `bt` |-> `ECMul`, `q` |-> `scalar`] ec_mem_operands_then) >>
  simp[ec_source_tail_storage_frame] >>
  TRY (conj_tac >-
    (rpt gen_tac >> strip_tac >>
     metis_tac[exprSimHashTheory.expr_exit_INR_cast])) >>
  rpt gen_tac >> strip_tac >> suspend "tail"
QED

Resume ecmul_vv_sim_mem[tail]:
  at_horizon `!H. valid_horizon cx st0 H es2.storage_trace ==>
                  expr_post H ctx func cenv cx a es sa s1 s0 es1 v1 p t /\ _`
    `H0` >>
  `value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 /\
   value_has_type (BaseTV (UintT 256)) v2` by
    gvs[vyperTypeExprResultTheory.expr_result_typed_def,
        vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
        vyperTypeInvariantsTheory.value_result_typed_def,
        vyperValueTheory.evaluate_type_def] >>
  `post_value_type cenv b = BaseT (UintT 256)` by
    fs[compileEnvTheory.is_word_type_def] >>
  `expr_val_rel cx (BaseT (UintT 256)) v2 scalar u` by
    metis_tac[loweringPostsTheory.expr_post_def] >>
  `?sw. eval_operand scalar u = SOME sw` by
    metis_tac[cj 1 ec_memory_semantics] >>
  `w2n w + 64 < dimword (:256)` by
    metis_tac[ec_point_pointer_bound] >>
  `!i. MEM i (emitted_insts sm sb) ==> MEM i (fn_insts func)` by
    metis_tac[exprSimHashTheory.hash_emitted_inst_mem] >>
  Cases_on `ec_source_tail cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul
    [ArrayT (BaseT (UintT 256)) (Fixed 2);BaseT (UintT 256)] [v1;v2] es2` >>
  rename1 `ec_source_tail _ _ _ _ _ _ = (sr,ee)` >>
  `ECMul = ECAdd \/ ECMul = ECMul` by simp[] >>
  `~expr_has_effect (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul [a;b]) ==>
   ~expr_has_effect a /\ ~expr_has_effect b` by
    simp[supportedExprTraverseTheory.expr_has_effect_def] >>
  `!H. valid_horizon cx st0 H es2.storage_trace ==>
     ?n k. gas_marked_path T ctx func u n k /\
       ((?t0 tv.
           k = OK (t0 with vs_inst_idx := LENGTH sb.cs_current_insts) /\
           run_inst_seq (emitted_insts sm sb) u = OK t0 /\ sr = INL tv /\
           vv_post H ctx func cenv cx (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul [a;b]) es2 sm sb u ee tv
             (FST (as_ptr_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) LocMemory (res,sb)))
             (t0 with vs_inst_idx := LENGTH sb.cs_current_insts) /\
           vv_store_bound cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) (ArrayT (BaseT (UintT 256)) (Fixed 2)) ee tv
             (FST (as_ptr_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) LocMemory (res,sb)))
             (t0 with vs_inst_idx := LENGTH sb.cs_current_insts) /\
           (t0 with vs_inst_idx := LENGTH sb.cs_current_insts).vs_current_bb =
             sb.cs_current_bb /\
           (t0 with vs_inst_idx := LENGTH sb.cs_current_insts).vs_inst_idx =
             LENGTH sb.cs_current_insts /\
           alloca_history func
             (t0 with vs_inst_idx := LENGTH sb.cs_current_insts) /\
           u.vs_alloca_next <=
             (t0 with vs_inst_idx := LENGTH sb.cs_current_insts).vs_alloca_next) \/
        (exit_result k /\ expr_exit sr k))` by
    (qx_gen_tac `H` >> strip_tac >>
     at_horizon `!H. valid_horizon cx st0 H es2.storage_trace ==>
                     expr_post H ctx func cenv cx a es sa s1 s0 es1 v1 p t /\ _`
       `H` >>
     drule_at (Pat `compile_ecmul_point _ _ _ = _`)
       (Q.INST [`e` |-> `Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul [a;b]`] ecmul_points_path_mem) >>
     simp[exprLoweringTheory.lowered_value_type_def,
          vyperASTTheory.expr_type_def] >>
     TRY (disch_then drule_all) >>
     disch_then (strip_assume_tac o SPEC_ALL) >> metis_tac[]) >>
  drule_all ec_tail_lift_mem >> simp[]
QED
Finalise ecmul_vv_sim_mem

Theorem ecadd_vv_sim_mem:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann ECAdd [a;b]) es /\
  body_exprs_mem_ok cx [a;b] ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin ann ECAdd [a;b]) es
Proof
  strip_tac >> drule (cj 1 ec_pre_types) >> strip_tac >> gvs[] >>
  rewrite_tac[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule (cj 2 compile_ec_operands) >> strip_tac >>
  `cs_extends sm sb` by
    (drule (cj 1 ec_points_code_shape) >>
     simp[same_blocks_def, cs_extends_def, rich_listTheory.IS_PREFIX_APPEND] >>
     metis_tac[listTheory.APPEND]) >>
  simp[ec_eval_bind] >>
  ho_match_mp_tac (Q.INST [`ann` |-> `ArrayT (BaseT (UintT 256)) (Fixed 2)`,
    `bt` |-> `ECAdd`] ec_mem_operands_then) >>
  simp[ec_source_tail_storage_frame] >>
  TRY (conj_tac >-
    (rpt gen_tac >> strip_tac >>
     metis_tac[exprSimHashTheory.expr_exit_INR_cast])) >>
  rpt gen_tac >> strip_tac >> suspend "typed"
QED

Resume ecadd_vv_sim_mem[typed]:
  at_horizon `!H. valid_horizon cx st0 H es2.storage_trace ==>
                  expr_post H ctx func cenv cx a es sa s1 s0 es1 v1 p t /\ _`
    `H0` >>
  `value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 /\
   value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v2` by
    gvs[vyperTypeExprResultTheory.expr_result_typed_def,
        vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
        vyperTypeInvariantsTheory.value_result_typed_def,
        vyperValueTheory.evaluate_type_def] >>
  `post_value_type cenv b = expr_type b` by
    (irule exprSimHypsTheory.post_value_type_ec_point >> conj_tac >- simp[] >>
     qexistsl_tac [`cx`,`env`,`es`] >>
     qpat_assum `expr_type b = _` (fn th => simp[th]) >>
     qpat_x_assum `expr_body_pre _ _ _ (Builtin _ _ _) _` mp_tac >>
     simp[exprSimHypsDefsTheory.expr_body_pre_def,
          vyperTypeSystemTheory.well_typed_expr_def]) >>
  `expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v2 q u /\
   expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) s1 sm es2 v2 q u` by
    metis_tac[loweringPostsTheory.expr_post_def] >>
  `sa.cs_next_id <= s1.cs_next_id` by metis_tac[cj 2 compile_expr_grows] >>
  `expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) sa sm es2 v2 q u` by
    metis_tac[exprSimPropsTheory.expr_val_at_start_mono] >>
  `?w2. eval_operand q u = SOME w2` by
    (qpat_assum `expr_val_rel _ _ v1 p u`
      (mp_then (Pat `expr_val_rel _ _ _ _ _`) mp_tac (cj 2 ec_memory_semantics)) >>
     simp[] >> disch_then drule_all >> metis_tac[]) >>
  `w2n w2 + 64 <= u.vs_alloca_next` by
    (irule bodyMemEcArithOperandsTheory.ec_point_read_capacity >>
     qexistsl_tac [`cx`,`q`,`u`,`v2`] >> simp[]) >>
  `w2n w + 64 < dimword (:256) /\ w2n w2 + 64 < dimword (:256)` by
    metis_tac[ec_point_pointer_bound] >>
  `!i. MEM i (emitted_insts sm sb) ==> MEM i (fn_insts func)` by
    metis_tac[exprSimHashTheory.hash_emitted_inst_mem] >>
  Cases_on `ec_source_tail cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd
    [ArrayT (BaseT (UintT 256)) (Fixed 2);ArrayT (BaseT (UintT 256)) (Fixed 2)]
    [v1;v2] es2` >>
  rename1 `ec_source_tail _ _ _ _ _ _ = (sr,ee)` >>
  `ECAdd = ECAdd \/ ECAdd = ECMul` by simp[] >>
  `~expr_has_effect (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd [a;b]) ==>
   ~expr_has_effect a /\ ~expr_has_effect b` by
    simp[supportedExprTraverseTheory.expr_has_effect_def] >>
  `!H. valid_horizon cx st0 H es2.storage_trace ==>
     ?n k. gas_marked_path T ctx func u n k /\
       ((?t0 tv.
           k = OK (t0 with vs_inst_idx := LENGTH sb.cs_current_insts) /\
           run_inst_seq (emitted_insts sm sb) u = OK t0 /\ sr = INL tv /\
           vv_post H ctx func cenv cx (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd [a;b]) es2 sm sb u ee tv
             (FST (as_ptr_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) LocMemory (res,sb)))
             (t0 with vs_inst_idx := LENGTH sb.cs_current_insts) /\
           vv_store_bound cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) (ArrayT (BaseT (UintT 256)) (Fixed 2)) ee tv
             (FST (as_ptr_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) LocMemory (res,sb)))
             (t0 with vs_inst_idx := LENGTH sb.cs_current_insts) /\
           (t0 with vs_inst_idx := LENGTH sb.cs_current_insts).vs_current_bb =
             sb.cs_current_bb /\
           (t0 with vs_inst_idx := LENGTH sb.cs_current_insts).vs_inst_idx =
             LENGTH sb.cs_current_insts /\
           alloca_history func
             (t0 with vs_inst_idx := LENGTH sb.cs_current_insts) /\
           u.vs_alloca_next <=
             (t0 with vs_inst_idx := LENGTH sb.cs_current_insts).vs_alloca_next) \/
        (exit_result k /\ expr_exit sr k))` by
    (qx_gen_tac `H` >> strip_tac >>
     at_horizon `!H. valid_horizon cx st0 H es2.storage_trace ==>
                     expr_post H ctx func cenv cx a es sa s1 s0 es1 v1 p t /\ _`
       `H` >>
     drule_at (Pat `compile_ecadd_points _ _ _ = _`)
       (Q.INST [`e` |-> `Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd [a;b]`] ecadd_points_path_mem) >>
     simp[exprLoweringTheory.lowered_value_type_def,
          vyperASTTheory.expr_type_def] >>
     TRY (disch_then drule_all) >>
     disch_then (strip_assume_tac o SPEC_ALL) >> metis_tac[]) >>
  drule_all ec_tail_lift_mem >> simp[]
QED
Finalise ecadd_vv_sim_mem

Theorem ec_arith_sim_mem:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann bt [a;b]) es /\
  body_exprs_mem_ok cx [a;b] /\ (bt = ECAdd \/ bt = ECMul) ==>
  expr_sim_mem ctx func cenv cx ty (Builtin ann bt [a;b]) es /\
  expr_vv_sim_mem ctx func cenv cx ty (Builtin ann bt [a;b]) es
Proof
  strip_tac >>
  `expr_vv_sim_mem ctx func cenv cx ty (Builtin ann bt [a;b]) es` by
    metis_tac[ecadd_vv_sim_mem, ecmul_vv_sim_mem] >> simp[] >>
  gvs[] >>
  (irule body_expr_sim_mem_of_vv_sim_mem >> simp[] >> conj_tac
   >- (rpt strip_tac >> imp_res_tac compile_ec_operands >>
       gvs[exprLoweringTheory.as_ptr_val_def]) >>
   qexists_tac `env` >> simp[])
QED
