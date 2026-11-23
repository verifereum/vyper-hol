(* Selected visits in constructor operands follow the original native suffix.
   Snapshot and encoder instructions are not source operand evaluations. *)
Theory entryCreateCtorStageVisit
Ancestors
  entryCreateNativeFirstExit entryCreateEffectFocus entryCreateBodyCut entryCreateFocusSpec
  createSizePrefixReplay createSizeItinerary exprSimWordArgs
  vyperStorageTrace vyperStorageFootprint gasSummaryCompose fragGasPath
  vyperInterpreter vyperState list pair arithmetic compileEnv exprLowering
  createSizeCreateLayoutCode createSizeOperandCode createSizeConcreteSnapshots
  createSizeCutCode fragExec createCtorSegmentArrival relation abiEncoderProps

(* The snapshot row may use a second compiler band after the VV expression.
   Its completed-row callback consumes exactly the observations of the two
   bands queried by the outer cut; it is not an all-tails execution claim. *)
Theorem create_ctor_completed_row_right[local]:
  ~s.vs_halted /\
  create_expr_prefix a m E ctx fn s (create_cut_marks E front) t /\
  (!v. storage_trace_frame (next v)) /\
  (!H tail r mid.
    source (es with gas_obs :=
      gas_explicit (create_cut_marks E front) s.vs_gas_readings ++ tail) = (r,mid) /\
    valid_horizon cx st0 H mid.storage_trace ==>
    create_cut_failure tops r \/
    ?v. r = INL v /\ mid.gas_obs = tail /\
      create_body_cut E tops cx st0 (next v) (mid with gas_obs := [],t) (back,hit)) ==>
  create_body_cut E tops cx st0 (bind source next) (es,s) (front ++ back,hit)
Proof
  strip_tac >>
  drule_all create_prefix_gas_path >>
  disch_then (assume_tac o GEN_ALL o MATCH_MP gas_explicit_append_path) >>
  rw[create_body_cut_def] >>
  qabbrev_tac `suffix = gas_explicit (create_cut_marks E back) t.vs_gas_readings ++ tail` >>
  `?r mid. source (es with gas_obs :=
    gas_explicit (create_cut_marks E front) s.vs_gas_readings ++ suffix) = (r,mid)` by
      (Cases_on `source (es with gas_obs :=
        gas_explicit (create_cut_marks E front) s.vs_gas_readings ++ suffix)` >> simp[]) >>
  `bind source next (es with gas_obs :=
     gas_explicit (create_cut_marks E front) s.vs_gas_readings ++ suffix) = (res,ee)` by
     fs[Abbr `suffix`,APPEND_ASSOC] >>
  pop_assum (mk_asm "bound") >> asm_x "bound" mp_tac >>
  pure_once_rewrite_tac[bind_def] >>
  qpat_assum `source _ = (r,mid)` (pure_once_rewrite_tac o single) >>
  Cases_on `r` >> simp_tac (srw_ss()) [] >> strip_tac
  >- (`valid_horizon cx st0 H mid.storage_trace` by
       (qpat_assum `next _ mid = _` (mp_then Any irule valid_horizon_frame) >> simp[]) >>
      qpat_assum `!H tail r mid. _` (drule_all_then strip_assume_tac)
      >- fs[create_cut_failure_def] >>
      `((mid with gas_obs := []) with gas_obs := suffix) = mid` by
        simp[evaluation_state_component_equality] >>
      qpat_x_assum `create_body_cut _ _ _ _ _ _ _` mp_tac >>
      simp[create_body_cut_def] >>
      disch_then (qspecl_then [`H`,`tail`,`res`,`ee`] mp_tac) >>
      fs[Abbr `suffix`]) >>
  gvs[] >> qpat_assum `!H tail r mid. _` (drule_all_then mp_tac) >>
  simp[create_cut_failure_def] >> metis_tac[]
QED

Theorem ctor_source_cons[local]:
  bind (eval_exprs cx (e::args)) k =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (eval_exprs cx args) (\vs. k (v::vs)))
Proof
  simp[eval_exprs_cons_action,bind_assoc,bind_return]
QED

(* The observed suffix after a row supplies the exit fetch required by the
   snapshot replay theorem. It may be a pending caller visit, so no OK
   execution of that instruction, or of a later dispatch, is required. *)
Theorem create_ctor_row_exit_fetch[local]:
  create_interior_visit a b E ctx fn (p,d,k) t (before,hit,after) ==>
  ?i. create_operand_fetch a b fn t i /\
      ctor_segment_fetch fn t = SOME i /\ a.cs_next_id <= i.inst_id
Proof
  simp_tac bool_ss [create_interior_visit_def,LET_THM] >>
  disch_then (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 mp_tac
      (CONJUNCTS_THEN2 assume_tac (K ALL_TAC)))))) >>
  simp[Once RTC_CASES1] >> strip_tac
  >- (gvs[] >> fs[create_operand_fetch_def,ctor_segment_fetch_def,frag_ids_def]) >>
  qmatch_asmsub_rename_tac `create_operand_native_step _ _ _ _ _ _ _ endpoint` >>
  PairCases_on `endpoint` >>
  fs[create_operand_native_step_def,create_operand_fetch_def,
     ctor_segment_fetch_def,frag_ids_def] >> metis_tac[]
QED

(* No mark or opcode from the unevaluated suffix is fed back into the
   completed row. Conversely, an interior left hit consumes no row replay. *)
Theorem create_ctor_row_visit[local]:
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m fn /\
  create_cut_code {} m b /\ fn_has_code m b fn /\
  ~s.vs_halted /\ (!v. storage_trace_frame (next v)) /\
  create_operand_cut a m E ctx fn tops cx st0 source (es,s) /\
  (!front t j H tail r mid.
    create_operand_at m t /\ ctor_segment_fetch fn t = SOME j /\ m.cs_next_id <= j.inst_id /\
    create_expr_prefix a m E ctx fn s (create_cut_marks E front) t /\
    source (es with gas_obs :=
      gas_explicit (create_cut_marks E front) s.vs_gas_readings ++ tail) = (r,mid) /\
    valid_horizon cx st0 H mid.storage_trace ==>
    create_cut_failure tops r \/
    ?v. r = INL v /\ mid.gas_obs = tail /\
      create_operand_cut m b E ctx fn tops cx st0 (next v) (mid with gas_obs := [],t)) ==>
  create_operand_cut a b E ctx fn tops cx st0 (bind source next) (es,s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[create_operand_cut_def] >> rpt gen_tac >> strip_tac >>
  drule_all create_interior_visit_first_exit >> strip_tac
  >- (irule create_cut_bind_left >> simp[] >> fs[create_operand_cut_def] >> metis_tac[]) >>
  drule_then strip_assume_tac create_ctor_row_exit_fetch >>
  qpat_x_assum `before = front ++ back` SUBST_ALL_TAC >>
  irule create_ctor_completed_row_right >> simp[] >>
  first_assum (irule_at Any) >> simp[] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!front t j H tail r mid. _` (drule_all_then strip_assume_tac)
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> qexists_tac `v` >> fs[create_operand_cut_def] >> metis_tac[]
QED

Theorem ctor_program_closed[local]:
  compile_create_ctor_args compile_expr ce args a = (vals,b) ==>
  create_cut_code {} a b
Proof
  strip_tac >>
  `create_cut_code {} a (SND (compile_create_ctor_args compile_expr ce args a))` by
    (irule create_ctor_args_cut >> simp[create_operand_cut_code,create_vv_snapshot_cut_code]) >>
  pop_assum mp_tac >> pure_asm_rewrite_tac[] >> simp[]
QED

(* P describes the actual entry relation; in applications its ghosts are
   existential outside the horizon quantifier. Constructor rows may choose
   a different representation (ordinary or VV) at each boundary. *)
Theorem create_ctor_rows_visit[local]:
  !args a vals m es s next.
    body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
    EVERY Eligible args /\
    compile_create_ctor_args compile_expr ce args a = (vals,m) /\
    create_cut_code {} m b /\ fn_has_code a b fn /\ P a es s /\
    (!v. storage_trace_frame (next v)) /\
    (!c p u vs. P c p u /\ fn_has_code c b fn /\ c = m ==>
      create_operand_cut c b E ctx fn tops cx st0 (next vs) (p,u)) /\
    (!e rest c d h v sv p u.
      Eligible e /\ P c p u /\ fn_has_code c h fn /\
      compile_expr ce (expr_type e) e c = (v,d) /\
      compile_snapshot_vv ce (exprs_can_mutate ce rest)
        (ext_call_arg_value (lowered_value_type ce e) v) d = (sv,h) ==>
      ~u.vs_halted /\ create_operand_cut c h E ctx fn tops cx st0
         (bind (eval_expr cx e) (read_result cx)) (p,u)) /\
    (!e rest c d h v sv p u front t j H tail r mid.
      Eligible e /\ P c p u /\ fn_has_code c h fn /\
      compile_expr ce (expr_type e) e c = (v,d) /\
      compile_snapshot_vv ce (exprs_can_mutate ce rest)
        (ext_call_arg_value (lowered_value_type ce e) v) d = (sv,h) /\
      create_operand_at h t /\ ctor_segment_fetch fn t = SOME j /\ h.cs_next_id <= j.inst_id /\
      create_expr_prefix c h E ctx fn u (create_cut_marks E front) t /\
      bind (eval_expr cx e) (read_result cx)
        (p with gas_obs := gas_explicit (create_cut_marks E front) u.vs_gas_readings ++ tail) = (r,mid) /\
      valid_horizon cx st0 H mid.storage_trace ==>
      create_cut_failure tops r \/
      (?vv. r = INL vv /\ mid.gas_obs = tail /\ P h (mid with gas_obs := []) t)) ==>
    create_operand_cut a b E ctx fn tops cx st0 (bind (eval_exprs cx args) next) (es,s)
Proof
  Induct
  >- (simp[compile_create_ctor_args_def,comp_return_def] >> rpt gen_tac >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      `bind (eval_exprs cx []) next = next []` by simp[FUN_EQ_THM,bind_def,eval_exprs_nil] >>
      asm_rewrite_tac[] >> first_x_assum irule >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_create_ctor_args _ _ (_::_) _ = _` mp_tac >>
  simp[Once compile_create_ctor_args_def,comp_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  rename1 `compile_expr ce (expr_type e) e a = (v,d)` >>
  rename1 `compile_snapshot_vv ce _ _ d = (sv,c)` >>
  rename1 `compile_create_ctor_args compile_expr ce args c = (rest,m)` >>
  `create_cut_code {} a d` by metis_tac[create_operand_cut_code,SND] >>
  `create_cut_code {} d c` by metis_tac[create_vv_snapshot_cut_code,SND] >>
  `create_cut_code {} a c /\ create_cut_code {} c b` by
    metis_tac[ctor_program_closed,create_cut_code_join] >>
  `fn_has_code a c fn /\ fn_has_code c b fn` by
    metis_tac[create_cut_code_def,fn_has_code_split] >>
  `~s.vs_halted /\ create_operand_cut a c E ctx fn tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s)` by
      (qpat_assum `!e rest c d h v sv p u. _` (drule_all_then MATCH_ACCEPT_TAC)) >>
  rewrite_tac[ctor_source_cons] >> irule create_ctor_row_visit >>
  first_assum (irule_at Any) >> simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame] >>
  qexists_tac `ce` >> simp[] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!e rest c d h v sv p u front t j H tail r mid. _` (drule_all_then strip_assume_tac)
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> qexists_tac `vv` >> simp[] >>
  qpat_assum `!a' vals' m' es' s'' next'. _` irule >>
  first_assum (irule_at Any) >> simp[] >> conj_tac >> first_assum ACCEPT_TAC
QED
