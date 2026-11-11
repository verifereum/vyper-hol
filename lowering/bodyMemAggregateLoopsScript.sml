(* Allocated aggregate traversal, with checked memory accesses. *)
Theory bodyMemAggregateLoops
Ancestors
  bodyMemAggregateLoopBoundary bodyMemAggregateCons bodyMemoryPreds
  exprSimAggregateChildren exprSimAggregateLayout exprSimHyps
  exprLowering exprLoweringProps exprOperandVar compileEnv loweringStateRelDefs loweringPosts
  gasOutcome gasSummary exprSimWordArgs vyperState vyperInterpreter
  freshWrites valueEncoding valueEncodingDefs fragExec exprSimDefs exprSimMemDefs
  fragGasMode fragGasPath exprSimAggregateLoops valueEncodingProofs

Theorem aggregate_make_tuple_sim_mem:
  !args ce cx env off sa out sb es tvs func inst x b asz s0 ctx tops.
  compile_make_tuple compile_expr ce args (MAP expr_type args) (Var x) off sa =
    (out,sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  body_inv tops ctx ce cx /\ body_exprs_mem_ok cx args /\
  (!e. MEM e args ==>
     int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + type_memory_size_list tvs <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) =
       SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off)
       (type_memory_size_list tvs)) /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
    (\res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' r /\
      tuple_in_memory vs tvs (b+off) r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+type_memory_size_list tvs <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es es' s0 r /\
      alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next)
    (\res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  Induct_on `args`
  >- (rpt gen_tac >> strip_tac >>
      gvs[compile_make_tuple_def, comp_return_def] >>
      irule aggregate_tuple_nil_outcome_mem >>
      simp[val_in_memory_def, stmt_state_rel_gas_obs]) >>
  pop_assum (fn ih =>
    rpt gen_tac >> strip_tac >>
    `out = Var x` by metis_tac[compiler_make_tuple_result] >>
    gvs[] >>
    assume_tac ih) >>
  `expr_body_pre ce cx env h es` by metis_tac[listTheory.MEM] >>
  drule aggregate_mem_tuple_cons_compile >> strip_tac >>
  rename1 `compile_expr ce (expr_type h) h sa = (vv,sm)` >>
  rename1 `emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn)` >>
  rename1 `unwrap_value ce vv sn = (op,su)` >>
  rename1 `compile_store_memory ce op dst (expr_type h) (lowered_value_type ce h) su = ((),ss)` >>
  `ci_mono sa sm` by metis_tac[cj 1 compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sm sn` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sn su` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `ci_mono su ss` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `ci_mono ss sb` by
    metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  drule_all aggregate_tuple_child_outcome_mem >> strip_tac >>
  rewrite_tac[aggregate_tuple_eval_cons] >>
  match_mp_tac (Q.SPEC `\tv ee r.
    vv_post ctx func ce cx h es sa sm s0 ee tv vv r /\
    vv_store_bound cx (expr_type h) (lowered_value_type ce h) ee tv vv r /\
    r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next`
    (Q.GEN `P` aggregate_tuple_bind_outcome_any)) >>
  conj_tac
  >- (qpat_x_assum `gas_outcome _ _ _ (eval_expr _ _) _ _ _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[gas_outcome_def, gas_summary_at_def] >>
      rpt strip_tac >> qexists_tac `marks`
      >- (gvs[] >> disj1_tac >> qexistsl_tac [`INL tv`, `es_end`, `OK t`] >> simp[]) 
      >- (disj1_tac >> qexistsl_tac [`res`, `es_end`, `r`] >>
          Cases_on `res` >> gvs[expr_exit_def]) >>
      disj2_tac >> metis_tac[]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  rename1 `gas_marked_exec T _ (eval_expr cx h) _ marks (INL tv) es1 (OK t1)` >>
  suspend "child_success"
QED

Resume aggregate_make_tuple_sim_mem[child_success]:
  `es1 with gas_obs := [] = es1` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `~t1.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  drule_all aggregate_tuple_marked_child_source_any >> simp[] >> strip_tac >>
  `type_memory_bytes ce (expr_type h) = type_memory_size h'` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `cs_extends sm ss /\ cs_extends ss sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sm ss func` by metis_tac[fn_has_code_split] >>
  `lookup_var x t1 = SOME (n2w b) /\
   FLOOKUP t1.vs_allocas inst.inst_id = SOME (b,asz)` by
    (fs[vv_post_def] >> metis_tac[]) >>
  `not_fresh_at sm x` by metis_tac[not_fresh_at_mono, ci_mono_def] >>
  `stmt_state_rel ctx func ce cx es1 t1` by fs[vv_post_def] >>
  `expr_sim_inv ce cx env es1` by gvs[] >>
  `not_local_ptr ce es1.scopes x` by metis_tac[] >>
  `alloca_inv t1` by fs[stmt_state_rel_def] >>
  `off + type_memory_size h' <= asz` by
    (fs[type_memory_size_def] >> decide_tac) >>
  `!name lo sz. local_region ce es1.scopes t1 name lo sz ==>
     lo+sz <= b+off \/ b+off+type_memory_size h' <= lo` by
    (rpt strip_tac >> drule_all aggregate_alloca_slice_excludes_local >> simp[]) >>
  drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`) aggregate_tuple_marked_footprint_any >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ce.ce_is_ctor ==> _`)) >>
  simp[] >> strip_tac >>
  `ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size h')` by
    (rpt strip_tac >>
     qpat_x_assum `!name itv iv io. _ ==> regions_disjoint _ _ _ (type_memory_size_list _)`
       drule_all >>
     simp[regions_disjoint_def, type_memory_size_def] >> decide_tac) >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) aggregate_tuple_cons_continuation_mem_cursor >>
  disch_then (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  disch_then (qspecl_then [`asz`, `inst.inst_id`] mp_tac) >>
  impl_tac
  >- (simp[] >> reverse conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >>
      qpat_x_assum `!name lo sz. local_region _ _ _ _ _ _ ==> _` drule >>
      decide_tac) >> strip_tac >>
  suspend "tail"
QED

Resume aggregate_make_tuple_sim_mem[tail]:
  `body_exprs_mem_ok cx args` by
    (drule_all aggregate_body_exprs_mem_tail >> simp[]) >>
  `~q.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  irule aggregate_tuple_value_bind_any >>
  goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `!ce' cx' env' off' sa' out' sb' es' tvs' func' inst' x' b' asz' s0' ctx' tops'. _`
    (drule_at (Pat `compile_make_tuple _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `OPT_MMAP _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP s.vs_allocas _ = _`)) >>
  disch_then (qspecl_then [`env`, `tops`] mp_tac) >>
  impl_tac
  >- (simp[type_memory_size_def] >>
      `cs_extends sa ss` by metis_tac[cs_extends_trans] >>
      `fn_has_code ss sb func` by metis_tac[fn_has_code_split] >>
      `local_ptrs_reserved ce ss` by metis_tac[compiler_ci_mono_reserved] >>
      simp[] >> rpt conj_tac
      >- (fs[ci_mono_def] >> decide_tac)
      >- metis_tac[not_fresh_at_mono, ci_mono_def]
      >- fs[type_memory_size_def] >>
      rpt strip_tac >>
      qpat_x_assum `!name itv iv io. _ ==> regions_disjoint _ _ _ (type_memory_size_list _)`
        drule_all >>
      simp[regions_disjoint_def, type_memory_size_def] >> decide_tac) >>
  strip_tac >> suspend "assembly"
QED

Resume aggregate_make_tuple_sim_mem[assembly]:
  irule aggregate_tuple_values_outcome_any >>
  goal_assum (drule_at Any) >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[] >> suspend "post"
QED

Resume aggregate_make_tuple_sim_mem[post]:
  conj_tac >- suspend "head_encoding" >>
  conj_tac >- suspend "vars_join" >>
  conj_tac >- suspend "allocas_join" >>
  conj_tac >- suspend "slice_join" >>
  conj_tac >- suspend "exterior_join" >>
  suspend "locals_join"
QED

Resume aggregate_make_tuple_sim_mem[head_encoding]:
  pure_once_rewrite_tac[val_in_memory_def] >>
  simp_tac std_ss [listTheory.list_case_def, LET_THM] >>
  conj_tac
  >- (irule (cj 1 val_in_memory_mem_agree_proof) >>
      simp[] >> conj_tac
      >- (irule (cj 1 valueEncodingTypingTheory.value_has_type_val_wf) >>
          qpat_x_assum `!v. read_result _ _ _ = _ ==> value_has_type _ _` irule >>
          fs[gas_marked_exec_def] >> metis_tac[]) >>
      qexists_tac `q.vs_memory` >> simp[]) >>
  qpat_x_assum `tuple_in_memory vs t _ _` mp_tac >>
  rpt (pop_assum kall_tac) >> pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >>
  simp_tac bool_ss []
QED

Resume aggregate_make_tuple_sim_mem[vars_join]:
  rpt strip_tac >>
  `not_fresh_at sm z /\ not_fresh_at ss z` by
    (conj_tac >> irule not_fresh_at_mono >>
     qexists_tac `sa` >> fs[ci_mono_def] >> decide_tac) >>
  qpat_x_assum `!z w. not_fresh_at ss z /\ _ ==> _` irule >> simp[] >>
  qpat_x_assum `!z a. not_fresh_at sm z /\ _ ==> _` irule >> simp[] >>
  fs[vv_post_def] >> metis_tac[]
QED
Resume aggregate_make_tuple_sim_mem[allocas_join]:
  rpt strip_tac >>
  qpat_x_assum `!aid a. FLOOKUP q.vs_allocas aid = SOME a ==> _` irule >>
  qpat_x_assum `!i a. FLOOKUP t1.vs_allocas i = SOME a ==> _` irule >>
  fs[vv_post_def] >> metis_tac[]
QED
Resume aggregate_make_tuple_sim_mem[slice_join]:
  rpt strip_tac >>
  `!name lo sz. local_region ce es.scopes s0 name lo sz ==>
      asz + b <= lo \/ lo + sz <= b` by
    (`not_local_ptr ce es.scopes x` by simp[] >>
     `alloca_inv s0 /\ local_ptrs_rel func ce es.scopes s0` by
       (qpat_assum `stmt_state_rel ctx func ce cx es s0` mp_tac >>
        simp_tac std_ss [stmt_state_rel_def, state_rel_def] >>
        strip_tac >> asm_rewrite_tac[]) >>
     rpt strip_tac >> drule_all localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     simp[regions_disjoint_def, arithmeticTheory.ADD_COMM]) >>
  `!name lo sz. local_region ce es1.scopes t1 name lo sz ==>
      asz + b <= lo \/ lo + sz <= b` by
    (`not_local_ptr ce es1.scopes x` by simp[] >>
     `alloca_inv t1 /\ local_ptrs_rel func ce es1.scopes t1` by
       (qpat_assum `stmt_state_rel ctx func ce cx es1 t1` mp_tac >>
        simp_tac std_ss [stmt_state_rel_def, state_rel_def] >>
        strip_tac >> asm_rewrite_tac[]) >>
     rpt strip_tac >> drule_all localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     simp[regions_disjoint_def, arithmeticTheory.ADD_COMM]) >>
  `mem_bytes_at b asz t1.vs_memory = mem_bytes_at b asz s0.vs_memory` by
    (irule vv_post_old_buffer >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     qexists_tac `inst.inst_id` >> simp[] >> rpt strip_tac >>
     metis_tac[]) >>
  `mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory` by
    (qpat_x_assum `!p n. b <= p /\ _ ==> _` irule >>
     fs[type_memory_size_def] >> decide_tac) >>
  `mem_bytes_at p n q.vs_memory = mem_bytes_at p n t1.vs_memory` by
    (qpat_x_assum `!i lo sz a k. _ ==> mem_bytes_at a k q.vs_memory = _` irule >>
     reverse conj_tac >- (fs[type_memory_size_def] >> decide_tac) >>
     qexistsl_tac [`inst.inst_id`, `b`, `asz`] >> simp[] >>
     rpt strip_tac >> metis_tac[]) >>
  `mem_bytes_at p n t1.vs_memory = mem_bytes_at p n s0.vs_memory` by
    (qpat_assum `mem_bytes_at b asz t1.vs_memory = _`
       (mp_then Any mp_tac mem_bytes_at_agree_window) >>
     strip_tac >> sym_tac >> first_x_assum irule >> decide_tac) >>
  simp[]
QED
Resume aggregate_make_tuple_sim_mem[exterior_join]:
  rpt strip_tac >>
  `local_ptrs_reserved ce sm` by metis_tac[compiler_ci_mono_reserved] >>
  `!name lo sz. local_region ce es1.scopes t1 name lo sz ==>
      n + p <= lo \/ lo + sz <= p` by
    (rpt strip_tac >>
     `local_region ce es.scopes s0 name lo sz` by
       (irule aggregate_mem_tuple_local_region_backward >>
        goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     metis_tac[]) >>
  `!name lo sz. local_region ce es1.scopes q name lo sz ==>
      n + p <= lo \/ lo + sz <= p` by
    (rpt strip_tac >>
     `local_region ce es1.scopes t1 name lo sz` by
       (irule exprSimPropsTheory.local_region_frame >> conj_tac
        >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`sm`, `es1.scopes`, `q`] >> asm_rewrite_tac[]) >>
     metis_tac[]) >>
  `mem_bytes_at p n t1.vs_memory = mem_bytes_at p n s0.vs_memory` by
    (irule vv_post_old_buffer >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     qexists_tac `aid` >> simp[] >> rpt strip_tac >> metis_tac[]) >>
  `FLOOKUP t1.vs_allocas aid = SOME (p,n)` by
    (fs[vv_post_def] >> metis_tac[]) >>
  `FLOOKUP q.vs_allocas aid = SOME (p,n)` by
    (qpat_x_assum `!i a. FLOOKUP t1.vs_allocas i = SOME a ==> _` irule >> simp[]) >>
  `mem_bytes_at p n q.vs_memory = mem_bytes_at p n t1.vs_memory` by
    (qpat_x_assum `!i lo sz a k. _ ==> mem_bytes_at a k q.vs_memory = _` irule >>
     reverse conj_tac >- (fs[type_memory_size_def] >> decide_tac) >>
     qexistsl_tac [`aid`, `p`, `n`] >> simp[] >>
     fs[ci_mono_def] >> metis_tac[]) >>
  `mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory` by
    (qpat_x_assum `!aid p n. _ ==> mem_bytes_at p n r.vs_memory = _` irule >>
     simp[] >> conj_tac >- metis_tac[] >>
     qexists_tac `aid` >> simp[] >> fs[ci_mono_def] >> decide_tac) >>
  simp[]
QED
Resume aggregate_make_tuple_sim_mem[locals_join]:
  `local_ptrs_reserved ce sm` by metis_tac[compiler_ci_mono_reserved] >>
  irule exprBopSimPropsTheory.locals_kept_trans >> qexistsl_tac [`es1`, `sa`, `t1`] >>
  fs[vv_post_def] >>
  irule exprBopSimPropsTheory.locals_kept_trans >> qexistsl_tac [`es1`, `sm`, `q`] >> simp[]
QED
Finalise aggregate_make_tuple_sim_mem
