(* Counted aggregate loops using the physical-layout child-store boundary. *)
Theory exprSimAggregateBodyLoops
Ancestors
  exprSimAggregateBodyHead exprSimAggregateBodySource exprSimAggregateBodyFrames
  exprSimAggregateBodyCounted exprSimAggregateLoops exprSimAggregateSource
  exprSimAggregateEncoding exprSimAggregateLayout exprLoweringProps
  exprSimDefs exprSimHypsDefs exprSimHyps exprSimProps exprSimSource loweringPosts
  compileEnv exprLowering valueEncoding valueEncodingProps valueEncodingProofs
  gasOutcome gasSummary gasSummaryCompose fragGasMode fragGasPath fragExec
  vyperInterpreter vyperState vyperImmutableMetadataFrame
  vyperEvalExprPreservesScopesDom exprBopSimProps
Libs
  monadsyntax

Theorem aggregate_body_make_tuple_sim:
  !args ce cx env off sa out sb es tvs func inst x b asz s0 ctx.
  compile_make_tuple compile_expr ce args (Var x) off sa = (out,sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st /\ (F ==> int_calls_expr e = [])) /\
  exprs_case F ctx func ce cx args /\
  (!e. MEM e args ==> (int_calls_expr e <> [] /\
    lowered_value_type ce e <> expr_type e ==>
    acyclic_struct_metadata ce.ce_struct_fields)) /\
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
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
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
      locals_kept ce es s0 r)
    (\res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  Induct_on `args`
  >- (rpt gen_tac >>
      simp[compile_make_tuple_def, comp_return_def] >> strip_tac >> gvs[] >>
      rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INL []`, `es`, `OK s0`] >>
      fs[gas_marked_exec_def, evaluate_def, return_def,
           gas_marked_path_def, gas_path_rules, val_in_memory_def,
           locals_kept_def, stmt_state_rel_def, state_rel_gas_obs,
           immutable_alloca_sep_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `compile_expr ce (expr_type h) h sa` >>
  rename1 `compile_expr ce (expr_type h) h sa = (vv,sm)` >>
  Cases_on `emit_op ADD [Var x; Lit (n2w off)] sm` >>
  rename1 `emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn)` >>
  Cases_on `unwrap_value ce vv sn` >>
  rename1 `unwrap_value ce vv sn = (op,su)` >>
  Cases_on `compile_store_memory ce op dst (expr_type h) (lowered_value_type ce h) su` >>
  rename1 `compile_store_memory ce op dst (expr_type h) (lowered_value_type ce h) su = (unit,st)` >>
  Cases_on `unit` >>
  qpat_x_assum `compile_make_tuple _ _ (_::_) _ _ _ = _` mp_tac >>
  simp[Once compile_make_tuple_def, comp_bind_def, comp_ignore_bind_def] >>
  strip_tac >>
  `ci_mono sa sm` by metis_tac[compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sm sn` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sn su` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `ci_mono su st` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `ci_mono st sb` by metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code st sb func /\ fn_has_code sa st func` by
    metis_tac[fn_has_code_split, ci_mono_def, cs_extends_trans] >>
  `expr_body_pre ce cx env h es` by metis_tac[listTheory.MEM] >>
  `gas_admissible (eval_expr cx h) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  `gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx h) (es,s0)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func ce cx h es sa sm s0 ee tv vv t /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (fs[exprs_case_def, expr_vv_case_def] >>
     first_x_assum (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
     simp[expr_vv_sim_def] >> disch_then irule >> simp[] >>
     qexists_tac `expr_type h` >> simp[]) >>
  `out = Var x` by metis_tac[exprOperandVarTheory.compiler_make_tuple_result] >>
  simp[] >>
  irule aggregate_body_cons_outcome >>
  qexists_tac `\tv ee t. vv_post ctx func ce cx h es sa sm s0 ee tv vv t /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts` >>
  reverse conj_tac
  >- (qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
      simp[gas_outcome_def, gas_summary_at_def] >>
      metis_tac[expr_exit_INL, sumTheory.sum_CASES]) >>
  simp[] >>
  rpt gen_tac >> strip_tac >>
  `?ht tt. evaluate_type (get_tenv cx) (expr_type h) = SOME ht /\
      OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tt /\
      tvs = ht::tt` by fs[] >> gvs[] >>
  `type_memory_bytes ce (expr_type h) = type_memory_size ht` by
    metis_tac[expr_sim_inv_memory_size, expr_body_pre_def] >>
  `off + type_memory_size ht <= asz` by
    (fs[type_memory_size_def] >> decide_tac) >>
  `ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size ht)` by
    (fs[type_memory_size_def, regions_disjoint_def] >> rpt strip_tac >>
     first_x_assum drule >> disch_then drule_all >> strip_tac >> decide_tac) >>
  `~t.vs_halted` by metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `int_calls_expr h <> [] /\ lowered_value_type ce h <> expr_type h ==>
      acyclic_struct_metadata ce.ce_struct_fields` by metis_tac[] >>
  `expr_body_pre ce cx env h es` by metis_tac[] >>
  `b + asz < dimword (:256)` by decide_tac >>
  drule_all aggregate_body_tuple_head_path >> strip_tac >>
  `exprs_case F ctx func ce cx args` by
    (drule aggregate_body_marked_replay >> strip_tac >>
     fs[exprs_case_def] >> metis_tac[]) >>
  `ci_mono sa sn` by metis_tac[aggregate_body_ci_mono_trans] >>
  `ci_mono sa su` by metis_tac[aggregate_body_ci_mono_trans] >>
  `ci_mono sa st` by metis_tac[aggregate_body_ci_mono_trans] >>
  `immutable_metadata_frame es mid` by
    (drule_all aggregate_body_marked_replay >> strip_tac >>
     drule eval_expr_immutable_metadata_frame >>
     simp[immutable_metadata_frame_def] >> metis_tac[]) >>
  `ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size_list (ht::tt))` by
    (strip_tac >> ho_match_mp_tac immutable_metadata_frame_property >>
     simp[] >>
     qpat_x_assum `ce.ce_is_ctor ==> !name itv iv io. _ ==> regions_disjoint _ _ _ (type_memory_size_list _)` mp_tac >>
     simp[]) >>
  qabbrev_tac `tailoff = off + type_memory_size ht` >>
  `gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args)
    (mid with gas_obs := [],q)
    (\res ee r. ?vs. res = INL vs /\
      r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env ee /\
      stmt_state_rel ctx func ce cx ee r /\
      tuple_in_memory vs tt (b+tailoff) r.vs_memory /\
      (!z w. not_fresh_at st z /\ lookup_var z q = SOME w ==> lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP q.vs_allocas aid = SOME a ==> FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+tailoff \/
          b+tailoff+type_memory_size_list tt <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory) /\
      (!aid p n. FLOOKUP q.vs_allocas aid = SOME (p,n) /\
        aid < st.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce (mid with gas_obs := []).scopes q name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory) /\
      locals_kept ce (mid with gas_obs := []) q r)
    (\res ee exit. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) exit)` by
    (simp[] >> first_x_assum (irule o SRULE [] o
       Q.INST [`es'` |-> `mid with gas_obs := []`] o SPEC_ALL o cj 2) >>
     simp[] >> conj_tac >- metis_tac[] >>
     conj_tac >- (fs[Abbr `tailoff`, type_memory_size_def] >> decide_tac) >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `ce.ce_is_ctor ==> !name itv iv io.
           _ /\ FLOOKUP (case ALOOKUP mid.immutables _ of NONE => _ | SOME imms => _) _ = _ ==> _` mp_tac >>
         simp[] >> disch_then drule_all >>
         simp[regions_disjoint_def, type_memory_size_def, Abbr `tailoff`] >> decide_tac) >>
     `sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id` by
       (qpat_x_assum `ci_mono sa st` mp_tac >> simp[ci_mono_def]) >>
     conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
     conj_tac
     >- (qexistsl_tac [`inst`, `Var x`, `x`] >>
         simp[Abbr `tailoff`] >>
         conj_tac >- metis_tac[] >>
         fs[not_fresh_at_def] >> rpt strip_tac >>
         first_x_assum irule >> decide_tac) >>
     fs[]) >>
  irule aggregate_body_read_cons_outcome >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `\vs ee r.
      r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env ee /\
      stmt_state_rel ctx func ce cx ee r /\
      tuple_in_memory vs tt (b+tailoff) r.vs_memory /\
      (!z w. not_fresh_at st z /\ lookup_var z q = SOME w ==> lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP q.vs_allocas aid = SOME a ==> FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+tailoff \/ b+tailoff+type_memory_size_list tt <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory) /\
      (!aid p n. FLOOKUP q.vs_allocas aid = SOME (p,n) /\
        aid < st.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce (mid with gas_obs := []).scopes q name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory) /\
      locals_kept ce (mid with gas_obs := []) q r` >>
  reverse conj_tac >-
    (qpat_x_assum `gas_outcome _ _ _ (eval_exprs _ _) _ _ _` mp_tac >> simp[]) >>
  rpt gen_tac >> simp[] >> strip_tac >> simp[] >>
  conj_tac >- suspend "tuple_memory" >>
  conj_tac >- suspend "lookup_frame" >>
  conj_tac >- suspend "outside_frame" >>
  conj_tac >- suspend "old_frame" >>
  suspend "locals_frame"
QED

Resume aggregate_body_make_tuple_sim[tuple_memory]:
  pure_once_rewrite_tac [val_in_memory_def] >> simp[] >>
  `val_wf ht v` by
    (drule_all aggregate_body_marked_replay >> strip_tac >>
     irule aggregate_materialised_child_wf >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`ce`, `env`] >> simp[]) >>
  irule val_in_memory_mem_agree >> simp[] >>
  qexistsl_tac [`type_memory_size ht`, `q.vs_memory`] >> simp[] >>
  qpat_x_assum `!p n. _ ==> mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory` mp_tac >>
  disch_then (qspecl_then [`b+off`, `type_memory_size ht`] mp_tac) >>
  simp[Abbr `tailoff`]
QED
Resume aggregate_body_make_tuple_sim[lookup_frame]:
  rpt strip_tac >>
  `sa.cs_next_var <= st.cs_next_var` by fs[ci_mono_def] >>
  `not_fresh_at st z` by
    (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  first_x_assum irule >> simp[]
QED
Resume aggregate_body_make_tuple_sim[outside_frame]:
  rpt strip_tac >>
  `mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory` by
    (qpat_x_assum `!p n. _ ==> mem_bytes_at p n r.vs_memory = _` irule >>
     fs[Abbr `tailoff`, type_memory_size_def] >> decide_tac) >>
  simp[] >>
  qpat_x_assum `!p n. _ ==> mem_bytes_at p n q.vs_memory = _` irule >>
  fs[type_memory_size_def, Abbr `tailoff`] >> decide_tac
QED
Resume aggregate_body_make_tuple_sim[old_frame]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule_all aggregate_body_marked_replay >>
     disch_then assume_tac >> drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `!name lo sz. local_region ce mid.scopes q name lo sz ==>
      local_region ce es.scopes s0 name lo sz` by
    (rpt strip_tac >> irule local_region_frame >> conj_tac
     >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sa`, `mid.scopes`, `q`] >> simp[]) >>
  `mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory` by
    (qpat_x_assum `!aid p n. _ ==> mem_bytes_at p n r.vs_memory = _` irule >>
     conj_tac >- (rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
     conj_tac >- (qexists_tac `aid` >> simp[] >> fs[ci_mono_def] >> decide_tac) >>
     simp[]) >>
  simp[] >>
  qpat_x_assum `!aid p n. _ ==> mem_bytes_at p n q.vs_memory = _` irule >>
  conj_tac >-
    (qpat_x_assum `!name lo sz. local_region ce es.scopes s0 name lo sz ==> _` mp_tac >>
     simp[arithmeticTheory.ADD_COMM]) >>
  conj_tac >- (qexists_tac `aid` >> simp[]) >>
  fs[type_memory_size_def] >> decide_tac
QED

Resume aggregate_body_make_tuple_sim[locals_frame]:
  irule locals_kept_trans >>
  qexistsl_tac [`mid with gas_obs := []`, `sa`, `q`] >> simp[] >>
  drule_all aggregate_body_marked_replay >>
  disch_then assume_tac >> drule eval_expr_preserves_scopes_dom >> simp[]
QED

Finalise aggregate_body_make_tuple_sim
