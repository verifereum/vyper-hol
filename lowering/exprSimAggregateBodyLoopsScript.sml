(* Counted aggregate loops using the physical-layout child-store boundary. *)
Theory exprSimAggregateBodyLoops
Ancestors
  exprSimAggregateBodyHeader stmtSimDeclCompose stmtSimDeclPath emitHelper venomInst venomState
  exprSimAggregateBodyHead exprSimAggregateBodySource exprSimAggregateBodyFrames
  exprSimAggregateBodyCounted exprSimAggregateLoops exprSimAggregateSource
  exprSimAggregateEncoding exprSimAggregateLayout exprLoweringProps
  exprSimDefs exprSimHypsDefs exprSimHyps exprSimProps exprSimSource loweringPosts
  compileEnv exprLowering valueEncoding valueEncodingProps valueEncodingProofs
  gasOutcome gasSummary gasSummaryCompose fragGasMode fragGasPath fragExec
  vyperInterpreter vyperState vyperImmutableMetadataFrame
  vyperEvalExprPreservesScopesDom exprBopSimProps exprSimMemDefs
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

Theorem aggregate_body_make_array_elems_sim:
  !args ce cx env elem_ty tv header idx off sa out sb es func inst x b asz s0 ctx.
  EVERY (\e. expr_type e = elem_ty) args /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  type_memory_bytes ce elem_ty = type_memory_size tv /\
  off = (if header then 32 else 0) + idx * type_memory_size tv /\
  compile_make_array_elems compile_expr ce args elem_ty
    (type_memory_bytes ce elem_ty) header (Var x) idx sa = (out,sb) /\
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
  off + LENGTH args * type_memory_size tv <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off)
       (LENGTH args * type_memory_size tv)) /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
    (\res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' r /\
      elems_in_memory vs (b+off) tv r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+LENGTH args * type_memory_size tv <= p) ==>
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
  rpt gen_tac >> strip_tac >>
  `compile_make_tuple compile_expr ce args (Var x) off sa = (out,sb)` by
    (drule compile_make_array_elems_as_tuple >> simp[] >> metis_tac[]) >>
  `OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) =
    SOME (REPLICATE (LENGTH args) tv)` by
    (irule OPT_MMAP_uniform_map >> metis_tac[]) >>
  drule_at (Pat `compile_make_tuple _ _ _ _ _ _ = _`) aggregate_body_make_tuple_sim >>
  disch_then (drule_at (Pat `OPT_MMAP _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`env`, `inst`, `b`, `asz`] mp_tac) >>
  simp[type_memory_size_list_replicate] >>
  (impl_tac >-
    (conj_tac >- (qpat_x_assum `!e. MEM e args ==> _` mp_tac >> simp[]) >>
     conj_tac >- (gvs[] >> decide_tac) >>
     qpat_x_assum `ce.ce_is_ctor ==> _` mp_tac >>
     simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM])) >>
  strip_tac >> simp[] >>
  drule gas_outcome_source_invariant >>
  disch_then (qspec_then `\res. !vs. res = INL vs ==> LENGTH vs = LENGTH args` mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >> gvs[] >> drule eval_exprs_length >> simp[])) >>
  strip_tac >>
  irule gas_outcome_post_mono >> goal_assum (drule_at Any) >>
  rpt gen_tac >> disch_then assume_tac >>
  gvs[SF CONJ_ss] >>
  fs[GSYM tuple_in_memory_replicate_elems] >>
  metis_tac[]
QED


Theorem aggregate_body_make_array_sim:
  !args ce cx env elem_ty tv stride header sa out sb es func inst x b asz s0 ctx.
  EVERY (\e. expr_type e = elem_ty) args /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  stride = type_memory_size tv /\
  type_memory_bytes ce elem_ty = type_memory_size tv /\
  compile_make_array compile_expr ce args elem_ty stride header (Var x) sa = (out,sb) /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  exprs_case F ctx func ce cx args /\
  (!e. MEM e args ==> (int_calls_expr e <> [] /\
    lowered_value_type ce e <> expr_type e ==> acyclic_struct_metadata ce.ce_struct_fields)) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  (if header then 32 else 0) + LENGTH args * type_memory_size tv <= asz /\
  b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) b
      ((if header then 32 else 0) + LENGTH args * type_memory_size tv)) /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
    (\res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' r /\
      elems_in_memory vs (b+(if header then 32 else 0)) tv r.vs_memory /\
      (header ==> mem_word_at b r.vs_memory = n2w (LENGTH args)) /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b \/ b+(if header then 32 else 0)+LENGTH args * type_memory_size tv <= p) ==>
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
  rpt gen_tac >> strip_tac >> Cases_on `header`
  >- suspend "dynamic"
  >> gvs[compile_make_array_def, comp_ignore_bind_def, comp_bind_def, comp_return_def]
  >> drule aggregate_body_make_array_elems_sim
  >> disch_then (drule_at (Pat `evaluate_type _ _ = _`))
  >> disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`))
  >> disch_then (qspec_then `env` mp_tac) >> simp[]
  >> disch_then (drule_at (Pat `compile_make_array_elems _ _ _ _ _ _ _ _ _ = _`))
  >> disch_then (qspecl_then [`inst`,`b`,`asz`] mp_tac) >> simp[]
  >> (impl_tac >- metis_tac[]) >> simp[]
QED

Resume aggregate_body_make_array_sim[dynamic]:
  gvs[compile_make_array_def, comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >> rename1 `emit_void _ _ sa = ((),sm)` >>
  `compile_make_tuple compile_expr ce args (Var x) 32 sm = (out,sb)` by
    (drule compile_make_array_elems_as_tuple >>
     disch_then (qspecl_then [`T`, `compile_expr`, `ce`, `Var x`, `0`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `ci_mono sa sm` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `ci_mono sm sb` by metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `sm.cs_next_var = sa.cs_next_var /\ sm.cs_next_id = SUC sa.cs_next_id /\
   sm.cs_current_bb = sa.cs_current_bb /\
   LENGTH sm.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> gvs[]) >>
  qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ _ (es,s0) Q R` >>
  `b < dimword (:256)` by decide_tac >>
  `gas_marked_path F ctx func s0 0
    (OK (mstore b (n2w (LENGTH args)) s0 with vs_inst_idx := LENGTH sm.cs_current_insts))` by
    (drule emit_mstore_marked_path >>
     disch_then (drule_at (Pat `fn_has_code _ _ _`)) >> simp[eval_operand_def] >>
     disch_then (qspecl_then [`n2w b`, `s0`, `ctx`] mp_tac) >> simp[]) >>
  qabbrev_tac `s1 = mstore b (n2w (LENGTH args)) s0 with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  `stmt_state_rel ctx func ce cx es (mstore b (n2w (LENGTH args)) s0) /\
   locals_kept ce es s0 (mstore b (n2w (LENGTH args)) s0) /\
   mem_word_at b (mstore b (n2w (LENGTH args)) s0).vs_memory = n2w (LENGTH args)` by
    (drule aggregate_body_header_store_boundary >>
     disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (b,asz)`)) >>
     simp[] >> (impl_tac >-
       (rpt strip_tac >> first_x_assum drule_all >>
        simp[regions_disjoint_def] >> decide_tac)) >> simp[]) >>
  `stmt_state_rel ctx func ce cx es s1` by
    (simp[Abbr `s1`, stmt_state_rel_inst_idx]) >>
  `local_ptrs_reserved ce sm /\ not_fresh_at sm x /\ inst.inst_id < sm.cs_next_id` by
    (conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
     conj_tac >- (qpat_x_assum `not_fresh_at sa x` mp_tac >> simp[not_fresh_at_def]) >> decide_tac) >>
  `lookup_var x s1 = SOME (n2w b) /\
   FLOOKUP s1.vs_allocas inst.inst_id = SOME (b,asz) /\
   ~s1.vs_halted /\ s1.vs_current_bb = sm.cs_current_bb /\
   s1.vs_inst_idx = LENGTH sm.cs_current_insts` by
    (simp[Abbr `s1`, mstore_def, lookup_var_def] >> fs[lookup_var_def]) >>
  drule aggregate_body_make_array_elems_sim >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (qspec_then `ce` mp_tac) >> simp[] >>
  disch_then (drule_at (Pat `compile_make_array_elems _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ s1`)) >>
  disch_then (qspecl_then [`env`, `inst`, `b`, `asz`] mp_tac) >>
  simp[] >>
  (impl_tac >-
    (conj_tac >- metis_tac[] >> rpt strip_tac >>
     first_x_assum drule_all >> simp[regions_disjoint_def] >> decide_tac)) >>
  strip_tac >> simp[] >>
  irule gas_outcome_zero_prefix >> qexists_tac `s1` >> simp[] >>
  irule gas_outcome_post_mono >> goal_assum (drule_at Any) >>
  rpt gen_tac >> strip_tac >> gvs[Abbr `Q`, SF CONJ_ss] >>
  conj_tac
  >- (`mem_bytes_at b 32 t.vs_memory = mem_bytes_at b 32 s1.vs_memory` by
        (qpat_x_assum `!p n. b <= p /\ _ ==> _` irule >> decide_tac) >>
      fs[mem_word_at_def, GSYM mem_bytes_at_def, Abbr `s1`]) >>
  conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!z w. not_fresh_at sm z /\ _ ==> _` irule >>
      simp[not_fresh_at_def, Abbr `s1`, mstore_def, lookup_var_def] >>
      fs[not_fresh_at_def, lookup_var_def]) >>
  conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!aid a. _ ==> FLOOKUP t.vs_allocas aid = _` irule >>
      simp[Abbr `s1`, mstore_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at p n t.vs_memory = mem_bytes_at p n s1.vs_memory` by
        (qpat_x_assum `!p n. b <= p /\ _ ==> _` irule >> decide_tac) >>
      simp[Abbr `s1`] >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at p n t.vs_memory = mem_bytes_at p n s1.vs_memory` by
        (qpat_x_assum `!aid p n. _ ==> _` irule >>
         conj_tac >-
           (simp[Abbr `s1`, local_region_def, mstore_def, lookup_var_def] >>
            fs[local_region_def, lookup_var_def] >> metis_tac[]) >>
         conj_tac >- (qexists_tac `aid` >> simp[Abbr `s1`, mstore_def]) >> simp[]) >>
      simp[Abbr `s1`] >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  qpat_x_assum `locals_kept ce es s1 t` mp_tac >>
  qpat_x_assum `locals_kept ce es s0 _` mp_tac >>
  simp[locals_kept_def, Abbr `s1`, local_region_def, lookup_var_def, mstore_def] >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `mem_bytes_at _ _ M = mem_bytes_at _ _ s0.vs_memory` >>
  metis_tac[]
QED

Finalise aggregate_body_make_array_sim
