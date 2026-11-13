(* Conditional memory-safe interleaved custom-error stores. *)
Theory stmtSimCustomErrorMemStoreLoop
Ancestors
  stmtLowering stmtLoweringMono exprSimAggregateBodySource exprSimAggregateBodyFrames
  exprSimAggregateBodyCounted exprSimAggregateLoops exprSimAggregateSource
  exprSimAggregateChildren exprSimAggregateEncoding exprSimAggregateLayout
  exprLoweringProps exprSimDefs exprSimHypsDefs exprSimHyps exprSimProps
  exprSimSource loweringPosts compileEnv loweringStateRelDefs
  valueEncoding valueEncodingDefs valueEncodingProps valueEncodingProofs
  gasOutcome gasSummary gasSummaryCompose fragGasMode fragGasPath fragExec
  vyperInterpreter vyperState vyperImmutableMetadataFrame
  vyperEvalExprPreservesScopesDom exprBopSimProps exprSimMemDefs
  bodyMemoryPreds bodyMemoryDefs exprSimSubscriptMap stmtReasonVvMemory
  fragGasPathMem allocaHistory gasExemptCert exprSimMemorySource
Libs monadsyntax

(* The existing cons boundary is F-specific.  Reuse the generic bind
   boundary for the expression and keep only this list-valued read adapter. *)
Theorem custom_error_mem_read_cons_outcome[local]:
  read_result cx tv es = (INL v,es) /\
  gas_marked_path memory ctx func t 0 (OK q) /\
  gas_outcome memory tops (ctx,func) (eval_exprs cx args)
    (es with gas_obs := [],q)
    (\res ee r. ?vs. res = INL vs /\ P vs ee r)
    (\res ee r. ?exc. res = INR exc /\ R (INR exc) ee r) /\
  (!vs ee r. P vs ee r ==> Q (INL (v::vs)) ee r) ==>
  gas_outcome memory tops (ctx,func)
    (bind (read_result cx tv)
      (\v. bind (eval_exprs cx args) (\vs. return (v::vs))))
    (es,t) Q R
Proof
  strip_tac >>
  `gas_marked_exec memory (ctx,func) (read_result cx tv) (es,t)
      [] (INL v) es (OK q)` by
    (simp[gas_marked_exec_def] >> metis_tac[read_result_gas_obs]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "normal"
      >> suspend "exit") >>
  suspend "exempt"
QED
Resume custom_error_mem_read_cons_outcome[normal]:
  gvs[] >>
  `gas_marked_exec memory (ctx,func)
      (bind (eval_exprs cx args) (\vs. return (v::vs)))
      (es with gas_obs := [],q) marks (INL (v::vs)) es_end (OK t')` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >> simp[bind_def, return_def]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (v::vs)`, `es_end`, `OK t'`] >> simp[] >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`] (SPEC_ALL gas_marked_exec_bind_normal))) >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume custom_error_mem_read_cons_outcome[exit]:
  gvs[] >>
  `gas_marked_exec memory (ctx,func)
      (bind (eval_exprs cx args) (\vs. return (v::vs)))
      (es with gas_obs := [],q) marks (INR exc) es_end r` by
    (irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end`, `r`] >> simp[] >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`] (SPEC_ALL gas_marked_exec_bind_normal))) >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume custom_error_mem_read_cons_outcome[exempt]:
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
  simp[bind_assoc, bind_return] >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`] (SPEC_ALL gas_exempt_cert_bind_value))) >>
  goal_assum (drule_at Any) >> simp[GSYM ignore_bind_def]
QED
Finalise custom_error_mem_read_cons_outcome

Theorem custom_error_store_args_sim_mem_using_head:
  (!ce e sa vv sm off x dst sn op su st cx env es s0 ctx func marks tvv mid r
    inst b asz tv.
    compile_expr ce (expr_type e) e sa = (vv,sm) /\
    (if off = 0 then comp_return (Var x)
     else emit_op ADD [Var x; Lit (n2w off)]) sm = (dst,sn) /\
    unwrap_value ce vv sn = (op,su) /\
    compile_store_memory ce op dst (expr_type e) (lowered_value_type ce e)
      su = ((),st) /\
    expr_body_pre ce cx env e es /\
    gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
      marks (INL tvv) mid (OK r) /\
    vv_post ctx func ce cx e es sa sm s0 (mid with gas_obs := []) tvv vv r /\
    vv_store_bound cx (expr_type e) (lowered_value_type ce e)
      (mid with gas_obs := []) tvv vv r /\
    alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next /\
    (int_calls_expr e <> [] /\ lowered_value_type ce e <> expr_type e ==>
      acyclic_struct_metadata ce.ce_struct_fields) /\
    fn_has_code sa st func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
    inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
    (!ee. expr_sim_inv ce cx env ee ==> not_local_ptr ce ee.scopes x) /\
    not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    off + type_memory_size tv <= asz /\ b+asz < dimword (:256) /\
    (ce.ce_is_ctor ==> !name itv iv io.
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name =
        SOME (itv,iv) ==>
      regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size tv)) /\
    stmt_state_rel ctx func ce cx es s0 /\ ~r.vs_halted /\
    r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?v q.
      read_result cx tvv (mid with gas_obs := []) =
        (INL v,mid with gas_obs := []) /\
      expr_sim_inv ce cx env (mid with gas_obs := []) /\
      gas_marked_path T ctx func r 0 (OK q) /\
      ~q.vs_halted /\ q.vs_current_bb = st.cs_current_bb /\
      q.vs_inst_idx = LENGTH st.cs_current_insts /\
      alloca_history func q /\ r.vs_alloca_next <= q.vs_alloca_next /\
      val_in_memory tv v (b+off) q.vs_memory /\
      stmt_state_rel ctx func ce cx (mid with gas_obs := []) q /\
      (!z a. not_fresh_at sa z /\ lookup_var z s0 = SOME a ==>
        lookup_var z q = SOME a) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP q.vs_allocas aid = SOME a) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) /\
        (p+n <= b+off \/ b+off+type_memory_size tv <= p) ==>
        mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+type_memory_size tv <= p) ==>
        mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es (mid with gas_obs := []) s0 q /\
      (~expr_has_effect e ==>
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          mem_bytes_at lo sz q.vs_memory = mem_bytes_at lo sz s0.vs_memory) /\
        (!p n. (p+n <= b \/ b+asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
            sa.cs_next_id <= i.inst_id /\
            FLOOKUP q.vs_allocas i.inst_id = SOME (c,sz) ==>
            regions_disjoint p n c sz) ==>
          mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory))) ==>
  !args ce cx env off sa sb es tvs func inst x b asz s0 ctx tys tops.
  tys = MAP expr_type args /\
  compile_custom_error_store_args ce args tys (Var x) off sa = ((),sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
  expr_sim_inv ce cx env es /\
  (!e ee. MEM e args /\ expr_sim_inv ce cx env ee ==>
    expr_body_pre ce cx env e ee) /\
  body_exprs_mem_ok cx args /\ body_inv tops ctx ce cx /\
  (!e. MEM e args ==> (int_calls_expr e <> [] /\
    lowered_value_type ce e <> expr_type e ==>
    acyclic_struct_metadata ce.ce_struct_fields)) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!ee. expr_sim_inv ce cx env ee ==> not_local_ptr ce ee.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + type_memory_size_list tvs <= asz /\ b+asz < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name =
      SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size_list tvs)) /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
    (\res ee r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env ee /\
      stmt_state_rel ctx func ce cx ee r /\
      alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next /\
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
      locals_kept ce es ee s0 r /\
      (EVERY ($~ o expr_has_effect) args ==>
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          mem_bytes_at lo sz r.vs_memory = mem_bytes_at lo sz s0.vs_memory) /\
        (!p n. (p+n <= b \/ b+asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
            sa.cs_next_id <= i.inst_id /\
            FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
            regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory)))
    (\res ee exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  disch_then (mk_asm "head") >>
  Induct_on `args`
  >- (asm_x "head" kall_tac >> rpt gen_tac >> simp[compile_custom_error_store_args_def, comp_return_def] >>
      strip_tac >> gvs[] >>
      rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INL []`, `es`, `OK s0`] >>
      fs[gas_marked_exec_def, evaluate_def, return_def,
         gas_marked_path_def, gas_path_mem_rules, val_in_memory_def,
         locals_kept_def, stmt_state_rel_def, state_rel_gas_obs,
         immutable_alloca_sep_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> qpat_x_assum `tys = _` SUBST_ALL_TAC >>
  Cases_on `compile_expr ce (expr_type h) h sa` >>
  rename1 `compile_expr ce (expr_type h) h sa = (vv,sm)` >>
  Cases_on `(if off = 0 then comp_return (Var x)
    else emit_op ADD [Var x; Lit (n2w off)]) sm` >>
  rename1 `(if off = 0 then comp_return (Var x)
    else emit_op ADD [Var x; Lit (n2w off)]) sm = (dst,sn)` >>
  Cases_on `unwrap_value ce vv sn` >>
  rename1 `unwrap_value ce vv sn = (op,su)` >>
  Cases_on `compile_store_memory ce op dst (expr_type h) (lowered_value_type ce h) su` >>
  rename1 `compile_store_memory ce op dst (expr_type h) (lowered_value_type ce h) su = (unit,st)` >>
  Cases_on `unit` >>
  qpat_x_assum `compile_custom_error_store_args _ (_::_) _ _ _ _ = _` mp_tac >>
  simp[Once compile_custom_error_store_args_def, comp_bind_def, comp_ignore_bind_def] >>
  strip_tac >> suspend "step"
QED
Resume custom_error_store_args_sim_mem_using_head[step]:
  `ci_mono sa sm /\ ci_mono sn su /\ ci_mono su st /\ ci_mono st sb` by
    (asm_x "head" kall_tac >>
     metis_tac[compile_expr_ci_mono, ci_mono_unwrap_value,
       ci_mono_compile_store_memory, cj 1 ci_mono_custom_error, pairTheory.SND]) >>
  `ci_mono sm sn` by
    (asm_x "head" kall_tac >> Cases_on `off = 0` >>
     gvs[comp_return_def] >> metis_tac[ci_mono_emit_op, pairTheory.SND, ci_mono_refl]) >>
  `fn_has_code sa sm func /\ fn_has_code st sb func /\ fn_has_code sa st func` by
    (asm_x "head" kall_tac >>
     metis_tac[fn_has_code_split, ci_mono_def, cs_extends_trans]) >>
  `expr_body_pre ce cx env h es` by
    (asm_x "head" kall_tac >> metis_tac[listTheory.MEM]) >>
  `gas_admissible (eval_expr cx h) expr_vv_res_ok es` by
    (asm_x "head" kall_tac >> metis_tac[expr_body_pre_vv_gas_admissible]) >>
  `gas_outcome T (cx_tops cx) (ctx,func) (eval_expr cx h) (es,s0)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func ce cx h es sa sm s0 ee tv vv t /\
      vv_store_bound cx (expr_type h) (lowered_value_type ce h) ee tv vv t /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)` by
    (asm_x "head" kall_tac >> fs[body_exprs_mem_ok_def, body_expr_mem_ok_def] >>
     first_x_assum (drule_at (Pat `body_inv _ _ _ _`)) >>
     disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
     simp[expr_vv_sim_mem_def] >> strip_tac >> metis_tac[]) >>
  once_rewrite_tac[evaluate_def] >>
  irule gas_outcome_bind_result_exec >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (Cases >> simp[expr_exit_INL]) >>
  reverse conj_tac >- (rpt gen_tac >> strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `?ht tt. evaluate_type (get_tenv cx) (expr_type h) = SOME ht /\
    OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tt /\
    tvs = ht::tt` by fs[] >> gvs[] >>
  `type_memory_bytes ce (expr_type h) = type_memory_size ht` by
    (asm_x "head" kall_tac >>
     metis_tac[expr_sim_inv_memory_size, expr_body_pre_def]) >>
  `off + type_memory_size ht <= asz` by
    (fs[type_memory_size_def] >> decide_tac) >>
  `ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size ht)` by
    (fs[type_memory_size_def, regions_disjoint_def] >> rpt strip_tac >>
     first_x_assum drule >> disch_then drule_all >> strip_tac >> decide_tac) >>
  `~t.vs_halted` by
    (asm_x "head" kall_tac >>
     metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal]) >>
  `int_calls_expr h <> [] /\ lowered_value_type ce h <> expr_type h ==>
    acyclic_struct_metadata ce.ce_struct_fields` by
    (asm_x "head" kall_tac >> metis_tac[]) >>
  `expr_body_pre ce cx env h es` by
    (asm_x "head" kall_tac >> metis_tac[]) >>
  `b+asz < dimword (:256)` by decide_tac >>
  asm_x "head" (drule_all_then strip_assume_tac) >>
  suspend "tail"
QED
Resume custom_error_store_args_sim_mem_using_head[tail]:
  `body_exprs_mem_ok cx args` by
    (drule aggregate_body_marked_replay >> strip_tac >>
     fs[body_exprs_mem_ok_def] >> metis_tac[]) >>
  `ci_mono sa sn /\ ci_mono sa su /\ ci_mono sa st` by
    metis_tac[aggregate_body_ci_mono_trans] >>
  `immutable_metadata_frame es mid` by
    (drule_all aggregate_body_marked_replay >> strip_tac >>
     drule eval_expr_immutable_metadata_frame >>
     simp[immutable_metadata_frame_def] >> metis_tac[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule_all aggregate_body_marked_replay >> strip_tac >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size_list (ht::tt))` by
    (strip_tac >> ho_match_mp_tac immutable_metadata_frame_property >> simp[] >>
     qpat_x_assum `ce.ce_is_ctor ==> !name itv iv io. _ ==> regions_disjoint _ _ _ (type_memory_size_list _)` mp_tac >>
     simp[]) >>
  qabbrev_tac `tailoff = off + type_memory_size ht` >>
  qabbrev_tac `Post = \vs ee r.
    r.vs_current_bb = sb.cs_current_bb /\
    r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env ee /\
    stmt_state_rel ctx func ce cx ee r /\
    alloca_history func r /\ q.vs_alloca_next <= r.vs_alloca_next /\
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
    locals_kept ce (mid with gas_obs := []) ee q r /\
    (EVERY ($~ o expr_has_effect) args ==>
      (!name lo sz. local_region ce (mid with gas_obs := []).scopes q name lo sz ==>
        mem_bytes_at lo sz r.vs_memory = mem_bytes_at lo sz q.vs_memory) /\
      (!p n. (p+n <= b \/ b+asz <= p) /\
        (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
          st.cs_next_id <= i.inst_id /\
          FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
          regions_disjoint p n c sz) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory))` >>
  `gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx args)
    (mid with gas_obs := [],q)
    (\res ee r. ?vs. res = INL vs /\ Post vs ee r)
    (\res ee exit. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) exit)` by
    (simp[Abbr `Post`] >>
     first_x_assum (irule o SRULE [] o
       Q.INST [`es'` |-> `mid with gas_obs := []`] o SPEC_ALL) >>
     simp[] >> conj_tac >- metis_tac[] >>
     conj_tac >- (fs[Abbr `tailoff`, type_memory_size_def] >> decide_tac) >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `ce.ce_is_ctor ==> !name itv iv io.
           _ /\ FLOOKUP (case ALOOKUP mid.immutables _ of NONE => _ | SOME imms => _) _ = _ ==> _` mp_tac >>
         simp[] >> disch_then drule_all >>
         simp[regions_disjoint_def, type_memory_size_def, Abbr `tailoff`] >> decide_tac) >>
     `sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id` by
       fs[ci_mono_def] >>
     conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
     conj_tac
     >- (qexistsl_tac [`inst`, `x`] >> simp[Abbr `tailoff`] >>
         conj_tac >- metis_tac[] >>
         fs[not_fresh_at_def] >> rpt strip_tac >>
         first_x_assum irule >> decide_tac) >> fs[] >> metis_tac[]) >>
  irule custom_error_mem_read_cons_outcome >>
  goal_assum (drule_at Any) >> simp[] >> qexists_tac `Post` >>
  reverse conj_tac
  >- (qpat_x_assum `gas_outcome _ _ _ (eval_exprs _ _) _ _ _` mp_tac >> simp[]) >>
  rpt gen_tac >> simp[Abbr `Post`] >> strip_tac >> simp[] >>
  conj_tac >- suspend "tuple_memory" >>
  conj_tac >- suspend "lookup_frame" >>
  conj_tac >- suspend "outside_frame" >>
  conj_tac >- suspend "old_frame" >>
  conj_tac >- suspend "locals_frame" >>
  suspend "pure_frame"
QED
Resume custom_error_store_args_sim_mem_using_head[tuple_memory]:
  pure_once_rewrite_tac [val_in_memory_def] >> simp[] >>
  `val_wf ht v'` by
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
Resume custom_error_store_args_sim_mem_using_head[lookup_frame]:
  rpt strip_tac >>
  `sa.cs_next_var <= st.cs_next_var` by fs[ci_mono_def] >>
  `not_fresh_at st z` by
    (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  first_x_assum irule >> simp[]
QED
Resume custom_error_store_args_sim_mem_using_head[outside_frame]:
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory` by
    (qpat_x_assum `!p n. _ ==> mem_bytes_at p n r.vs_memory = _` irule >>
     fs[Abbr `tailoff`, type_memory_size_def] >> decide_tac) >>
  simp[] >>
  qpat_x_assum `!p n. _ ==> mem_bytes_at p n q.vs_memory = _` irule >>
  fs[type_memory_size_def, Abbr `tailoff`] >> decide_tac
QED
Resume custom_error_store_args_sim_mem_using_head[old_frame]:
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
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
Resume custom_error_store_args_sim_mem_using_head[locals_frame]:
  irule locals_kept_trans >>
  qexistsl_tac [`mid with gas_obs := []`, `sa`, `q`] >> simp[]
QED
Resume custom_error_store_args_sim_mem_using_head[pure_frame]:
  strip_tac >>
  `~expr_has_effect h /\ EVERY ($~ o expr_has_effect) args` by fs[] >>
  `sa.cs_next_id <= st.cs_next_id` by fs[ci_mono_def] >>
  qpat_x_assum `~expr_has_effect h ==> _` mp_tac >> simp[] >> strip_tac >>
  qpat_x_assum `EVERY _ args ==> _` mp_tac >> simp[] >> strip_tac >>
  match_mp_tac (SRULE [arithmeticTheory.ADD_COMM] aggregate_pure_frame_trans) >>
  qexistsl_tac [`mid with gas_obs := []`, `st`, `q`] >> simp[] >>
  rpt conj_tac >> first_assum (MATCH_ACCEPT_TAC o SRULE [arithmeticTheory.ADD_COMM])
QED
Finalise custom_error_store_args_sim_mem_using_head
