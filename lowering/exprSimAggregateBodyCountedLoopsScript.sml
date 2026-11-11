Theory exprSimAggregateBodyCountedLoops
Ancestors
  aggregateCountedPureFramePrep
  exprSimAggregateBodyCountedChildren exprSimAggregateLoops exprLowering
  compileEnv loweringStateRelDefs exprLoweringProps emitHelper list exprSimSource exprSimHypsDefs exprSimDefs
  vyperImmutableMetadataFrame vyperEvalExprPreservesScopesDom gasSummary gasContext
  exprSimAggregateChildren emitHelperProps exprSimVVFrame fragGasMode
  exprSimProps loweringPosts stmtSimDefs valueEncodingProofs
  aggregateCountedOutcome aggregateEvaluatedLayout exprSimAggregateLayout
  vyperInterpreter vyperState valueEncoding valueEncodingDefs exprSimUnwrap fragExec
  venomExecSemantics venomInstProofs venomInst venomState gasExemptCert
  stmtReasonVvMemory exprSimWordArgs fragGasPath exprOperandVar
  valueEncodingTyping exprSimHyps exprSimMemorySource valueEncodingProps exprBopSimProps
Libs
  monadsyntax


Theorem aggregate_make_tuple_body_sim:
  !args ce cx env off sa out sb es tvs func inst x b asz s0 ctx.
  compile_make_tuple compile_expr ce args (Var x) off sa = (out,sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  exprs_case F ctx func ce cx args /\
  (!e. MEM e args /\ int_calls_expr e <> [] /\
     lowered_value_type ce e <> expr_type e ==>
     acyclic_struct_metadata ce.ce_struct_fields) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + type_memory_size_list tvs <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size_list tvs)) /\
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
      locals_kept ce es es' s0 r)
    (\res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  Induct_on `args`
  >- (rpt gen_tac >>
      simp[Once compile_make_tuple_def, comp_return_def] >>
      strip_tac >> gvs[] >>
      simp[Once evaluate_def] >>
      irule counted_outcome_return >>
      simp[expr_sim_inv_gas_obs, val_in_memory_def, locals_kept_def, popped_kept_def]) >>
  suspend "cons"
QED

Resume aggregate_make_tuple_body_sim[cons]:
  rpt gen_tac >> strip_tac >>
  drule aggregate_tuple_body_cons_compile >> strip_tac >>
  `expr_body_pre ce cx env h es` by metis_tac[listTheory.MEM] >>
  drule compile_expr_extends >> strip_tac >>
  `ci_mono sm sn` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sn su` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `ci_mono su st` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `ci_mono st sb` by
    (qspec_then `compile_expr` mp_tac ci_mono_compile_make_tuple_cfn >>
     simp[cj 1 compile_expr_ci_mono] >>
     disch_then (qspecl_then
       [`ce`, `args`, `Var x`, `off + type_memory_bytes ce (expr_type h)`, `st`]
       mp_tac) >> simp[]) >>
  conj_tac >- suspend "result" >>
  `cs_extends sm sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  drule_all (SRULE [] (Q.INST [`nocalls` |-> `F`]
    aggregate_body_tuple_child_outcome)) >> disch_tac >>
  pure_rewrite_tac[Once evaluate_def] >>
  irule counted_outcome_bind_exec >>
  conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_result >> goal_assum (drule_at Any) >>
      gvs[GSYM ignore_bind_def]) >>
  conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_error_result >> simp[]) >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac
  >- (Cases >> simp[expr_exit_def]) >>
  reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  drule_all aggregate_body_tuple_marked_child_source >> strip_tac >>
  drule vv_post_read_ok >> disch_then (qx_choose_then `hv` assume_tac) >>
  `value_has_type tvt hv` by metis_tac[] >>
  `~t.vs_halted /\ stmt_state_rel ctx func ce cx (mid with gas_obs := []) t /\
   lookup_var x t = SOME (n2w b)` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once vv_post_def] >> strip_tac >> simp[] >>
     qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, gas_marked_path_def] >>
     metis_tac[gas_path_normal]) >>
  `fn_has_code sm sn func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `eval_operand (Var x) t = SOME (n2w b)` by simp[eval_operand_def] >>
  drule_all aggregate_body_tuple_add_marked >> strip_tac >>
  drule_all aggregate_body_marked_read_source >> disch_tac >>
  `expr_body_pre ce cx env h
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    simp[aggregate_body_pre_gas_obs] >>
  `vv_post ctx func ce cx h
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)
     sa sn s0 (mid with gas_obs := []) v vv q` by
    simp[vv_post_initial_gas] >>
  `stmt_state_rel ctx func ce cx (mid with gas_obs := []) q` by
    (fs[vv_post_def]) >>
  `!tvt. evaluate_type (get_tenv cx) (post_value_type ce h) = SOME tvt /\
     ~is_word_type (post_value_type ce h) ==>
     type_memory_bytes ce (post_value_type ce h) = type_memory_size tvt /\
     type_memory_size tvt < 2 ** 64` by
    (drule body_post_type_allocation_bound >> simp[]) >>
  `!z. op = Var z ==> not_fresh_at su z` by
    (drule aggregate_child_unwrap_var >> simp[] >>
     strip_tac >> rpt strip_tac >> first_x_assum irule >>
     qexists_tac `sn` >> fs[ci_mono_def]) >>
  `local_ptrs_reserved ce sn /\ local_ptrs_reserved ce su` by
    (conj_tac >> irule local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> fs[ci_mono_def] >> decide_tac) >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sn z` by
    (rpt strip_tac >>
     `not_fresh_at sm z` by
       (irule (cj 1 compiler_compile_var) >>
        goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[]) >>
     fs[not_fresh_at_def, ci_mono_def] >> decide_tac) >>
  `val_wf tvt hv` by metis_tac[value_has_type_val_wf] >>
  `type_memory_bytes ce (expr_type h) = type_memory_size tvt` by
    (drule_all expr_sim_inv_memory_size >> simp[]) >>
  `?d. dst = Var d /\ not_fresh_at sn d` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[not_fresh_at_def] >>
     qexists_tac `sm.cs_next_var` >> simp[]) >>
  gvs[] >>
  `off + type_memory_size tvt <= asz /\
   b + off + type_memory_size tvt < dimword (:256)` by
    (fs[type_memory_size_def] >> decide_tac) >>
  `FLOOKUP q.vs_allocas inst.inst_id = SOME (b,asz)` by
    (fs[vv_post_def]) >>
  `not_local_ptr ce mid.scopes x` by
    (first_x_assum irule >> fs[expr_sim_inv_gas_obs]) >>
  `!name lo sz. local_region ce mid.scopes q name lo sz ==>
     lo+sz <= b+off \/ b+off+type_memory_size tvt <= lo` by
    (drule_all aggregate_body_destination_separation >>
     simp[] >> metis_tac[]) >>
  `ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off)
      (type_memory_size_list (tvt::t'))` by
    (mp_tac (Q.INST [`b` |-> `b+off`, `n` |-> `type_memory_size_list (tvt::t')`,
        `e` |-> `h`, `tv` |-> `v`] aggregate_body_tuple_marked_footprint) >>
     (impl_tac >- (simp[] >> metis_tac[])) >>
     simp[]) >>
  `ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size tvt)` by
    (mp_tac (Q.INST [`es` |-> `mid`, `b` |-> `b+off`, `p` |-> `b+off`,
        `n` |-> `type_memory_size_list (tvt::t')`, `len` |-> `type_memory_size tvt`]
       (SPEC_ALL aggregate_body_immutable_slice)) >>
     (impl_tac >- (fs[type_memory_size_def] >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `lookup_var d q = SOME (n2w (b+off))` by
    fs[eval_operand_def, wordsTheory.word_add_n2w] >>
  `w2n (n2w (b+off) : bytes32) = b+off` by
    (simp[wordsTheory.w2n_n2w] >> irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  `fn_has_code sn su func /\ fn_has_code su st func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `expr_body_pre ce cx env h
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    (simp[] >> first_x_assum irule >> simp[]) >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    aggregate_body_child_store_slice_marked >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  simp[] >>
  (impl_tac >- (fs[ci_mono_def] >> rpt conj_tac >>
    first_assum MATCH_ACCEPT_TAC)) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `not_fresh_at sm x /\ not_fresh_at sn x /\ not_fresh_at st x` by
    (fs[not_fresh_at_def, ci_mono_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `lookup_var x u = SOME (n2w b)` by metis_tac[] >>
  `FLOOKUP u.vs_allocas inst.inst_id = SOME (b,asz)` by metis_tac[vv_post_def] >>
  `fn_has_code st sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `local_ptrs_reserved ce st` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     fs[ci_mono_def] >> decide_tac) >>
  `ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+(off+type_memory_size tvt))
      (type_memory_size_list t')` by
    (mp_tac (Q.INST [`es` |-> `mid`, `b` |-> `b+off`,
       `n` |-> `type_memory_size_list (tvt::t')`,
       `p` |-> `b+(off+type_memory_size tvt)`, `len` |-> `type_memory_size_list t'`]
       (SPEC_ALL aggregate_body_immutable_slice)) >>
     (impl_tac >- (fs[type_memory_size_def] >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `stmt_state_rel ctx func ce cx (mid with gas_obs := []) u` by simp[] >>
  `expr_sim_inv ce cx env (mid with gas_obs := [])` by simp[expr_sim_inv_gas_obs] >>
  first_x_assum
    (drule_at (Pat `compile_make_tuple _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `OPT_MMAP _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = _`)) >>
  simp[] >>
  (impl_tac >-
    (conj_tac
     >- (fs[exprs_case_def] >> first_x_assum irule >>
         fs[gas_marked_exec_def] >> metis_tac[]) >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (fs[ci_mono_def] >> decide_tac) >>
     conj_tac >- fs[type_memory_size_def] >>
     first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `gas_marked_path F ctx func t 0 (OK u)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `gas_marked_exec F (ctx,func) (read_result cx v)
     (mid with gas_obs := [],t) [] (INL hv) (mid with gas_obs := []) (OK u)` by
    (simp[gas_marked_exec_def] >> drule read_result_gas_obs >> simp[]) >>
  irule counted_outcome_prefix >>
  goal_assum (drule_at Any) >>
  conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_value >>
      goal_assum (drule_at Any) >>
      fs[ignore_bind_def, bind_assoc] >> first_assum ACCEPT_TAC) >>
  simp[] >> irule counted_outcome_bind_exec >>
  conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_values >> goal_assum (drule_at Any) >>
      gvs[GSYM ignore_bind_def]) >>
  conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_error_values >> simp[]) >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (rpt strip_tac >> irule counted_outcome_return >>
    conj_tac >- (fs[gas_marked_exec_def] >>
      metis_tac[gas_marked_path_exec, gas_path_normal]) >>
    simp[] >> conj_tac
    >- (`mem_bytes_at (b+off) (type_memory_size tvt) t''.vs_memory =
           mem_bytes_at (b+off) (type_memory_size tvt) u.vs_memory` by
          (qpat_x_assum `!p n. _ ==> mem_bytes_at p n t''.vs_memory = _` irule >>
           fs[type_memory_size_def]) >>
        simp[Once val_in_memory_def] >>
        irule val_in_memory_relocate >>
        conj_tac >- metis_tac[value_has_type_val_wf] >>
        qexistsl_tac [`u.vs_memory`, `type_memory_size tvt`, `b+off`] >>
        simp[]) >>
    conj_tac
    >- (rpt strip_tac >>
        `not_fresh_at sn z /\ not_fresh_at st z` by
          (fs[not_fresh_at_def, ci_mono_def] >> decide_tac) >>
        `lookup_var z q = SOME w` by (fs[vv_post_def] >> metis_tac[]) >>
        `lookup_var z u = SOME w` by metis_tac[] >> metis_tac[]) >>
    conj_tac
    >- (rpt strip_tac >>
        `FLOOKUP t.vs_allocas aid = SOME a` by (fs[vv_post_def] >> metis_tac[]) >>
        metis_tac[]) >>
    `!name lo sz. local_region ce es.scopes s0 name lo sz ==>
       b+asz <= lo \/ lo+sz <= b` by
      (`not_local_ptr ce es.scopes x` by metis_tac[] >>
       qpat_assum `stmt_state_rel ctx func ce cx es s0`
         (mp_then Any mp_tac (Q.INST [`off` |-> `0`, `n` |-> `asz`]
            aggregate_body_destination_separation)) >>
       simp[] >> strip_tac >>
       first_x_assum (qspecl_then [`x`, `inst`, `b`, `asz`] mp_tac) >>
       simp[] >> metis_tac[]) >>
    qpat_x_assum `vv_post _ _ _ _ _ (_ with gas_obs := gas_explicit _ _) _ _ _ _ _ _ _` kall_tac >>
    `(!p n. b <= p /\ p+n <= b+asz /\
       (p+n <= b+off \/ b+off+type_memory_size tvt <= p) ==>
       mem_bytes_at p n u.vs_memory = mem_bytes_at p n s0.vs_memory) /\
     (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
       aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
       (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
         p+n <= lo \/ lo+sz <= p) ==>
       mem_bytes_at p n u.vs_memory = mem_bytes_at p n s0.vs_memory)` by
      (irule aggregate_body_child_store_frames >> simp[arithmeticTheory.ADD_COMM] >>
       conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
       conj_tac >- (qexists_tac `inst.inst_id` >> simp[]) >>
       goal_assum (drule_at Any) >> simp[] >>
       rpt strip_tac >>
       qpat_x_assum `!aid off' sz a len. _`
         (drule_at (Pat `FLOOKUP _ _ = _`)) >>
       disch_then irule >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
    conj_tac
    >- (rpt strip_tac >>
        `mem_bytes_at p n t''.vs_memory = mem_bytes_at p n u.vs_memory` by
          (qpat_x_assum `!p n. _ ==> mem_bytes_at p n t''.vs_memory = _` irule >>
           fs[type_memory_size_def] >> decide_tac) >>
        `mem_bytes_at p n u.vs_memory = mem_bytes_at p n s0.vs_memory` by
          (qpat_x_assum `!p n. _ ==> mem_bytes_at p n u.vs_memory = _` irule >>
           fs[type_memory_size_def] >> decide_tac) >> simp[]) >>
    `!name lo sz. local_region ce mid.scopes u name lo sz ==>
       local_region ce es.scopes s0 name lo sz` by
      (rpt strip_tac >>
       `local_region ce mid.scopes q name lo sz` by
         (irule local_region_frame >>
          conj_tac
          >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
          qexistsl_tac [`sn`, `mid.scopes`, `u`] >> simp[]) >>
       irule aggregate_body_tuple_local_region_backward >>
       goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
       simp[]) >>
    conj_tac
    >- (rpt strip_tac >>
        `FLOOKUP u.vs_allocas aid = SOME (p,n)` by
          (fs[vv_post_def] >> metis_tac[]) >>
        `aid < st.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
        `mem_bytes_at p n t''.vs_memory = mem_bytes_at p n u.vs_memory` by
          (qpat_x_assum `!aid p n. _ ==> mem_bytes_at p n t''.vs_memory = _` irule >>
           conj_tac >- metis_tac[] >>
           simp[] >> qexists_tac `aid` >> simp[]) >>
        `mem_bytes_at p n u.vs_memory = mem_bytes_at p n s0.vs_memory` by
          (qpat_x_assum `!aid p n. _ ==> mem_bytes_at p n u.vs_memory = _` irule >>
           conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
           conj_tac >- (qexists_tac `aid` >> simp[]) >> decide_tac) >> simp[]) >>
    `locals_kept ce (mid with gas_obs := []) (mid' with gas_obs := []) q t''` by
      (irule locals_kept_trans >>
       qexistsl_tac [`mid with gas_obs := []`, `sn`, `u`] >> simp[]) >>
    irule locals_kept_trans >>
    qexistsl_tac [`mid with gas_obs := []`, `sa`, `q`] >>
    fs[vv_post_def]) >>
  metis_tac[]
QED

Resume aggregate_make_tuple_body_sim[result]:
  qsuff_tac `!xs off a out z.
    compile_make_tuple compile_expr ce xs (Var x) off a = (out,z) ==>
    out = Var x`
  >- metis_tac[] >>
  POP_ASSUM_LIST (K all_tac) >> Induct
  >- simp[compile_make_tuple_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >>
  drule aggregate_tuple_body_cons_compile >> strip_tac >> metis_tac[]
QED

Finalise aggregate_make_tuple_body_sim

Theorem aggregate_body_tuple_fields_memory:
  !names tvs vs ptr mem.
    LENGTH names = LENGTH tvs /\ tuple_in_memory vs tvs ptr mem ==>
    fields_in_memory (ZIP (names,vs)) (ZIP (names,tvs)) ptr mem
Proof
  Induct >> Cases_on `tvs` >> Cases_on `vs` >>
  simp[val_in_memory_def, ZIP_def] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem aggregate_struct_fields_body_sim:
  !fields ce cx env ty off sa out sb es tvs func inst x b asz s0 ctx.
  EVERY (\(name,e).
    ALOOKUP (get_struct_fields ce.ce_struct_fields
      (case ty of StructT nsid => nsid_to_string nsid | _ => "")) name =
      SOME (expr_type e,type_memory_bytes ce (expr_type e))) fields /\
  compile_struct_lit compile_expr ce ty fields (Var x) off sa = (out,sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type (MAP SND fields)) = SOME tvs /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e (MAP SND fields) /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  exprs_case F ctx func ce cx (MAP SND fields) /\
  (!e. MEM e (MAP SND fields) /\ int_calls_expr e <> [] /\
    lowered_value_type ce e <> expr_type e ==>
    acyclic_struct_metadata ce.ce_struct_fields) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + type_memory_size_list tvs <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size_list tvs)) /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx (MAP SND fields)) (es,s0)
    (\res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' r /\
      fields_in_memory (ZIP (MAP FST fields,vs))
        (ZIP (MAP FST fields,tvs)) (b+off) r.vs_memory /\
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
      locals_kept ce es es' s0 r)
    (\res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >>
  `compile_make_tuple compile_expr ce (MAP SND fields) (Var x) off sa = (out,sb)` by
    metis_tac[compile_struct_lit_as_tuple] >>
  drule_all aggregate_make_tuple_body_sim >> strip_tac >> simp[] >>
  irule counted_outcome_conseq >> goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> simp[] >>
  conj_tac >- (irule aggregate_body_tuple_fields_memory >> simp[] >>
    drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  conj_tac >> first_assum ACCEPT_TAC
QED
