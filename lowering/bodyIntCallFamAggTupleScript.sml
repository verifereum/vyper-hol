(* Seam 2 joint induction, a family leaf of the agg step: tuple literals. *)
Theory bodyIntCallFamAggTuple
Ancestors
  bodyIntCallJointContract bodyIntCallFamAggTupleLoop
  exprSimHyps exprSimProps exprSimHypsDefs valueEncoding words list
  bodyIntCallJointAggCore actualAllocExec bodyIntCallRestoreResults
  loweringPosts context compileEnv exprRecursionRegression

(* Evaluated child layouts are small enough for the counted store interface. *)
Theorem intcall_children_layout:
  !args tvs.
    EVERY (\e. expr_body_pre ce cx env e es) args /\
    OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs ==>
    LIST_REL (\e tv.
      evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
      type_memory_bytes ce (expr_type e) = type_memory_size tv /\
      type_memory_size tv + 64 < dimword (:256)) args tvs
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> conj_tac
  >- (irule expr_sim_inv_memory_size >>
      goal_assum (drule_at Any) >>
      fs[expr_body_pre_def] >> metis_tac[]) >>
  rename1 `expr_body_pre ce cx env child es` >>
  Cases_on `is_word_type (expr_type child)`
  >- (drule_all word_tv_memory_size >> simp[dimword_def]) >>
  drule_all expr_body_pre_copy_ok >> simp[dimword_def]
QED

(* The allocated root is authorized and clear of both endpoint local sets. *)
Theorem intcall_tuple_alloc_root:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  compile_alloc_buffer sz sa = (buf,sm) /\
  fn_has_code sa sm fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  sz < dimword (:256) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t w inst. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
    intcall_expr_cont fp ce env es sa s es sm t /\
    eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\ fp.jc_lo <= w2n w /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_id < sm.cs_next_id /\
    MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
    (!name b len. local_region ce es.scopes t name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region ce es.scopes s name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p)
Proof
  strip_tac >> drule_all intcall_alloc_landing >> strip_tac >>
  drule_all actual_alloc_buffer_site >> strip_tac >>
  qexistsl_tac [`u`, `w`,
    `mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)]`] >>
  simp[venomInstTheory.mk_inst_def] >> conj_tac
  >- (fs[intcall_expr_cont_def, intcall_joint_res_def,
         intCallFrameTheory.allocas_above_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `local_region ce es.scopes u name b len` by
    (irule local_region_frame_fwd >> goal_assum (drule_at Any) >>
     qexists_tac `sa` >> fs[intcall_expr_cont_def, intcall_joint_res_def]) >>
  metis_tac[]
QED

Theorem intcall_tuple_entry:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  (!e st. MEM e args /\ expr_sim_inv ce fp.jc_cx env st ==>
    expr_body_pre ce fp.jc_cx env e st) /\
  EVERY (intcall_expr_producer fp) args /\
  EVERY (supportedExprs$supported_expr fp.jc_tops) args /\
  (!e. MEM e args ==>
    calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e)) /\
  LIST_REL (\e tv. evaluate_type (get_tenv fp.jc_cx) (expr_type e) = SOME tv /\
    type_memory_bytes ce (expr_type e) = type_memory_size tv /\
    type_memory_size tv + 64 < dimword (:256)) args tvs /\
  compile_alloc_buffer (type_memory_size_list tvs) sa = (buf,sm) /\
  compile_make_tuple compile_expr ce args buf.buf_operand 0 sm = (out,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  type_memory_size_list tvs < dimword (:256) /\
  intcall_joint_res fp ce env es sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = buf.buf_operand /\
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_exprs fp.jc_cx args) (es,s)
    (\res ee t. ?vs w inst.
      res = INL vs /\ tuple_in_memory vs tvs (w2n w) t.vs_memory /\
      intcall_expr_cont fp ce env es sa s ee sb t /\
      eval_operand buf.buf_operand t = SOME w /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,type_memory_size_list tvs) /\
      sa.cs_next_id <= inst.inst_id /\ inst.inst_id < sb.cs_next_id /\
      w2n w + type_memory_size_list tvs < dimword (:256) /\ fp.jc_lo <= w2n w /\
      (!name b len. local_region ce ee.scopes t name b len ==>
        regions_disjoint (w2n w) (type_memory_size_list tvs) b len) /\
      (!x. buf.buf_operand = Var x ==> not_fresh_at sb x))
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `ci_mono sa sm` by
    (qspec_then `sa` mp_tac
      (Q.SPEC `type_memory_size_list tvs` exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >> simp[]) >>
  `ci_mono sm sb` by
    (qspecl_then [`compile_expr`, `ce`, `args`, `buf.buf_operand`, `0`, `sm`]
       mp_tac exprLoweringPropsTheory.ci_mono_compile_make_tuple_cfn >>
     simp[exprLoweringPropsTheory.compile_expr_ci_mono]) >>
  `fn_has_code sa sm fp.jc_func /\ fn_has_code sm sb fp.jc_func` by
    metis_tac[exprLoweringPropsTheory.ci_mono_def, fragExecTheory.fn_has_code_split] >>
  drule_all intcall_tuple_alloc_root >> strip_tac >>
  drule_at (Pat `compile_make_tuple _ _ _ _ _ _ = _`) intcall_tuple_tail >>
  disch_then (drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `LIST_REL _ _ _`)) >>
  disch_then (qspec_then `w` mp_tac) >>
  (impl_tac >- (fs[exprLoweringPropsTheory.ci_mono_def] >> metis_tac[])) >>
  strip_tac >> simp[] >>
  irule stmtReasonVvMemoryTheory.gas_outcome_zero_prefix_any >>
  goal_assum (drule_at Any) >>
  irule exprSimMemDefsTheory.gas_outcome_post_mono >>
  goal_assum (drule_at Any) >> simp_tac bool_ss [] >> rpt strip_tac >>
  qexistsl_tac [`vs`, `w`, `inst`] >>
  fs[exprLoweringPropsTheory.ci_mono_def] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

(* Source well-formedness is attached only to successful Value executions. *)
Theorem intcall_value_outcome_wf:
  expr_body_pre ce cx env e es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  gas_outcome memory tops (ctx,func) (eval_expr cx e) (es,s) Q R /\
  (!rr ee t. Q rr ee t ==> ?v. rr = INL (Value v)) ==>
  gas_outcome memory tops (ctx,func) (eval_expr cx e) (es,s)
    (\rr ee t. Q rr ee t /\ ?v. rr = INL (Value v) /\ val_wf tv v) R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac >>
  qexists_tac `marks`
  >- (disj1_tac >> fs[gasSummaryTheory.gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      disj1_tac >>
      first_x_assum drule >> strip_tac >> gvs[] >>
      irule intcall_materialised_child_wf >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      qexistsl_tac [`ctx`, `es_end`, `func`, `marks`, `memory`, `OK t`, `s`] >>
      fs[gasSummaryTheory.gas_marked_exec_def] >>
      simp[gasSummaryTheory.gas_marked_exec_def, vyperStateTheory.bind_def,
           vyperStateTheory.read_result_def, vyperStateTheory.return_def]) >>
  disj2_tac >> metis_tac[]
QED

Theorem intcall_tuple_root_post:
  evaluate_type (get_tenv cx) ann = SOME (TupleTV tvs) /\
  ~is_word_type ann /\
  tuple_in_memory vs tvs (w2n w) t.vs_memory /\
  val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
  eval_operand op t = SOME w /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size_list tvs) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!name b len. local_region ce ee.scopes t name b len ==>
    regions_disjoint (w2n w) (type_memory_size_list tvs) b len) ==>
  vv_holds ce cx ann (Value (ArrayV (TupleV vs)))
    (LocatedValue ann (mk_ptr op LocMemory)) ee t /\
  vv_at ce cx ann sa sb ee (Value (ArrayV (TupleV vs)))
    (LocatedValue ann (mk_ptr op LocMemory)) t
Proof
  strip_tac >> conj_tac
  >- (simp[vv_holds_def, mk_ptr_def, vyperStateTheory.read_result_def,
           vyperStateTheory.return_def] >>
      simp[valueEncodingTheory.val_in_memory_def]) >>
  irule bodyIntCallRestoreResultsTheory.allocated_value_vv_at >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[mk_ptr_def] >> reverse conj_tac
  >- (drule val_footprint_le >> simp[valueEncodingTheory.type_memory_size_def]) >>
  fs[regions_disjoint_def]
QED

Theorem intcall_tuple_outcome_map:
  compatible_bound n (LENGTH args) /\
  gas_outcome memory tops (ctx,func) (eval_exprs cx args) (es,s) Q R /\
  (!rr ee t. Q rr ee t ==>
    Q' (case rr of INL vs => INL (Value (ArrayV (TupleV vs)))
          | INR ex => INR ex) ee t) /\
  (!rr ee r. R rr ee r ==>
    R' (case rr of INL vs => INL (Value (ArrayV (TupleV vs)))
          | INR ex => INR ex) ee r) ==>
  gas_outcome memory tops (ctx,func)
    (eval_expr cx (Builtin ann (MakeArray NONE n) args)) (es,s) Q' R'
Proof
  strip_tac >>
  `eval_expr cx (Builtin ann (MakeArray NONE n) args) =
   vyperState$bind (eval_exprs cx args)
     (\vs. vyperState$return (Value (ArrayV (TupleV vs))))` by
    (simp[FUN_EQ_THM] >> qx_gen_tac `st` >>
     Cases_on `eval_exprs cx args st` >> rename1 `eval_exprs cx args st = (rr,ee)` >>
     drule_all exprSimAggregateSourceTheory.aggregate_eval_make_tuple >>
     simp[vyperStateTheory.bind_def, vyperStateTheory.return_def] >>
     Cases_on `rr` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule (BETA_RULE (ISPEC ``\vs. Value (ArrayV (TupleV vs))``
    (Q.GEN `f` intcall_gas_outcome_map))) >>
  qexistsl_tac [`Q`, `R`] >> simp[]
QED

Theorem intcall_tuple_landing:
  expr_body_pre ce fp.jc_cx env (Builtin ann (MakeArray NONE n) args) es /\
  evaluate_type (get_tenv fp.jc_cx) ann = SOME (TupleTV tvs) /\
  ~is_word_type ann /\ compatible_bound n (LENGTH args) /\
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_exprs fp.jc_cx args) (es,s)
    (\res ee t. ?vs w inst.
      res = INL vs /\ tuple_in_memory vs tvs (w2n w) t.vs_memory /\
      intcall_expr_cont fp ce env es sa s ee sb t /\
      eval_operand op t = SOME w /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,type_memory_size_list tvs) /\
      sa.cs_next_id <= inst.inst_id /\ inst.inst_id < sb.cs_next_id /\
      w2n w + type_memory_size_list tvs < dimword (:256) /\ fp.jc_lo <= w2n w /\
      (!name b len. local_region ce ee.scopes t name b len ==>
        regions_disjoint (w2n w) (type_memory_size_list tvs) b len) /\
      (!x. op = Var x ==> not_fresh_at sb x))
    (\res ee r. expr_exit res r) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_expr fp.jc_cx (Builtin ann (MakeArray NONE n) args)) (es,s)
    (\res ee t. ?v.
      res = INL v /\
      vv_holds ce fp.jc_cx ann v (LocatedValue ann (mk_ptr op LocMemory)) ee t /\
      vv_at ce fp.jc_cx ann sa sb ee v (LocatedValue ann (mk_ptr op LocMemory)) t /\
      (!x. op = Var x ==> not_fresh_at sb x) /\
      (!tv. evaluate_type (get_tenv fp.jc_cx) ann = SOME tv ==>
        ?w a k. eval_operand op t = SOME w /\ a <= w2n w /\
          w2n w + type_memory_size tv <= a + k /\ a + k < dimword (:256) /\
          (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)) /\
      intcall_expr_cont fp ce env es sa s ee sb t)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome F _ _ _ _ Q0 _` >>
  `gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_expr fp.jc_cx (Builtin ann (MakeArray NONE n) args)) (es,s)
    (\res ee t. ?vs. res = INL (Value (ArrayV (TupleV vs))) /\ Q0 (INL vs) ee t)
    (\res ee r. expr_exit res r)` by
    (irule intcall_tuple_outcome_map >> simp[] >>
     qexistsl_tac [`Q0`, `\res ee r. expr_exit res r`] >> simp[] >> conj_tac
     >- simp[exprSimDefsTheory.expr_exit_success_map] >>
     simp[Abbr `Q0`] >> rpt strip_tac >> simp[] >> metis_tac[]) >>
  drule_at (Pat `gas_outcome _ _ _ (eval_expr _ _) _ _ _`)
    intcall_value_outcome_wf >>
  disch_then (qspecl_then [`TupleTV tvs`, `env`, `ce`] mp_tac) >>
  simp[vyperASTTheory.expr_type_def] >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  irule exprSimMemDefsTheory.gas_outcome_post_mono >>
  goal_assum (drule_at Any) >> simp_tac bool_ss [] >>
  rpt strip_tac >> gvs[Abbr `Q0`] >>
  drule_all intcall_tuple_root_post >> strip_tac >>
  simp[] >> rpt strip_tac >> gvs[] >>
  qexistsl_tac [`w2n w`, `type_memory_size_list tvs`] >>
  simp[valueEncodingTheory.type_memory_size_def]
QED

Theorem intcall_tuple_literal_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a n args. e = Builtin a (MakeArray NONE n) args) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  strip_tac >> gvs[] >>
  reverse conj_tac
  >- (irule bodyIntCallJointAggCoreTheory.intcall_map_producer_other >> simp[]) >>
  rewrite_tac[intcall_expr_producer_def] >> rpt gen_tac >> strip_tac >>
  drule exprSimAggregateLayoutTheory.make_tuple_evaluated_layout >> strip_tac >>
  drule exprSimAggregateLayoutTheory.compile_tuple_literal_inv >> strip_tac >>
  `!e st. MEM e args /\ expr_sim_inv ce fp.jc_cx env st ==>
      expr_body_pre ce fp.jc_cx env e st` by
    (rpt strip_tac >> irule exprSimSourceTheory.expr_body_pre_builtin_arg >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `EVERY (intcall_expr_producer fp) args` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     drule exprRecursionRegressionTheory.expr_size_member >> strip_tac >>
     first_x_assum (qspec_then `e` mp_tac) >> simp[]) >>
  `EVERY (supportedExprs$supported_expr fp.jc_tops) args` by
    (fs[supportedExprsTheory.supported_expr_def,
        supportedExprsTheory.supported_pure_expr_def,
        supportedExprsTheory.supported_effect_expr_def,
        supportedExprsTheory.supported_pure_exprs_every, EVERY_MEM] >>
     metis_tac[]) >>
  `!child. MEM child args ==>
    calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr child)` by
    (fs[vyperTypeCallGraphTheory.int_calls_expr_def,
        vyperTypeCallStackSoundnessTheory.calls_follow_call_graph_def] >>
     rpt strip_tac >> irule exprSimSourceTheory.int_calls_exprs_every_mem >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `EVERY (\e. expr_body_pre ce fp.jc_cx env e es) args` by
    (simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum irule >>
     fs[intcall_joint_res_def]) >>
  drule_all intcall_children_layout >> strip_tac >>
  `~is_word_type a` by simp[is_word_type_def] >>
  `type_memory_size_list tvs < dimword (:256)` by
    (gvs[] >> drule expr_body_pre_copy_ok >>
     disch_then (qspec_then `TupleTV tvs` mp_tac) >>
     simp[vyperASTTheory.expr_type_def, is_word_type_def,
          valueEncodingTheory.type_memory_size_def, dimword_def]) >>
  qpat_x_assum `SUM _ = type_memory_size_list tvs` (fn th => fs[th]) >>
  drule_all intcall_tuple_entry >> strip_tac >>
  `compatible_bound n (LENGTH args)` by
    (fs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
        vyperTypeSystemTheory.well_typed_builtin_app_def]) >>
  gvs[] >>
  drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)
    (SRULE [arithmeticTheory.ADD_COMM] intcall_tuple_landing) >>
  disch_then (qspecl_then [`n`, `TupleT (MAP expr_type args)`] mp_tac) >>
  simp[vyperASTTheory.expr_type_def, mk_ptr_def,
       contextTheory.vv_operand_def, is_bytestring_type_def]
QED
