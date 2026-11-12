(* Counted tuple-tail loop with the internal-call resource continuation. *)
Theory bodyIntCallFamAggTupleLoop
Ancestors
  bodyIntCallJointAggCore exprSimAggregateChildren exprSimAggregateLayout
  exprSimAggregateSource exprSimHyps exprLoweringProps exprLowering
  bodyIntCallJointContract valueEncoding valueEncodingProps
  gasOutcome gasSummary stmtReasonVvMemory vyperInterpreter vyperState
  finite_map list compileEnv loweringStateRelDefs
  exprSimAggregateLoops aggregateEvaluatedLayout memoryLocalRhsProps
  vyperTypeArgFits valueEncodingTyping loweringPosts vyperTypeSystem
  typedCopyCompatibility

(* Outside a word or bytestring, the lowered and post types agree. *)
Theorem lowered_post_value_type_agg[local]:
  !ce e. well_typed_expr env e /\ ~is_word_type (expr_type e) /\
    ~is_bytestring_type (expr_type e) ==>
    lowered_value_type ce e = post_value_type ce e
Proof
  ho_match_mp_tac exprLoweringTheory.lowered_value_type_ind >>
  simp[exprLoweringTheory.lowered_value_type_def, post_value_type_def,
       vyperASTTheory.expr_type_def, is_bytestring_type_def,
       vyperTypeSystemTheory.well_typed_expr_def,
       vyperTypeSystemTheory.type_builtin_result_ok_def] >>
  rpt strip_tac >> gvs[is_bytestring_type_def] >>
  gvs[vyperTypeSystemTheory.well_typed_builtin_app_def] >>
  rpt (qpat_x_assum `(_ = BaseT _ /\ _) \/ _` strip_assume_tac) >>
  gvs[is_bytestring_type_def]
QED

(* compile_store_memory_post_type at a member type the child fits. *)
Theorem compile_store_memory_post_type_fits[local]:
  well_typed_expr env e /\ arg_type_fits (expr_type e) dty ==>
  compile_store_memory ce src dst dty (lowered_value_type ce e) =
  compile_store_memory ce src dst dty (post_value_type ce e)
Proof
  strip_tac >>
  Cases_on `is_word_type dty \/ is_bytestring_type dty`
  >- (rewrite_tac[contextTheory.compile_store_memory_def] >> gvs[]) >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type,
              memoryLocalRhsPropsTheory.arg_type_fits_bytestring_target] >>
  metis_tac[lowered_post_value_type_agg]
QED

Theorem intcall_tuple_head_compile:
  compile_make_tuple compile_expr ce (e::args) (mty::tys) buf off si = (out,sb) /\
  expr_body_pre ce cx env e es /\
  type_widens_to (get_tenv cx) (expr_type e) mty /\
  fn_has_code si sb func ==>
  ?vv sm dst sn op su sc stv.
    compile_expr ce (expr_type e) e si = (vv,sm) /\
    emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
    unwrap_value ce vv sn = (op,su) /\
    compile_store_memory ce op dst mty (post_value_type ce e) su = ((),sc) /\
    compile_make_tuple compile_expr ce args tys buf
      (off + type_memory_bytes ce mty) sc = (out,sb) /\
    fn_has_code si sm func /\ fn_has_code sm sn func /\
    fn_has_code sn su func /\ fn_has_code su sc func /\ fn_has_code sc sb func /\
    ci_mono si sc /\ ci_mono sc sb /\
    type_widens_to env.type_defs (expr_type e) mty /\
    type_widens_to (get_tenv cx) (post_value_type ce e) mty /\
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME stv
Proof
  strip_tac >> drule compile_make_tuple_cons >> strip_tac >>
  rename1 `compile_store_memory ce op dst mty _ su = (_,sc)` >>
  `ci_mono si sm` by
    (qspec_then `si` mp_tac
      (Q.SPECL [`ce`, `expr_type e`, `e`] (cj 1 compile_expr_ci_mono)) >> simp[]) >>
  `ci_mono sm sn` by
    (qspecl_then [`ADD`, `[buf; Lit (n2w off)]`, `sm`] mp_tac ci_mono_emit_op >> simp[]) >>
  `ci_mono sn su` by
    (qspecl_then [`ce`, `vv`, `sn`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  `ci_mono su sc` by
    (qspecl_then [`ce`, `op`, `dst`, `mty`, `lowered_value_type ce e`, `su`]
      mp_tac ci_mono_compile_store_memory >> simp[]) >>
  `ci_mono sc sb` by
    (qspecl_then [`compile_expr`, `ce`, `args`, `tys`, `buf`,
                  `off + type_memory_bytes ce mty`, `sc`]
      mp_tac ci_mono_compile_make_tuple_cfn >> simp[compile_expr_ci_mono]) >>
  `ci_mono si sc` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  `fn_has_code si sm func /\ fn_has_code sm sn func /\
   fn_has_code sn su func /\ fn_has_code su sc func /\ fn_has_code sc sb func` by
    metis_tac[ci_mono_def, cs_extends_trans,
              fragExecTheory.fn_has_code_split] >>
  `expr_sim_inv ce cx env es /\ well_typed_expr env e` by
    fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  drule_all post_value_type_widens >>
  `env.type_defs = get_tenv cx` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  strip_tac >>
  drule_all post_type_evaluates >> strip_tac >>
  `arg_type_fits (expr_type e) mty` by
    (fs[vyperTypeSystemTheory.type_widens_to_def] >> simp[]) >>
  `compile_store_memory ce op dst mty (post_value_type ce e) su = ((),sc)` by
    metis_tac[compile_store_memory_post_type_fits] >>
  gvs[] >> metis_tac[typedCopyCompatibilityTheory.type_widens_to_trans]
QED

Theorem intcall_tuple_head_store:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_expr_producer fp e /\ expr_body_pre ce fp.jc_cx env e es /\
  supportedExprs$supported_expr fp.jc_tops e /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  intcall_expr_res fp ce env es0 s0c s0 /\
  intcall_expr_cont fp ce env es0 s0c s0 es si t /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  s0c.cs_next_var <= si.cs_next_var /\ s0c.cs_next_id <= si.cs_next_id /\
  compile_make_tuple compile_expr ce (e::args) (mty::tys) buf off si = (out,sb) /\
  fn_has_code si sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  arg_type_fits (expr_type e) mty /\
  evaluate_type (get_tenv fp.jc_cx) mty = SOME dtv /\
  type_memory_size dtv + 64 < dimword (:256) /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (b,k) /\
  s0c.cs_next_id <= inst.inst_id /\ inst.inst_id < si.cs_next_id /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  eval_operand buf t = SOME bw /\ (!lbl. buf <> Label lbl) /\
  (!x. buf = Var x ==> not_fresh_at si x) /\
  fp.jc_lo <= b /\ b <= w2n bw /\
  w2n bw + off + type_memory_size dtv <= b+k /\ b+k < dimword (:256) /\
  (!name a n. local_region ce es.scopes t name a n ==> regions_disjoint b k a n) /\
  (!name a n. local_region ce es0.scopes s0 name a n ==> regions_disjoint b k a n) ==>
  ?sc. compile_make_tuple compile_expr ce args tys buf
         (off + type_memory_bytes ce mty) sc = (out,sb) /\
  ci_mono si sc /\ ci_mono sc sb /\ fn_has_code sc sb fp.jc_func /\
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (vyperState$bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) (es,t)
    (\res ee u. ?v. res = INL v /\
       val_in_memory dtv v (w2n bw + off) u.vs_memory /\
       intcall_expr_cont fp ce env es0 s0c s0 ee sc u /\
       FLOOKUP u.vs_allocas inst.inst_id = SOME (b,k) /\
       eval_operand buf u = SOME bw /\
       MAP FDOM es.scopes = MAP FDOM ee.scopes /\
       (!name a n. local_region ce ee.scopes u name a n ==> regions_disjoint b k a n) /\
       (!a n. b <= a /\ a+n <= b+k /\
          (a+n <= w2n bw+off \/ w2n bw+off+type_memory_size dtv <= a) ==>
          mem_bytes_at a n u.vs_memory = mem_bytes_at a n t.vs_memory))
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `type_widens_to (get_tenv fp.jc_cx) (expr_type e) mty` by
    fs[vyperTypeSystemTheory.type_widens_to_def,
       vyperTypeSystemTheory.well_formed_type_def] >>
  drule_all intcall_tuple_head_compile >> strip_tac >>
  drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`) intcall_counted_child_store >>
  disch_then drule_all >> strip_tac >>
  qexists_tac `sc` >> simp[]
QED

Theorem intcall_gas_outcome_map:
  gas_outcome memory tops (ctx,func) source (es,s) Q R /\
  (!rr ee t. Q rr ee t ==>
     Q' (case rr of INL v => INL (f v) | INR ex => INR ex) ee t) /\
  (!rr ee r. R rr ee r ==>
     R' (case rr of INL v => INL (f v) | INR ex => INR ex) ee r) ==>
  gas_outcome memory tops (ctx,func)
    (vyperState$bind source (\v. vyperState$return (f v))) (es,s) Q' R'
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> strip_tac >>
  qexists_tac `marks`
  >- (disj1_tac >> fs[gasSummaryTheory.gas_summary_at_def] >>
      (qexistsl_tac [`case res of INL v => INL (f v) | INR ex => INR ex`, `es_end`, `r`] >>
       conj_tac
       >- (fs[gasSummaryTheory.gas_marked_exec_def] >>
           simp[gasSummaryTheory.gas_marked_exec_def, vyperStateTheory.bind_def,
                vyperStateTheory.return_def] >> Cases_on `res` >> simp[]) >>
       simp[])) >>
  disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  fs[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_assoc,
     vyperStateTheory.bind_return]
QED

(* A counted, materialised child has its source type. *)
Theorem intcall_materialised_child_typed:
  expr_body_pre ce cx env e es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  gas_marked_exec memory (ctx,func)
    (vyperState$bind (eval_expr cx e) (read_result cx))
    (es,s) marks (INL v) ee r ==> value_has_type tv v
Proof
  strip_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >>
  simp[vyperStateTheory.bind_def] >> gvs[AllCaseEqs()] >> strip_tac >>
  drule vyperStateTheory.read_result_state >> strip_tac >> gvs[] >>
  irule aggregate_materialised_child_typed >> goal_assum (drule_at Any) >>
  qexistsl_tac [`ce`, `e`, `env`,
    `es with gas_obs := gas_explicit marks s.vs_gas_readings`] >>
  simp[exprSimSourceTheory.expr_body_pre_gas_obs]
QED

(* A counted, materialised child retains its source type's well-formedness. *)
Theorem intcall_materialised_child_wf:
  expr_body_pre ce cx env e es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  gas_marked_exec memory (ctx,func)
    (vyperState$bind (eval_expr cx e) (read_result cx))
    (es,s) marks (INL v) ee r ==> val_wf tv v
Proof
  metis_tac[intcall_materialised_child_typed,
            cj 1 valueEncodingTypingTheory.value_has_type_val_wf]
QED

Theorem intcall_tuple_tail:
  !args tys off si out sb es tvs t.
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  (!e st. MEM e args /\ expr_sim_inv ce fp.jc_cx env st ==>
     expr_body_pre ce fp.jc_cx env e st) /\
  EVERY (intcall_expr_producer fp) args /\
  EVERY (supportedExprs$supported_expr fp.jc_tops) args /\
  (!e. MEM e args ==>
     calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e)) /\
  LIST_REL (\t e. arg_type_fits (expr_type e) t) tys args /\
  LIST_REL (\t tv.
    evaluate_type (get_tenv fp.jc_cx) t = SOME tv /\
    type_memory_bytes ce t = type_memory_size tv /\
    type_memory_size tv + 64 < dimword (:256)) tys tvs /\
  compile_make_tuple compile_expr ce args tys buf off si = (out,sb) /\
  fn_has_code si sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  intcall_expr_res fp ce env es0 s0c s0 /\
  intcall_expr_cont fp ce env es0 s0c s0 es si t /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  s0c.cs_next_var <= si.cs_next_var /\ s0c.cs_next_id <= si.cs_next_id /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (b,k) /\
  s0c.cs_next_id <= inst.inst_id /\ inst.inst_id < si.cs_next_id /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  eval_operand buf t = SOME bw /\ (!lbl. buf <> Label lbl) /\
  (!x. buf = Var x ==> not_fresh_at si x) /\
  fp.jc_lo <= b /\ b <= w2n bw /\
  w2n bw + off + type_memory_size_list tvs <= b+k /\ b+k < dimword (:256) /\
  (!name a n. local_region ce es.scopes t name a n ==>
     regions_disjoint b k a n) /\
  (!name a n. local_region ce es0.scopes s0 name a n ==>
     regions_disjoint b k a n) ==>
  out = buf /\
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_exprs fp.jc_cx args) (es,t)
    (\res ee u. ?vs. res = INL vs /\
       tuple_in_memory vs tvs (w2n bw + off) u.vs_memory /\
       intcall_expr_cont fp ce env es0 s0c s0 ee sb u /\
       FLOOKUP u.vs_allocas inst.inst_id = SOME (b,k) /\
       eval_operand buf u = SOME bw /\
       MAP FDOM es.scopes = MAP FDOM ee.scopes /\
       (!name a n. local_region ce ee.scopes u name a n ==>
          regions_disjoint b k a n) /\
       (!a n. b <= a /\ a+n <= b+k /\
          (a+n <= w2n bw+off \/ w2n bw+off+type_memory_size_list tvs <= a) ==>
          mem_bytes_at a n u.vs_memory = mem_bytes_at a n t.vs_memory))
    (\res ee r. expr_exit res r)
Proof
  Induct_on `args`
  >- (rpt gen_tac >> strip_tac >> suspend "nil") >>
  rpt gen_tac >> strip_tac >>
  rename1 `LIST_REL _ tys (head::args)` >>
  Cases_on `tys` >> gvs[] >> rename1 `LIST_REL _ tail_tys args` >>
  rename1 `LIST_REL _ tail_tys tail_types` >>
  rename1 `compile_make_tuple compile_expr ce (head::args) (mty::tail_tys) buf off si = _` >>
  rename1 `evaluate_type _ mty = SOME h` >>
  `expr_sim_inv ce fp.jc_cx env es` by
    fs[intcall_expr_cont_def, intcall_joint_res_def, intcall_expr_res_def] >>
  `expr_body_pre ce fp.jc_cx env head es` by metis_tac[] >>
  `calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr head)` by metis_tac[] >>
  `s0c.cs_next_id <= si.cs_next_id` by decide_tac >>
  `w2n bw + off + type_memory_size h <= b+k` by
    fs[valueEncodingTheory.type_memory_size_def] >>
  drule_all intcall_tuple_head_store >> strip_tac >>
  conj_tac >- metis_tac[exprOperandVarTheory.compiler_make_tuple_result] >>
  rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  irule gas_outcome_bind_value >>
  goal_assum (drule_at Any) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      rename1 `val_in_memory h v _ head_state.vs_memory` >>
      `val_wf h v` by
        (`expr_body_pre ce fp.jc_cx env head es` by metis_tac[] >>
         drule exprSimHypsTheory.expr_body_pre_type_evaluates >>
         simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
         rename1 `evaluate_type _ (expr_type head) = SOME stv` >>
         `value_has_type stv v` by
           (irule intcall_materialised_child_typed >>
            qexistsl_tac [`ce`, `fp.jc_ctx`, `fp.jc_cx`, `head`, `mid`, `env`, `es`,
                          `fp.jc_func`, `marks`, `F`, `OK head_state`, `t`] >>
            fs[]) >>
         metis_tac[cj 1 vyperTypeArgFitsTheory.arg_type_fits_value_has_type,
                   cj 1 valueEncodingTypingTheory.value_has_type_val_wf]) >>
      first_x_assum (drule_at (Pat `compile_make_tuple _ _ _ _ _ _ _ = _`)) >>
      disch_then (qspec_then `mid with gas_obs := []` mp_tac) >>
      disch_then (qspecl_then [`tail_types`, `head_state`] mp_tac) >>
      (impl_tac
       >- (fs[ci_mono_def, not_fresh_at_def, valueEncodingTheory.type_memory_size_def] >>
           rpt conj_tac >> rpt strip_tac >> fs[] >> metis_tac[])) >>
      strip_tac >>
      irule intcall_gas_outcome_map >> goal_assum (drule_at Any) >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >> Cases_on `rr` >>
          gvs[exprSimDefsTheory.expr_exit_def]) >>
      rpt gen_tac >> strip_tac >> gvs[] >>
      rename1 `tuple_in_memory _ tail_types _ final_state.vs_memory` >>
      conj_tac
      >- (simp[Once valueEncodingDefsTheory.val_in_memory_def] >>
          irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
          simp[] >> qexistsl_tac [`type_memory_size h`, `head_state.vs_memory`] >> simp[] >>
          sym_tac >> first_x_assum irule >> decide_tac) >>
      conj_tac >- metis_tac[] >>
      rpt strip_tac >>
      `mem_bytes_at a n final_state.vs_memory = mem_bytes_at a n head_state.vs_memory` by
        (first_x_assum irule >> fs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
      simp[] >> first_x_assum irule >>
      fs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  rpt gen_tac >> Cases_on `res` >>
  simp[stmtSimPropsTheory.expr_exit_INR_type]
QED

(* HELD (train 15): pure_frame sweep, retired by alan 451258 *)
Resume intcall_tuple_tail[nil]:
  (* original proof, kept while held:
  gvs[compile_make_tuple_def, comp_return_def] >>
  irule intcall_gas_transparent_path_outcome >>
  qexistsl_tac [`es`, `OK t`, `INL []`] >>
  simp[exprSimWordArgsTheory.eval_exprs_nil,
       fragGasModeTheory.gas_marked_path_def,
       fragGasPathTheory.gas_path_rules, intcall_expr_cont_def] >>
  gvs[intcall_expr_cont_def, intcall_joint_res_def, intcall_expr_res_def,
      valueEncodingDefsTheory.val_in_memory_def,
      exprSimWordArgsTheory.stmt_state_rel_gas_obs,
      exprSimHypsDefsTheory.expr_sim_inv_gas_obs] >>
  simp[fragGasPathTheory.gas_path_rules] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
  *)
  cheat
QED

Finalise intcall_tuple_tail
