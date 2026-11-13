(* The arguments of an internal call, staged one at a time as Vyper
   0.5.0b1 lowers them: each argument's producer runs, then the argument
   is staged at once, a word on the stack, any other value copied into a
   fresh buffer of the callee's parameter type. *)
Theory bodyIntCallStageEndpoint
Ancestors
  bodyIntCallStageList bodyIntCallStageOwned bodyIntCallStageTransport
  bodyIntCallHeldArgs exprSimWordArgs exprLoweringProps fragGasFocus
  context exprLowering compileEnv bodyIntCallJointContract
  bodyIntCallFamCallIntAllocatedStage
  bodyIntCallStageEndpointWord bodyIntCallStageEndpointMemory
  bodyIntCallFamStmtLogArgsFrame bodyIntCallFamAggStructFields
  exprSimSubscriptMap
  stmtSimForLoop bodyIntCallStageCompile stmtReasonVvMemory
  bodyIntCallFamStmtLogMarked
  stmtSimAugAssignPlaceMemory valueEncodingProps exprSimProps

(* ML abbreviations only, as in bodyIntCallFamCallIntStageInterface:
   staged argument i, at type ty with flag flag, value v and operand op, in
   state s, for the staging code from start to current. *)
val completed = ``\cx start current ty flag v op s.
  ?tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w /\
    (!x. op = Var x ==> not_fresh_at current x) /\
    (if flag then is_word_type ty /\ w = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n w) s.vs_memory /\
       ?aid len. FLOOKUP s.vs_allocas aid = SOME (w2n w,len) /\
         start.cs_next_id <= aid /\ aid < current.cs_next_id /\
         type_memory_size tv <= len /\
         w2n w + len <= s.vs_alloca_next /\
         w2n w + len < dimword (:256))``;

val completed_prefix = ``\cx start current tys flags values ops s.
  LENGTH flags = LENGTH tys /\ LENGTH values = LENGTH tys /\
  LENGTH ops = LENGTH tys /\
  !i. i < LENGTH tys ==>
    ^completed cx start current (EL i tys) (EL i flags)
      (EL i values) (EL i ops) s``;

Theorem intcall_stage_completed_start_mono[local]:
  ^completed cx sm sb ty flag v op u /\ sa.cs_next_id <= sm.cs_next_id ==>
  ^completed cx sa sb ty flag v op u
Proof
  BETA_TAC >> strip_tac >> qexistsl_tac [`tv`,`w`] >> simp[] >>
  Cases_on `flag` >> gvs[] >> qexistsl_tac [`aid`,`len`] >> simp[]
QED

Theorem intcall_stage_completed_word_transport[local]:
  ^completed fp.jc_cx sa sm ty T v op s /\
  sm.cs_next_var <= sn.cs_next_var /\
  eval_operand op u = eval_operand op s ==>
  ^completed fp.jc_cx sa sn ty T v op u
Proof
  BETA_TAC >> strip_tac >> qexistsl_tac [`tv`,`w`] >> simp[] >>
  metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]
QED

Theorem intcall_stage_completed_memory_transport[local]:
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  eval_operand op s = SOME w /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  val_in_memory tv v (w2n w) s.vs_memory /\ val_wf tv v /\
  FLOOKUP s.vs_allocas aid = SOME (w2n w,len) /\
  sa.cs_next_id <= aid /\ aid < sm.cs_next_id /\
  type_memory_size tv <= len /\
  w2n w + len <= s.vs_alloca_next /\
  w2n w + len < dimword (:256) /\
  (!name b k. local_region ce es.scopes s name b k ==>
    regions_disjoint (w2n w) len b k) /\
  intcall_expr_cont fp ce env es sm s ee sn u /\
  sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var /\
  eval_operand op u = eval_operand op s ==>
  ^completed fp.jc_cx sa sn ty F v op u
Proof
  BETA_TAC >> strip_tac >>
  `mem_bytes_at (w2n w) len u.vs_memory =
   mem_bytes_at (w2n w) len s.vs_memory` by
    (fs[bodyIntCallJointContractTheory.intcall_expr_cont_def] >>
     qpat_x_assum `!aid off sz. _`
       (qspecl_then [`aid`,`w2n w`,`len`] mp_tac) >> simp[] >>
     impl_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!name b k. local_region _ _ _ _ _ _ ==> _` drule >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def,
              arithmeticTheory.ADD_COMM]) >> simp[]) >>
  `val_in_memory tv v (w2n w) u.vs_memory` by
    (irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
     conj_tac >- simp[] >>
     qexistsl_tac [`len`,`s.vs_memory`] >> simp[]) >>
  qexistsl_tac [`tv`,`w`] >> simp[] >>
  conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `FLOOKUP u.vs_allocas aid = SOME (w2n w,len)` by
    (fs[bodyIntCallJointContractTheory.intcall_expr_cont_def] >>
     qpat_x_assum `!aid b. _` irule >> simp[]) >>
  qexistsl_tac [`aid`,`len`] >>
  fs[bodyIntCallJointContractTheory.intcall_expr_cont_def] >> simp[] >> decide_tac
QED

Theorem intcall_stage_head_tail_disjoint[local]:
  alloca_inv u /\
  FLOOKUP u.vs_allocas head_id = SOME (w2n hw,cap) /\
  head_id < sm.cs_next_id /\ type_memory_size htv <= cap /\
  ^completed cx sm sb ty F v op u /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand op u = SOME w ==>
  regions_disjoint (w2n hw) (type_memory_size htv)
    (w2n w) (type_memory_size tv)
Proof
  BETA_TAC >> strip_tac >> gvs[] >>
  `head_id <> aid` by decide_tac >>
  fs[venomMemDefsTheory.alloca_inv_def,
     venomMemDefsTheory.allocas_non_overlapping_def] >>
  qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
    (qspecl_then [`head_id`,`aid`,`w2n hw`,`cap`,`w2n w`,`len`] mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem stage_head_outcome[local]:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_expr_producer fp e /\
  supportedExprs$supported_expr fp.jc_tops e /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  expr_body_pre ce fp.jc_cx env e es /\
  (flag ==> is_word_type ty) /\
  type_widens_to (get_tenv fp.jc_cx) (expr_type e) ty /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME dtv /\
  type_memory_bytes ce ty = type_memory_size dtv /\
  MAX 32 (type_memory_size dtv) + 64 < dimword (:256) /\
  compile_stage_intcall_args compile_expr ce (e::args) (flag::flags)
    (ty::tys) sa = (ops,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  intcall_expr_res fp ce env es sa t /\ ~t.vs_halted /\
  t.vs_current_bb = sa.cs_current_bb /\
  t.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?sm hop rest.
    ops = hop::rest /\
    compile_stage_intcall_args compile_expr ce args flags tys sm = (rest,sb) /\
    ci_mono sa sm /\ ci_mono sm sb /\ fn_has_code sm sb fp.jc_func /\
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (vyperState$bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) (es,t)
      (\res ee u. ?v w. res = INL v /\
        eval_operand hop u = SOME w /\
        (!x. hop = Var x ==> not_fresh_at sm x) /\ val_wf dtv v /\
        (if flag then is_word_type ty /\ w = typed_val_to_w256 dtv v
         else val_in_memory dtv v (w2n w) u.vs_memory /\
           ?aid len. FLOOKUP u.vs_allocas aid = SOME (w2n w,len) /\
             sa.cs_next_id <= aid /\ aid < sm.cs_next_id /\
             type_memory_size dtv <= len /\
             w2n w + len <= u.vs_alloca_next /\
             w2n w + len < dimword (:256) /\
             (!name a k. local_region ce ee.scopes u name a k ==>
               regions_disjoint (w2n w) len a k)) /\
        intcall_expr_cont fp ce env es sa t ee sm u /\
        MAP FDOM es.scopes = MAP FDOM ee.scopes)
      (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `!ce' ty' e' st. ci_mono st (SND (compile_expr ce' ty' e' st))` by
    metis_tac[compile_expr_ci_mono] >>
  Cases_on `flag` >> gvs[]
  >- (drule intcall_stage_word_parts >> strip_tac >> gvs[] >>
      drule_all intcall_stage_word_code >> strip_tac >>
      `ci_mono sa sm` by metis_tac[ci_mono_trans] >>
      `fn_has_code sa sm fp.jc_func` by
        (fs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
      qexists_tac `sm` >> simp[] >>
      drule_all intcall_stage_word_arg_outcome >> disch_tac >>
      irule gas_outcome_exec_conseq >> goal_assum (drule_at Any) >> simp[] >>
      rpt gen_tac >> strip_tac >> gvs[] >>
      qexistsl_tac [`v`, `typed_val_to_w256 dtv v`] >> simp[]) >>
  drule intcall_stage_memory_parts >> strip_tac >> gvs[] >>
  drule_all intcall_stage_memory_code >> strip_tac >>
  `ci_mono sa s4` by metis_tac[ci_mono_trans] >>
  qexists_tac `s4` >> simp[] >>
  drule_all intcall_stage_memory_arg_outcome >> disch_tac >>
  irule gas_outcome_exec_conseq >> goal_assum (drule_at Any) >> simp[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qexistsl_tac [`v`, `w`] >> simp[] >>
  qexistsl_tac [`s1.cs_next_id`, `MAX 32 (type_memory_size dtv)`] >> simp[]
QED

(* RESTATED (train 17): 0.5.0b1 per-argument staging.  Replaces the batch
   endpoints over held arguments (intcall_stage_args_endpoint and its
   distinct/return variants): ops are the INVOKE's argument operands, vs the
   source values.  Restated again (argon's ruling): no freshness premise on
   t's allocations, since a loop re-enters the same ALLOCAs; instead the
   distinct memory arguments' buffers are pairwise disjoint. *)
Theorem intcall_stage_args_outcome:
  !args flags tys ce env sa ops sb es fp t.
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  (!e. MEM e args ==> intcall_expr_producer fp e /\
     supportedExprs$supported_expr fp.jc_tops e /\
     calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e)) /\
  (!e ee. MEM e args /\ expr_sim_inv ce fp.jc_cx env ee ==>
     expr_body_pre ce fp.jc_cx env e ee) /\
  LENGTH args <= LENGTH flags /\ LENGTH tys = LENGTH args /\
  (!i. i < LENGTH args ==>
     (EL i flags ==> is_word_type (EL i tys)) /\
     type_widens_to (get_tenv fp.jc_cx) (expr_type (EL i args)) (EL i tys) /\
     ?dtv. evaluate_type (get_tenv fp.jc_cx) (EL i tys) = SOME dtv /\
       type_memory_bytes ce (EL i tys) = type_memory_size dtv /\
       MAX 32 (type_memory_size dtv) + 64 < dimword (:256)) /\
  compile_stage_intcall_args compile_expr ce args flags tys sa = (ops,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  intcall_expr_res fp ce env es sa t /\ ~t.vs_halted /\
  t.vs_current_bb = sa.cs_current_bb /\
  t.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_exprs fp.jc_cx args) (es,t)
    (\res ee u. ?vs. res = INL vs /\
       ^completed_prefix fp.jc_cx sa sb tys (TAKE (LENGTH args) flags) vs ops u /\
       (!i j tv_i tv_j w_i w_j.
          i < LENGTH args /\ j < LENGTH args /\ i <> j /\
          ~EL i flags /\ ~EL j flags /\
          evaluate_type (get_tenv fp.jc_cx) (EL i tys) = SOME tv_i /\
          evaluate_type (get_tenv fp.jc_cx) (EL j tys) = SOME tv_j /\
          eval_operand (EL i ops) u = SOME w_i /\
          eval_operand (EL j ops) u = SOME w_j ==>
          regions_disjoint (w2n w_i) (type_memory_size tv_i)
            (w2n w_j) (type_memory_size tv_j)) /\
       intcall_expr_cont fp ce env es sa t ee sb u /\
       MAP FDOM es.scopes = MAP FDOM ee.scopes)
    (\res ee r. expr_exit res r)
Proof
  Induct_on `args`
  >- (rpt gen_tac >> strip_tac >>
      gvs[exprLoweringTheory.compile_stage_intcall_args_def,
          compileEnvTheory.comp_return_def] >>
      rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
      qexists_tac `[]` >> disj1_tac >>
      rewrite_tac[gasSummaryTheory.gas_summary_at_def] >>
      qexistsl_tac [`INL []`, `es`, `OK t`] >>
      simp[gasSummaryTheory.gas_marked_exec_def,
           Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.return_def,
           fragGasModeTheory.gas_marked_path_def,
           fragGasPathTheory.gas_path_rules] >>
      simp[intcall_expr_cont_def, loweringPostsTheory.locals_kept_def,
           loweringPostsTheory.popped_kept_def]) >>
  suspend "cons"
QED

Resume intcall_stage_args_outcome[cons]:
  rpt gen_tac >> strip_tac >>
  rename1 `compile_stage_intcall_args compile_expr ce (e::args) flags tys sa` >>
  namedCases_on `flags` ["", "flag tailflags"] >> gvs[] >>
  namedCases_on `tys` ["", "ty tailtys"] >> gvs[] >>
  `expr_body_pre ce fp.jc_cx env e es` by
    (fs[intcall_expr_res_def] >> metis_tac[]) >>
  `(flag ==> is_word_type ty) /\
   type_widens_to (get_tenv fp.jc_cx) (expr_type e) ty /\
   ?dtv. evaluate_type (get_tenv fp.jc_cx) ty = SOME dtv /\
     type_memory_bytes ce ty = type_memory_size dtv /\
     MAX 32 (type_memory_size dtv) + 64 < dimword (:256)` by
    (qpat_x_assum `!i. i < SUC (LENGTH args) ==> _`
       (qspec_then `0` mp_tac) >> simp[]) >>
  drule_all stage_head_outcome >> strip_tac >> gvs[] >>
  rewrite_tac[eval_exprs_cons_action] >>
  irule gas_outcome_bind_value >> goal_assum (drule_at Any) >>
  reverse conj_tac
  >- (rpt strip_tac >> Cases_on `res` >>
      fs[exprSimDefsTheory.expr_exit_INL, stmtSimPropsTheory.expr_exit_INR_type]) >>
  suspend "tail"
QED

Resume intcall_stage_args_outcome[tail]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  rename1 `intcall_expr_cont fp ce env es sa t (mid with gas_obs := []) sm u` >>
  `intcall_expr_res fp ce env (mid with gas_obs := []) sm u /\
   ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
   u.vs_inst_idx = LENGTH sm.cs_current_insts` by
    fs[intcall_expr_cont_def] >>
  qpat_assum `!flags tys ce env sa ops sb es fp t. _`
    (qspecl_then [`tailflags`, `tailtys`, `ce`, `env`, `sm`, `rest`,
       `sb`, `mid with gas_obs := []`, `fp`, `u`] mp_tac) >>
  (impl_tac
   >- (simp[] >> rpt conj_tac
       >~ [`!i. i < _ ==> _`] >-
         (gen_tac >> strip_tac >>
          qpat_x_assum `!i. i < SUC (LENGTH args) ==> _`
            (qspec_then `SUC i` mp_tac) >> simp[]) >>
       metis_tac[listTheory.MEM])) >>
  disch_tac >>
  irule gas_outcome_marked_return_map >> goal_assum (drule_at Any) >>
  reverse conj_tac
  >- (rpt gen_tac >> simp[exprSimDefsTheory.expr_exit_success_map]) >>
  suspend "posts"
QED

Resume intcall_stage_args_outcome[posts]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 `gas_marked_exec _ _ (eval_exprs fp.jc_cx args)
    (mid with gas_obs := [],u) marks (INL vs) fin (OK q)` >>
  `eval_operand hop q = SOME w` by
    (irule (Q.INST [`memory` |-> `F`, `ctx` |-> `fp.jc_ctx`,
       `func` |-> `fp.jc_func`, `s` |-> `u`, `cs` |-> `sm`,
       `n` |-> `LENGTH marks`]
       (SPEC_ALL stmtSimAugAssignPlaceMemoryTheory.aug_place_saved_operand)) >>
     fs[gasSummaryTheory.gas_marked_exec_def, intcall_expr_cont_def]) >>
  `intcall_expr_cont fp ce env es sa t (fin with gas_obs := []) sb q` by
    (irule bodyIntCallFamStmtLogArgsFrameTheory.intcall_expr_cont_trans >>
     qexistsl_tac [`mid with gas_obs := []`, `sm`, `u`] >>
     fs[ci_mono_def]) >>
  `MAP FDOM es.scopes = MAP FDOM (fin with gas_obs := []).scopes` by
    fs[] >>
  suspend "certificates"
QED

Resume intcall_stage_args_outcome[certificates]:
  `~flag ==> !i tv' w'.
    i < LENGTH args /\ ~EL i tailflags /\
    evaluate_type (get_tenv fp.jc_cx) (EL i tailtys) = SOME tv' /\
    eval_operand (EL i rest) q = SOME w' ==>
    regions_disjoint (w2n w) (type_memory_size dtv)
      (w2n w') (type_memory_size tv')` by
    (strip_tac >> gvs[] >> rpt gen_tac >> strip_tac >>
     rename1 `FLOOKUP u.vs_allocas aid = SOME (w2n w,len)` >>
     `FLOOKUP q.vs_allocas aid = SOME (w2n w,len)` by
       (fs[intcall_expr_cont_def] >>
        qpat_x_assum `!aid b. FLOOKUP u.vs_allocas aid = SOME b ==> _` irule >>
        simp[]) >>
     `alloca_inv q` by
       fs[intcall_expr_cont_def, intcall_expr_res_def,
          exprLoweringPropsTheory.stmt_state_rel_def] >>
     irule (BETA_RULE (Q.INST [`head_id` |-> `aid`, `cap` |-> `len`,
       `sm` |-> `sm`, `sb` |-> `sb`, `cx` |-> `fp.jc_cx`,
       `ty` |-> `EL i tailtys`, `v` |-> `EL i vs`, `op` |-> `EL i rest`]
       (SPEC_ALL intcall_stage_head_tail_disjoint))) >> simp[] >>
     qpat_x_assum `!i. i < _ ==> ?tv w.
       evaluate_type _ (EL i tailtys) = SOME tv /\ _`
       (qspec_then `i` mp_tac) >> fs[listTheory.EL_TAKE]) >>
  `^completed fp.jc_cx sa sb ty flag v hop q` by
    (Cases_on `flag` >> gvs[]
     >- (irule (BETA_RULE (Q.INST [`sm` |-> `sm`, `s` |-> `u`]
           (SPEC_ALL intcall_stage_completed_word_transport))) >>
         simp[ci_mono_def] >> qexistsl_tac [`dtv`, `w`] >> simp[]) >>
     rename1 `FLOOKUP u.vs_allocas aid = SOME (w2n w,len)` >>
     irule (BETA_RULE (Q.INST [`sm` |-> `sm`, `s` |-> `u`,
       `tv` |-> `dtv`, `w` |-> `w`, `aid` |-> `aid`, `len` |-> `len`,
       `es` |-> `mid with gas_obs := []`, `ee` |-> `fin with gas_obs := []`,
       `ce` |-> `ce`, `env` |-> `env`]
       (SPEC_ALL intcall_stage_completed_memory_transport))) >> fs[ci_mono_def]) >>
  `^completed_prefix fp.jc_cx sa sb tailtys
    (TAKE (LENGTH args) tailflags) vs rest q` by
    (BETA_TAC >> fs[] >> rpt strip_tac >>
     irule (BETA_RULE (Q.INST [`sm` |-> `sm`]
       (SPEC_ALL intcall_stage_completed_start_mono))) >> fs[ci_mono_def]) >>
  `^completed_prefix fp.jc_cx sa sb (ty::tailtys)
    (TAKE (SUC (LENGTH args)) (flag::tailflags)) (v::vs) (hop::rest) q` by
    (BETA_TAC >> fs[] >> Cases >> simp[]) >>
  qexists_tac `v::vs` >> simp[] >>
  rpt gen_tac >> strip_tac >> Cases_on `i` >> Cases_on `j` >> gvs[]
  >- metis_tac[]
  >- metis_tac[intCallCalleeTheory.regions_disjoint_sym] >>
  metis_tac[]
QED
Finalise intcall_stage_args_outcome
