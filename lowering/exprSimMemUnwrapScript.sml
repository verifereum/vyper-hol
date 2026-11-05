(* The forced memory judgment from the value one: the memory twin of
   exprSimUnwrap's expr_sim_of_vv_sim, through unwrap_value's code. *)
Theory exprSimMemUnwrap
Ancestors
  exprSimMemDefs exprSimUnwrap exprSimDefs loweringPosts gasOutcome
  exprLowering compileEnv vyperInterpreter vyperState
  exprSimUnwrapProps exprSimProps exprSimMemorySource bodyFieldMemoryProps
  gasSummary gasSummaryCompose gasExemptCert fragGasMode fragGasPath
  fragGasPathMem fragGasSeqMem fragExecMem instMemFrontier allocaHistoryFragment
  emitHelperProps emitHelper exprLoweringProps loweringSlice context
  fragExec exprOperandVar vyperEvalExprPreservesScopesDom
  venomExecSemantics venomInst venomState list rich_list finite_map

(* A word's rounded footprint is its one word. *)
Theorem word_val_store_size[local]:
  is_word_type t /\ evaluate_type tenv t = SOME tv ==> val_store_size tv v = 32
Proof
  strip_tac >> drule_all word_tv_memory_size >> strip_tac >>
  Cases_on `t` >> gvs[is_word_type_def]
  >- (rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_word_type_def] >>
      TRY (rename1 `BytesT bd` >> Cases_on `bd` >> gvs[is_word_type_def]) >>
      gvs[vyperValueTheory.evaluate_type_def] >>
      Cases_on `v` >> simp[val_store_size_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> simp[val_store_size_def]
QED

Theorem unwrap_storage_word_path_mem:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    is_word_type t /\ local_ptrs_reserved cenv sm /\
    sa.cs_next_var <= sm.cs_next_var /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path_mem ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  cheat
QED

Theorem unwrap_runtime_word_path_mem:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\
    sa.cs_next_var <= sm.cs_next_var /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path_mem ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  cheat
QED

Theorem unwrap_ctor_word_path_mem:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\
    sa.cs_next_var <= sm.cs_next_var /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path_mem ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  cheat
QED

(* The copies into a fresh buffer: storage/transient and both kinds of
   code. *)
Theorem unwrap_copy_path_mem:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
     p.ptr_location = LocCode) /\ ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
           type_memory_bytes cenv t = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path_mem ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        expr_store_bound cx t v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  cheat
QED

(* unwrap_value_path's memory-checked form: every value_vv's code, one
   path, keeping the allocation history and bounding the result. *)
Theorem unwrap_value_path_mem:
  !ctx func cenv cx e es sa sm sb s0 es' v vv op s.
    unwrap_value cenv vv sm = (op, sb) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!t op'. vv = StackValue t op' ==> is_word_type (expr_type e)) /\
    (is_word_type (expr_type e) ==>
     ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s /\
    vv_store_bound cx (expr_type e) es' (Value v) vv s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path_mem ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        expr_store_bound cx (expr_type e) v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  Cases_on `vv`
  >- (gvs[unwrap_value_def, comp_return_def] >> qexists_tac `s` >>
      simp[cj 1 gas_path_mem_rules, expr_store_bound_word] >>
      metis_tac[expr_post_of_vv_post_stack]) >>
  rename1 `LocatedValue t p` >>
  RULE_ASSUM_TAC (REWRITE_RULE [contextTheory.vv_operand_def]) >>
  `t = expr_type e` by gvs[vv_post_def, vv_holds_def] >>
  Cases_on `p.ptr_location = LocCalldata`
  >- gvs[vv_post_calldata] >>
  Cases_on `p.ptr_location = LocMemory`
  >- (`read_result cx (Value v) es' = (INL v, es')` by
        simp[read_result_def, return_def] >>
      `is_word_type t ==> ?w. eval_operand p.ptr_operand s = SOME w /\
                              w2n w + 32 <= s.vs_alloca_next` by
        (strip_tac >> gvs[] >>
         `?w. eval_operand p.ptr_operand s = SOME w` by
           gvs[vv_post_def, vv_holds_def] >>
         qexists_tac `w` >> simp[] >>
         qpat_x_assum `vv_store_bound _ _ _ _ _ _`
           (mp_tac o REWRITE_RULE [vv_store_bound_def]) >>
         disch_then (qspecl_then [`expr_type e`, `p`, `v`, `tvt`, `w`] mp_tac) >>
         simp[] >> metis_tac[word_val_store_size]) >>
      drule_at (Pat `unwrap_value _ _ _ = _`) body_unwrap_memory_counted_read >>
      disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[] >> strip_tac >> qexists_tac `u` >> gvs[]) >>
  Cases_on `is_word_type t`
  >- (Cases_on `p.ptr_location = LocCode`
      >- (Cases_on `cenv.ce_is_ctor`
          >- (drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_ctor_word_path_mem >>
              disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
              simp[] >> strip_tac >> qexists_tac `u` >>
              gvs[expr_store_bound_word]) >>
          drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_runtime_word_path_mem >>
          disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
          simp[] >> strip_tac >> qexists_tac `u` >>
          gvs[expr_store_bound_word]) >>
      `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by
        (Cases_on `p.ptr_location` >> gvs[]) >>
      drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_storage_word_path_mem >>
      disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[] >> strip_tac >> qexists_tac `u` >>
      gvs[expr_store_bound_word]) >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
   p.ptr_location = LocCode` by (Cases_on `p.ptr_location` >> gvs[]) >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_copy_path_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> strip_tac >> gvs[] >> goal_assum drule >> simp[]
QED

(* The counted read suffix, memory-checked. *)
Theorem unwrap_value_marked_read_mem:
  !ctx func cenv cx e es sa sm sb s0 ee tv vv op s.
    unwrap_value cenv vv sm = (op, sb) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!t op'. vv = StackValue t op' ==> is_word_type (expr_type e)) /\
    (is_word_type (expr_type e) ==>
     ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
    vv_store_bound cx (expr_type e) ee tv vv s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?v u. gas_marked_exec T (ctx,func) (read_result cx tv) (ee,s)
            [] (INL v) ee (OK u) /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
      expr_store_bound cx (expr_type e) v op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `read_result cx tv ee` >> rename1 `_ = (res, ee')` >>
  `ee' = ee` by metis_tac[read_result_state] >> gvs[] >>
  reverse (Cases_on `res`)
  >- metis_tac[vv_post_failed_read] >>
  rename1 `read_result cx tv ee = (INL v, ee)` >>
  `vv_store_bound cx (expr_type e) ee (Value v) vv s` by
    (qpat_x_assum `vv_store_bound _ _ _ _ _ _` mp_tac >>
     rw[vv_store_bound_def] >> gvs[read_result_def, return_def] >>
     first_x_assum irule >> metis_tac[]) >>
  drule vv_post_read_result >> strip_tac >> gvs[] >> pop_assum kall_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_path_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`v`, `u`] >> simp[] >>
  simp[gas_marked_exec_def, gas_marked_path_def] >>
  metis_tac[read_result_gas_obs, APPEND]
QED

Theorem expr_sim_mem_of_vv_sim_mem:
  !ctx func cenv cx ty e es.
    expr_vv_sim_mem ctx func cenv cx ty e es /\
    (!sa t op sb. compile_expr cenv ty e sa = (StackValue t op, sb) ==>
                  is_word_type (expr_type e)) /\
    (is_word_type (expr_type e) ==>
     ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
    expr_sim_mem ctx func cenv cx ty e es
Proof
  rw[expr_sim_mem_def] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (drule (cj 1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  `!t op'. vv = StackValue t op' ==> is_word_type (expr_type e)` by
    (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_mem_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `s0`] mp_tac) >>
  simp[] >>
  rewrite_tac[gas_outcome_def] >> strip_tac >>
  qexists_tac `marks`
  >- (disj1_tac >> gvs[gas_summary_at_def]
      >- (rename1 `vv_post _ _ _ _ _ _ _ _ _ _ tv vv u` >>
          `~u.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          `MAP FDOM es.scopes = MAP FDOM (es_end with gas_obs := []).scopes` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
             strip_tac >> first_x_assum (qspec_then `[]` assume_tac) >>
             drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >>
             simp[]) >>
          drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_marked_read_mem >>
          disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
          impl_tac >- simp[] >> strip_tac >>
          rename1 `gas_marked_exec T _ (read_result _ _) _ [] _ _ (OK u2)` >>
          qexistsl_tac [`INL v`, `es_end with gas_obs := []`, `OK u2`] >>
          simp[] >>
          `marks = marks ++ []` by simp[] >>
          pop_assum SUBST1_TAC >> irule gas_marked_exec_bind_normal >>
          goal_assum drule >> simp[]) >>
      Cases_on `res`
      >- (Cases_on `r` >> gvs[expr_exit_def]) >>
      rename1 `expr_exit (INR exc) r` >>
      `expr_res_ok (INR exc : value + exception)` by
        (Cases_on `exc` >> Cases_on `r` >>
         gvs[expr_exit_def, expr_res_ok_def, AllCaseEqs()] >>
         Cases_on `e'` >> gvs[expr_exit_def, expr_res_ok_def]) >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >>
      simp[GSYM expr_exit_exception_transport] >>
      irule gas_marked_exec_bind_exception >> goal_assum drule) >>
  disj2_tac >> metis_tac[force_exempt_cert]
QED
