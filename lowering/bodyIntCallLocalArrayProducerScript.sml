(* Local-array production: compiler decomposition before counted composition. *)
Theory bodyIntCallLocalArrayProducer
Ancestors
  bodyIntCallArraySuffix bodyIntCallProducerRoots exprSimNameValue
  bodyIntCallIndexArithmetic
  exprLowering compileEnv context vyperAST venomState vyperInterpreter vyperState
  gasSummary gasSummaryCompose gasOutcome bodyIntCallProducerInterface
  bodyIntCallPathLayout loweringPosts exprSimProps exprLoweringProps
  vyperTypeSystem valueEncoding finite_map exprSimHypsDefs allocLimits
  supportedExprTraverse vyperTypeCallGraph vyperTypeCallStackSoundness
  exprSimSource exprSimDefs exprSimUnopProps fragExec
  vyperTypeEnv vyperTypeInvariants vyperTypeExprResult vyperValue
  vyperTypeExprSoundness arithmetic words valueEncodingProps freshWrites
  typedMemoryCopy vyperPlaceStatePreservation vyperTyping valueTypingMemoryProps
  exprSimWordArgs exprSimHash
Libs
  monadsyntax

Theorem compile_local_fixed_array_subscript:
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root_var) sz) ==>
  compile_expr cenv ty (Subscript ann (Name (ArrayT et (Fixed cnt)) id) idx) =
  do i <- lower_value compile_expr cenv ty idx;
     p <- compile_array_subscript (Var root_var) i F cnt
            (word_scale LocMemory) (elem_size_in_location cenv LocMemory et)
            (is_signed_type (expr_type idx))
            (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory);
     comp_return (LocatedValue ann (mk_ptr p LocMemory))
  od
Proof
  strip_tac >> drule compile_name_value_ptr >> strip_tac >>
  simp[FUN_EQ_THM, Once compile_expr_def, expr_type_def] >>
  simp[compile_subscript_def, lower_value_def, comp_bind_def, comp_return_def,
       exprCallBoundsTheory.expr_child_callback_def, expr_size_def,
       compile_name_value_ptr, place_type_def, expr_type_def, vv_operand_def,
       vv_location_def, mk_ptr_def]
QED

Theorem eval_local_subscript:
  lookup_scopes id es.scopes = SOME entry ==>
  eval_expr cx (Subscript ann (Name arrty id) idx) es =
    bind (bind (eval_expr cx idx) (read_result cx))
      (\v. select_result cx arrty (PlaceR (MemoryPlace id []))
             (ValueSubscript v)) es
Proof
  strip_tac >>
  simp[Once evaluate_def, bind_def, Once evaluate_def, get_scopes_def,
       type_check_def, assert_def, check_def, ignore_bind_def, return_def,
       expr_type_def] >>
  Cases_on `eval_expr cx idx es` >> rename1 `_ = (res,ee)` >>
  Cases_on `res` >> simp[bind_def] >> pairarg_tac >> simp[]
QED

Theorem local_subscript_marked_exec:
  lookup_scopes id es.scopes = SOME entry /\
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx idx) (read_result cx)) (es,s0)
    marks (INL v) mid (OK t) /\
  gas_marked_exec memory (ctx,func)
    (select_result cx arrty (PlaceR (MemoryPlace id [])) (ValueSubscript v))
    (mid with gas_obs := [],t) [] res fin r ==>
  gas_marked_exec memory (ctx,func)
    (eval_expr cx (Subscript ann (Name arrty id) idx))
    (es,s0) marks res fin r
Proof
  strip_tac >>
  `gas_marked_exec memory (ctx,func)
     (bind (bind (eval_expr cx idx) (read_result cx))
       (\v. select_result cx arrty (PlaceR (MemoryPlace id []))
              (ValueSubscript v))) (es,s0) marks res fin r` suffices_by
    simp[gas_marked_exec_def, eval_local_subscript] >>
  irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
         |> REWRITE_RULE [listTheory.APPEND_NIL]) >>
  goal_assum (drule_at Any) >> simp[]
QED

(* A root read cannot fall back to popped history.  Selection is against
   the current root value, after the general index has run. *)
Theorem select_local_root:
  lookup_scopes id es.scopes = SOME entry ==>
  select_result cx arrty (PlaceR (MemoryPlace id [])) sub es =
    case evaluate_subscripts entry.type entry.value [sub] of
    | INL v => (INL (PlaceR (MemoryPlace id [sub])),es)
    | INR err => (INR (Error err),es)
Proof
  strip_tac >>
  simp[select_result_def, extend_place_def, place_type_value_def,
       read_place_def, read_memory_path_def, get_scopes_def,
       subscripts_type_def, evaluate_subscripts_def, bind_def,
       lift_option_type_def, lift_sum_def, ignore_bind_def, return_def,
       extend_memory_place_def] >>
  Cases_on `evaluate_subscripts entry.type entry.value [sub]` >>
  simp[lift_sum_def, bind_def, return_def, raise_def]
QED

Theorem local_fixed_array_marked_success:
  lookup_scopes id es.scopes = SOME initial_entry /\
  gas_marked_exec F (ctx,func)
    (bind (eval_expr cx idx) (read_result cx)) (es,s0)
    marks (INL (IntV n)) mid (OK s1) /\
  lookup_scopes id mid.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value [ValueSubscript (IntV n)] = INL val /\
  compile_array_subscript base_op idx_op F cnt ws esz sgn loader sa = (p,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx (mid with gas_obs := []) s1 /\ ~s1.vs_halted /\
  s1.vs_current_bb = sa.cs_current_bb /\
  s1.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand base_op (drop_fresh sa s1) = SOME b /\
  eval_operand idx_op (drop_fresh sa s1) = SOME i /\
  idx_in_range sgn i (n2w cnt) ==>
  ?t. gas_marked_exec F (ctx,func)
        (eval_expr cx (Subscript ann (Name arrty id) idx)) (es,s0)
        marks (INL (PlaceR (MemoryPlace id [ValueSubscript (IntV n)]))) mid (OK t) /\
      stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t /\
      eval_operand p t = SOME (b + i * n2w esz) /\
      (!z v. not_fresh_at sa z /\ lookup_var z s1 = SOME v ==>
             lookup_var z t = SOME v) /\
      (!aid buf. FLOOKUP s1.vs_allocas aid = SOME buf ==>
                 FLOOKUP t.vs_allocas aid = SOME buf) /\
      t.vs_memory = s1.vs_memory /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all fixed_array_subscript_success_path >> strip_tac >>
  rename1 `gas_marked_path F ctx func s1 0 (OK t)` >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule local_subscript_marked_exec >> conj_tac
  >- metis_tac[] >>
  qexistsl_tac [`mid`,`s1`,`IntV n`] >>
  simp[gas_marked_exec_def] >> gen_tac >>
  `lookup_scopes id (mid with gas_obs := tail).scopes = SOME entry` by simp[] >>
  drule select_local_root >> simp[]
QED

Theorem local_fixed_array_marked_abort:
  lookup_scopes id es.scopes = SOME initial_entry /\
  gas_marked_exec F (ctx,func)
    (bind (eval_expr cx idx) (read_result cx)) (es,s0)
    marks (INL (IntV n)) mid (OK s1) /\
  lookup_scopes id mid.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value [ValueSubscript (IntV n)] =
    INR (RuntimeError msg) /\
  compile_array_subscript base_op idx_op F cnt ws esz sgn loader sa = (p,sb) /\
  fn_has_code sa sb func /\ ~s1.vs_halted /\
  s1.vs_current_bb = sa.cs_current_bb /\
  s1.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand base_op (drop_fresh sa s1) = SOME b /\
  eval_operand idx_op (drop_fresh sa s1) = SOME i /\
  ~idx_in_range sgn i (n2w cnt) ==>
  ?t. gas_marked_exec F (ctx,func)
        (eval_expr cx (Subscript ann (Name arrty id) idx)) (es,s0)
        marks (INR (Error (RuntimeError msg))) mid (Abort Revert_abort t)
Proof
  strip_tac >> drule_all fixed_array_subscript_abort_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_marked_path F ctx func s1 0 (Abort Revert_abort t)` >>
  qexists_tac `t` >> irule local_subscript_marked_exec >> conj_tac
  >- metis_tac[] >>
  qexistsl_tac [`mid`,`s1`,`IntV n`] >>
  simp[gas_marked_exec_def] >> gen_tac >>
  `lookup_scopes id (mid with gas_obs := tail).scopes = SOME entry` by simp[] >>
  drule select_local_root >> simp[]
QED

Theorem local_selection_provenance:
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root_var) sz) /\
  lookup_var root_var s = SOME root_word /\
  value_has_type entry.type entry.value /\
  mem_path_offset entry.type path = SOME (k,tvt) /\
  evaluate_subscripts entry.type entry.value path = INL selected /\
  val_wf tvt selected /\ evaluate_type (get_tenv cx) ann = SOME tvt /\
  eval_operand op s = SOME w /\ w2n w = w2n root_word + k /\
  stmt_state_rel ctx func cenv cx es s ==>
  intcall_vv_provenance cenv cx ann sa sb es
    (PlaceR (MemoryPlace id path)) (LocatedValue ann (mk_ptr op LocMemory)) s
Proof
  strip_tac >>
  `sub_layout entry.type entry.value k tvt selected` by
    (irule mem_path_selection_sub_layout >> simp[] >>
     qexists_tac `path` >> simp[]) >>
  `type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  drule val_footprint_le >> strip_tac >>
  simp[intcall_vv_provenance_def, mk_ptr_def] >> rpt strip_tac >>
  `v = selected` by
    (gvs[read_result_def, read_place_def, get_scopes_def, bind_def,
         lift_option_type_def, lift_sum_def, read_memory_path_def,
         return_def, raise_def]) >>
  gvs[] >> disj2_tac >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`id`,`sz`,`entry`,`root_var`,`root_word`,`k`] >>
  simp[local_region_def] >> fs[sub_layout_def]
QED

Theorem expr_body_pre_subscript_index:
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_sim_inv cenv cx env es' ==>
  expr_body_pre cenv cx env idx es'
Proof
  simp[expr_body_pre_def, well_typed_expr_def, byte_widths_expr_def,
       alloc_limits_expr_def, int_calls_expr_def, supported_expr_exists_def,
       expr_has_evm_run_thm] >>
  metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right]
QED

Theorem local_fixed_array_index_outcome:
  expr_body_pre cenv cx env (Subscript ann (Name (ArrayT et (Fixed cnt)) id) idx) es /\
  expr_sim_case F ctx func cenv cx idx /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root_var) sz) /\
  compile_expr cenv ty (Subscript ann (Name (ArrayT et (Fixed cnt)) id) idx) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?i sm p.
    lower_value compile_expr cenv ty idx sa = (i,sm) /\
    compile_array_subscript (Var root_var) i F cnt (word_scale LocMemory)
      (elem_size_in_location cenv LocMemory et) (is_signed_type (expr_type idx))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) sm = (p,sb) /\
    vv = LocatedValue ann (mk_ptr p LocMemory) /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    gas_outcome F (cx_tops cx) (ctx,func)
      (bind (eval_expr cx idx) (read_result cx)) (es,s0)
      (\res ee t. ?v. res = INL v /\
         expr_post ctx func cenv cx idx es sa sm s0 ee v i t /\
         t.vs_current_bb = sm.cs_current_bb /\
         t.vs_inst_idx = LENGTH sm.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule compile_local_fixed_array_subscript >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (Subscript _ _ _) _ = _` mp_tac >>
  asm_rewrite_tac[] >> simp[comp_bind_def, comp_return_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `lower_value compile_expr cenv ty idx sa = (i,sm)` >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `cs_extends sm cs''` by
    (drule_at Any straight_fresh_cs_extends >>
     simp[straight_fresh_fixed_array_subscript]) >>
  drule_all fn_has_code_split >> strip_tac >> simp[] >>
  `expr_body_pre cenv cx env idx es` by
    (drule expr_body_pre_subscript_index >>
     disch_then (qspec_then `es` mp_tac) >>
     impl_tac >- fs[expr_body_pre_def] >> simp[]) >>
  drule expr_body_pre_gas_admissible >> strip_tac >>
  fs[expr_sim_case_def] >>
  first_x_assum (qspecl_then [`env`,`ty`,`es`] mp_tac) >>
  simp[] >> simp[expr_sim_def] >>
  disch_then irule >> simp[]
QED

Theorem local_fixed_array_subscript_typing:
  well_typed_expr env (Subscript ann (Name (ArrayT et (Fixed cnt)) id) idx) ==>
  well_typed_expr env (Name (ArrayT et (Fixed cnt)) id) /\
  ann = et /\ is_int_type (expr_type idx)
Proof
  simp[well_typed_expr_def, expr_type_def,
       subscript_type_ok_def] >> metis_tac[]
QED

(* Recover semantic types from the actual source index execution. *)
Theorem local_fixed_array_current_types:
  expr_body_pre cenv cx env
    (Subscript ann (Name (ArrayT et (Fixed cnt)) id) idx) es /\
  (do result <- eval_expr cx idx; read_result cx result od) es = (INL v,ee) ==>
  expr_sim_inv cenv cx env ee /\ ann = et /\ is_int_type (expr_type idx) /\
  cnt < dimword (:256) /\
  ?entry etv itv.
    lookup_scopes id ee.scopes = SOME entry /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    entry.type = ArrayTV etv (Fixed cnt) /\
    value_has_type entry.type entry.value /\
    evaluate_type (get_tenv cx) (expr_type idx) = SOME itv /\
    value_has_type itv v
Proof
  strip_tac >>
  `well_typed_expr env (Name (ArrayT et (Fixed cnt)) id) /\
   ann = et /\ is_int_type (expr_type idx)` by
    (fs[expr_body_pre_def] >> drule local_fixed_array_subscript_typing >> simp[]) >>
  `expr_body_pre cenv cx env idx es` by
    (drule expr_body_pre_subscript_index >>
     disch_then (qspec_then `es` mp_tac) >>
     impl_tac >- fs[expr_body_pre_def] >> simp[]) >>
  drule_all expr_body_pre_eval >> strip_tac >> simp[] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?entry tv. lookup_scopes id ee.scopes = SOME entry /\
      evaluate_type env.type_defs (ArrayT et (Fixed cnt)) = SOME tv /\
      entry.type = tv /\ value_has_type tv entry.value` by
    (drule well_typed_Name_lookup >>
     disch_then (qspecl_then [`ee`,`cx`] mp_tac) >>
     fs[expr_sim_inv_def]) >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  conj_tac
  >- (qpat_x_assum `ArrayTV _ _ = entry.type` (SUBST_ALL_TAC o SYM) >>
      rename1 `0 < type_slot_size etv` >>
      `cnt <= cnt * type_slot_size etv` by simp[] >>
      qpat_x_assum `type_slot_size (ArrayTV _ _) < _` mp_tac >>
      rewrite_tac[type_slot_size_def] >> decide_tac) >>
  fs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def] >>
  metis_tac[]
QED

Theorem local_fixed_array_address:
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root_var) sz) /\
  entry.type = ArrayTV etv (Fixed cnt) /\
  stmt_state_rel ctx func cenv cx es s ==>
  ?b. lookup_var root_var s = SOME b /\
      val_wf entry.type entry.value /\
      val_in_memory entry.type entry.value (w2n b) s.vs_memory /\
      (!j. j < cnt ==> w2n b + j * type_memory_size etv < dimword (:256))
Proof
  strip_tac >>
  `?b. lookup_var root_var s = SOME b /\
       w2n b + sz <= s.vs_alloca_next /\
       type_memory_size entry.type <= sz /\
       val_wf entry.type entry.value /\
       val_in_memory entry.type entry.value (w2n b) s.vs_memory` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  qexists_tac `b` >> simp[] >> rpt strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `cnt * type_memory_size etv <= sz` by
    (qpat_x_assum `type_memory_size entry.type <= sz` mp_tac >>
     asm_rewrite_tac[type_memory_size_def]) >>
  `j * type_memory_size etv <= cnt * type_memory_size etv` by simp[] >>
  decide_tac
QED

Theorem local_fixed_array_cut_selection:
  expr_body_pre cenv cx env
    (Subscript ann (Name (ArrayT et (Fixed cnt)) id) idx) es /\
  (do result <- eval_expr cx idx; read_result cx result od) es = (INL v,ee) /\
  expr_post ctx func cenv cx idx es sa sm s0 ee v op s /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root_var) sz) ==>
  ?entry etv n b i.
    lookup_scopes id ee.scopes = SOME entry /\
    entry.type = ArrayTV etv (Fixed cnt) /\
    evaluate_type (get_tenv cx) ann = SOME etv /\
    value_has_type entry.type entry.value /\
    lookup_var root_var s = SOME b /\ v = IntV n /\
    eval_operand op s = SOME i /\ math_val (expr_type idx) i = n /\
    (idx_in_range (is_signed_type (expr_type idx)) i (n2w cnt) <=>
       0 <= n /\ n < &cnt) /\
    (if idx_in_range (is_signed_type (expr_type idx)) i (n2w cnt) then
       ?selected.
         evaluate_subscripts entry.type entry.value [ValueSubscript (IntV n)] = INL selected /\
         mem_path_offset entry.type [ValueSubscript (IntV n)] =
           SOME (Num n * type_memory_size etv,etv) /\
         w2n (b + i * n2w (type_memory_size etv)) =
           w2n b + Num n * type_memory_size etv
     else evaluate_subscripts entry.type entry.value [ValueSubscript (IntV n)] =
           INR (RuntimeError "evaluate_subscripts array_index"))
Proof
  strip_tac >> drule_all local_fixed_array_current_types >> strip_tac >>
  `post_value_type cenv idx = expr_type idx` by
    (irule post_value_type_word >>
     qpat_x_assum `is_int_type (expr_type idx)` mp_tac >>
     Cases_on `expr_type idx` >> simp[is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_word_type_def]) >>
  `stmt_state_rel ctx func cenv cx ee s /\
   expr_val_rel cx (expr_type idx) v op s` by gvs[expr_post_def] >>
  drule_all typed_index_operand_bounds >> strip_tac >> gvs[] >>
  drule_all local_fixed_array_address >> strip_tac >>
  qexists_tac `b` >> simp[] >>
  qabbrev_tac `n = math_val (expr_type idx) w` >>
  drule typed_fixed_array_selection >>
  disch_then (qspec_then `n` mp_tac) >>
  Cases_on `0 <= n /\ n < &cnt` >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  irule index_address_nonwrapping >> simp[] >>
  reverse conj_tac
  >- (qexists_tac `expr_type idx` >> simp[Abbr `n`]) >>
  first_x_assum irule >> intLib.ARITH_TAC
QED

Theorem local_fixed_array_cut_drop_fresh:
  expr_body_pre cenv cx env
    (Subscript ann (Name (ArrayT et (Fixed cnt)) id) idx) es /\
  lower_value compile_expr cenv ty idx sa = (op,sm) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root_var) sz) /\
  local_ptrs_reserved cenv sa ==>
  eval_operand op (drop_fresh sm s) = eval_operand op s /\
  eval_operand (Var root_var) (drop_fresh sm s) =
    eval_operand (Var root_var) s /\ local_ptrs_reserved cenv sm
Proof
  strip_tac >>
  `expr_body_pre cenv cx env idx es` by
    (drule expr_body_pre_subscript_index >>
     disch_then (qspec_then `es` mp_tac) >>
     impl_tac >- fs[expr_body_pre_def] >> simp[]) >>
  `is_int_type (expr_type idx)` by
    (fs[expr_body_pre_def] >> drule local_fixed_array_subscript_typing >> simp[]) >>
  `is_word_type (expr_type idx)` by
    (Cases_on `expr_type idx` >> gvs[is_int_type_def] >>
     rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
     gvs[is_int_type_def, is_word_type_def]) >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  simp[eval_operand_drop_fresh] >>
  irule eval_operand_drop_fresh >>
  fs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem local_fixed_array_cut_ready:
  expr_body_pre cenv cx env
    (Subscript ann (Name (ArrayT et (Fixed cnt)) id) idx) es /\
  (do result <- eval_expr cx idx; read_result cx result od) es = (INL v,ee) /\
  expr_post ctx func cenv cx idx es sa sm s0 ee v op s /\
  lower_value compile_expr cenv ty idx sa = (op,sm) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root_var) sz) /\
  local_ptrs_reserved cenv sa ==>
  ?entry etv n b i.
    lookup_scopes id ee.scopes = SOME entry /\
    entry.type = ArrayTV etv (Fixed cnt) /\
    evaluate_type (get_tenv cx) ann = SOME etv /\
    value_has_type entry.type entry.value /\
    v = IntV n /\ local_ptrs_reserved cenv sm /\
    eval_operand (Var root_var) (drop_fresh sm s) = SOME b /\
    eval_operand op (drop_fresh sm s) = SOME i /\
    elem_size_in_location cenv LocMemory et = type_memory_size etv /\
    (if idx_in_range (is_signed_type (expr_type idx)) i (n2w cnt) then
       ?selected.
         evaluate_subscripts entry.type entry.value [ValueSubscript (IntV n)] = INL selected /\
         mem_path_offset entry.type [ValueSubscript (IntV n)] =
           SOME (Num n * type_memory_size etv,etv) /\
         val_wf etv selected /\
         w2n (b + i * n2w (elem_size_in_location cenv LocMemory et)) =
           w2n b + Num n * type_memory_size etv
     else evaluate_subscripts entry.type entry.value [ValueSubscript (IntV n)] =
           INR (RuntimeError "evaluate_subscripts array_index"))
Proof
  strip_tac >> drule_all local_fixed_array_cut_selection >> strip_tac >>
  drule_all local_fixed_array_cut_drop_fresh >> strip_tac >>
  `expr_sim_inv cenv cx env ee` by
    (drule_all local_fixed_array_current_types >> simp[]) >>
  `ann = et` by
    (fs[expr_body_pre_def] >> drule local_fixed_array_subscript_typing >> simp[]) >>
  `elem_size_in_location cenv LocMemory et = type_memory_size etv` by
    (simp[elem_size_in_location_def, is_slot_addressed_def] >>
     irule typed_copy_memory_size >> fs[expr_sim_inv_def] >> metis_tac[]) >>
  qexistsl_tac [`entry`,`etv`,`n`,`b`,`i`] >>
  simp[eval_operand_def] >>
  Cases_on `idx_in_range (is_signed_type (expr_type idx)) i (n2w cnt)` >>
  gvs[] >>
  irule value_has_type_memory_wf >>
  irule evaluate_subscripts_type >> goal_assum (drule_at Any) >>
  simp[subscripts_type_def, subscript_type_def] >>
  fs[expr_sim_inv_def, state_well_typed_def] >>
  drule_all scope_well_typed_lookup_scopes >> simp[] >> strip_tac >>
  `Num (math_val (expr_type idx) i) < cnt` by
    (qpat_x_assum `0 <= math_val _ _` mp_tac >>
     qpat_x_assum `math_val _ _ < &cnt` mp_tac >>
     rpt (pop_assum kall_tac) >> intLib.ARITH_TAC) >> simp[]
QED

(* Any currently selected local path has both the semantic and lifetime posts. *)
Theorem local_selection_value_posts:
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root_var) sz) /\
  lookup_var root_var s = SOME b /\
  cenv.ce_var_type id = SOME t0 /\
  evaluate_type (get_tenv cx) t0 = SOME entry.type /\
  value_has_type entry.type entry.value /\
  mem_path_offset entry.type path = SOME (k,tvt) /\
  evaluate_subscripts entry.type entry.value path = INL selected /\
  val_wf tvt selected /\ value_has_type tvt selected /\
  evaluate_type (get_tenv cx) ann = SOME tvt /\
  eval_operand op s = SOME w /\ w2n w = w2n b + k /\
  stmt_state_rel ctx func cenv cx es s ==>
  vv_holds cenv cx ann (PlaceR (MemoryPlace id path))
    (LocatedValue ann (mk_ptr op LocMemory)) es s /\
  vv_at cenv cx ann sa sb es (PlaceR (MemoryPlace id path))
    (LocatedValue ann (mk_ptr op LocMemory)) s
Proof
  strip_tac >>
  `read_result cx (PlaceR (MemoryPlace id path)) es = (INL selected,es)` by
    simp[read_result_def, read_place_def, read_memory_path_def, get_scopes_def,
         bind_def, lift_option_type_def, lift_sum_def, return_def] >>
  `type_memory_size entry.type <= sz /\
   val_in_memory entry.type entry.value (w2n b) s.vs_memory` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  `sub_layout entry.type entry.value k tvt selected` by
    (irule mem_path_selection_sub_layout >> simp[] >>
     qexists_tac `path` >> simp[]) >>
  `val_in_memory tvt selected (w2n w) s.vs_memory` by
    (fs[sub_layout_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  conj_tac
  >- (simp[vv_holds_def, mk_ptr_def] >> strip_tac >>
      drule_all val_in_memory_word_type >> simp[arithmeticTheory.ADD_COMM]) >>
  simp[vv_at_def, mk_ptr_def] >> rpt strip_tac >> gvs[] >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`id`,`w2n b`,`sz`] >>
  simp[local_region_def] >>
  `val_footprint tvt selected <= type_memory_size tvt` by
    simp[val_footprint_le] >>
  conj_tac >- (fs[sub_layout_def] >> decide_tac) >>
  irule local_path_at_val_at >> simp[local_path_at_def] >>
  qexists_tac `path` >> simp[]
QED

Theorem local_selection_endpoint:
  expr_post ctx func cenv cx idx es sa sm s0 ee v i s /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!z w. not_fresh_at sm z /\ lookup_var z s = SOME w ==> lookup_var z t = SOME w) /\
  (!aid buf. FLOOKUP s.vs_allocas aid = SOME buf ==> FLOOKUP t.vs_allocas aid = SOME buf) /\
  t.vs_memory = s.vs_memory /\ stmt_state_rel ctx func cenv cx ee t /\
  lookup_scopes id ee.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root_var) sz) /\
  lookup_var root_var t = SOME b /\
  cenv.ce_var_type id = SOME t0 /\
  evaluate_type (get_tenv cx) t0 = SOME entry.type /\
  value_has_type entry.type entry.value /\
  mem_path_offset entry.type path = SOME (k,tvt) /\
  evaluate_subscripts entry.type entry.value path = INL selected /\
  val_wf tvt selected /\ value_has_type tvt selected /\
  evaluate_type (get_tenv cx) ann = SOME tvt /\
  eval_operand op t = SOME w /\ w2n w = w2n b + k ==>
  vv_post ctx func cenv cx (Subscript ann obj idx) es sa sb s0 ee
    (PlaceR (MemoryPlace id path)) (LocatedValue ann (mk_ptr op LocMemory)) t /\
  intcall_vv_provenance cenv cx ann sa sb ee
    (PlaceR (MemoryPlace id path)) (LocatedValue ann (mk_ptr op LocMemory)) t
Proof
  strip_tac >>
  drule_all local_selection_value_posts >> strip_tac >>
  reverse conj_tac >- (irule local_selection_provenance >> simp[] >>
    goal_assum (drule_at Any) >> simp[]) >>
  irule vv_post_frame_intro >> simp[expr_type_def] >>
  conj_tac >- simp[contextTheory.mk_ptr_def] >>
  drule expr_post_frame >> strip_tac >>
  irule wb_frame_readonly_tail >> goal_assum (drule_at Any) >>
  qexists_tac `sm` >> simp[]
QED

(* Apply the endpoint boundary to the actual successful fixed-array suffix. *)
Theorem local_fixed_array_endpoint:
  expr_body_pre cenv cx env
    (Subscript ann (Name (ArrayT et (Fixed cnt)) id) idx) es /\
  (do result <- eval_expr cx idx; read_result cx result od) es = (INL v,ee) /\
  expr_post ctx func cenv cx idx es sa sm s0 ee v i s /\
  lower_value compile_expr cenv ty idx sa = (i,sm) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root_var) sz) /\
  local_ptrs_reserved cenv sa /\
  lookup_scopes id ee.scopes = SOME entry /\
  evaluate_type (get_tenv cx) ann = SOME tvt /\
  value_has_type entry.type entry.value /\
  mem_path_offset entry.type path = SOME (k,tvt) /\
  evaluate_subscripts entry.type entry.value path = INL selected /\
  val_wf tvt selected /\
  eval_operand (Var root_var) (drop_fresh sm s) = SOME b /\
  eval_operand op t = SOME w /\ w2n w = w2n b + k /\
  (!z w. not_fresh_at sm z /\ lookup_var z s = SOME w ==> lookup_var z t = SOME w) /\
  (!aid buf. FLOOKUP s.vs_allocas aid = SOME buf ==> FLOOKUP t.vs_allocas aid = SOME buf) /\
  t.vs_memory = s.vs_memory /\ stmt_state_rel ctx func cenv cx ee t ==>
  vv_post ctx func cenv cx (Subscript ann (Name (ArrayT et (Fixed cnt)) id) idx)
    es sa sb s0 ee (PlaceR (MemoryPlace id path))
    (LocatedValue ann (mk_ptr op LocMemory)) t /\
  intcall_vv_provenance cenv cx ann sa sb ee
    (PlaceR (MemoryPlace id path)) (LocatedValue ann (mk_ptr op LocMemory)) t
Proof
  strip_tac >> drule_all local_fixed_array_current_types >> strip_tac >>
  `well_typed_expr env (Name (ArrayT et (Fixed cnt)) id)` by
    (fs[expr_body_pre_def] >> drule local_fixed_array_subscript_typing >> simp[]) >>
  `cenv.ce_var_type id = SOME (ArrayT et (Fixed cnt))` by
    (fs[well_typed_expr_def, expr_sim_inv_def] >> metis_tac[]) >>
  drule_all local_fixed_array_cut_drop_fresh >> strip_tac >>
  `lookup_var root_var s = SOME b` by fs[eval_operand_def] >>
  `not_fresh_at sm root_var` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `lookup_var root_var t = SOME b` by metis_tac[] >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `well_formed_type_value entry.type` by
    (fs[expr_sim_inv_def, state_well_typed_def] >>
     drule_all scope_well_typed_lookup_scopes >> strip_tac >> gvs[]) >>
  `value_has_type tvt selected` by
    (drule mem_path_offset_sound >> strip_tac >>
     irule evaluate_subscripts_type >> goal_assum (drule_at Any) >>
     qexists_tac `entry.value` >> simp[]) >>
  `evaluate_type (get_tenv cx) (ArrayT et (Fixed cnt)) = SOME entry.type` by
    (`env.type_defs = get_tenv cx` by
       fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
     drule well_typed_Name_lookup >>
     disch_then (qspecl_then [`ee`,`cx`] mp_tac) >>
     (impl_tac >- fs[expr_sim_inv_def]) >> strip_tac >> gvs[]) >>
  irule local_selection_endpoint >> goal_assum (drule_at Any) >> simp[] >>
  conj_tac
  >- (qexists_tac `selected` >> gvs[]) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any)
QED

Theorem local_subscript_marked_exception:
  lookup_scopes id es.scopes = SOME entry /\
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx idx) (read_result cx)) (es,s0)
    marks (INR exc) ee r ==>
  gas_marked_exec memory (ctx,func)
    (eval_expr cx (Subscript ann (Name arrty id) idx)) (es,s0)
    marks (INR exc) ee r
Proof
  strip_tac >>
  fs[gas_marked_exec_def] >>
  simp[eval_local_subscript, bind_def]
QED

Theorem local_subscript_exempt:
  lookup_scopes id es.scopes = SOME entry /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx idx) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,tfinal) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_expr cx (Subscript ann (Name arrty id) idx)) (return ()))
    (es,s0) marks (err,ee) (leaf,tfinal)
Proof
  strip_tac >>
  once_rewrite_tac[ignore_bind_def] >>
  once_rewrite_tac[evaluate_def] >>
  rewrite_tac[bind_assoc] >> BETA_TAC >>
  once_rewrite_tac[evaluate_def] >>
  rewrite_tac[bind_assoc] >> BETA_TAC >>
  irule gasExemptCertTheory.gas_exempt_cert_get_scopes >>
  simp[type_check_def, assert_def, check_def, ignore_bind_def, bind_return,
       expr_type_def] >>
  `!e. vyperState$assert T e = return ()` by
    simp[FUN_EQ_THM, vyperStateTheory.assert_def, return_def] >>
  asm_rewrite_tac[bind_return] >>
  BETA_TAC >>
  rewrite_tac[bind_assoc] >> BETA_TAC >>
  once_rewrite_tac[GSYM bind_assoc] >>
  irule gasExemptCertTheory.gas_exempt_cert_error_value >>
  simp[GSYM ignore_bind_def]
QED

Theorem local_fixed_array_producer:
  expr_body_pre cenv cx env (Subscript ann (Name (ArrayT et (Fixed cnt)) id) idx) es /\
  expr_sim_case F ctx func cenv cx idx /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root_var) sz) /\
  compile_expr cenv ty (Subscript ann (Name (ArrayT et (Fixed cnt)) id) idx) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_expr cx (Subscript ann (Name (ArrayT et (Fixed cnt)) id) idx)) (es,s0)
    (\res ee t. ?tv. res = INL tv /\
       vv_post ctx func cenv cx (Subscript ann (Name (ArrayT et (Fixed cnt)) id) idx)
         es sa sb s0 ee tv vv t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       intcall_vv_provenance cenv cx ann sa sb ee tv vv t)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule_all local_fixed_array_index_outcome >> strip_tac >>
  `?initial_entry. lookup_scopes id es.scopes = SOME initial_entry` by
    (`well_typed_expr env (Name (ArrayT et (Fixed cnt)) id)` by
       (fs[expr_body_pre_def] >> drule local_fixed_array_subscript_typing >> simp[]) >>
     drule well_typed_Name_lookup >>
     disch_then (qspecl_then [`es`,`cx`] mp_tac) >>
     (impl_tac >- fs[expr_body_pre_def, expr_sim_inv_def]) >> metis_tac[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      fs[gas_summary_at_def]
      >- suspend "counted_index_success" >>
      Cases_on `res` >- fs[expr_exit_def] >>
      drule_all local_subscript_marked_exception >>
      disch_then (qspecl_then [`ArrayT et (Fixed cnt)`,`ann`] assume_tac) >>
      goal_assum (drule_at Any) >>
      disj2_tac >> conj_tac >- (first_assum ACCEPT_TAC) >>
      qpat_x_assum `expr_exit _ _` mp_tac >>
      mp_tac (Q.ISPECL [`\v. Value v`,`INR y : value + vyperState$exception`] expr_exit_success_map) >>
      simp[FUN_EQ_THM]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  irule local_subscript_exempt >> goal_assum (drule_at Any) >> simp[]
QED

Resume local_fixed_array_producer[counted_index_success]:
  gvs[] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_exec,
              fragGasPathTheory.gas_path_normal] >>
  `bind (eval_expr cx idx) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, es_end with gas_obs := [])` by
    (fs[gas_marked_exec_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_post ctx func cenv cx idx
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)
     sa sm s0 (es_end with gas_obs := []) v i t` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def, locals_kept_def] >> metis_tac[]) >>
  `expr_body_pre cenv cx env
     (Subscript ann (Name (ArrayT et (Fixed cnt)) id) idx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) local_fixed_array_cut_ready) >>
  strip_tac >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by fs[expr_post_def] >>
  rename1 `eval_operand i (drop_fresh sm t) = SOME index_word` >>
  Cases_on `idx_in_range (is_signed_type (expr_type idx)) index_word (n2w cnt)` >> fs[]
  >- (gvs[] >>
      `evaluate_subscripts entry.type entry.value [ValueSubscript (IntV n)] = INL selected` by simp[] >>
      `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by simp[] >>
      drule_all local_fixed_array_marked_success >>
      disch_then (qspecl_then [`ArrayT et (Fixed cnt)`,`ann`] strip_assume_tac) >>
      `lookup_scopes id (es_end with gas_obs := []).scopes = SOME entry /\
       value_has_type entry.type entry.value /\
       mem_path_offset entry.type [ValueSubscript (IntV n)] =
         SOME (Num n * type_memory_size etv,etv)` by simp[] >>
      `expr_body_pre cenv cx env
         (Subscript ann (Name (ArrayT et (Fixed cnt)) id) idx)
         (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
      drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) local_fixed_array_endpoint) >>
      disch_then (qspec_then `sb` strip_assume_tac) >>
      rename1 `eval_operand p endpoint_state = SOME _` >>
      qexistsl_tac [`INL (PlaceR (MemoryPlace id [ValueSubscript (IntV n)]))`,
                    `es_end with gas_obs := []`,`OK endpoint_state`] >>
      conj_tac
      >- (qpat_x_assum `gas_marked_exec _ _ (eval_expr _ (Subscript _ _ _)) _ _ _ _ _` mp_tac >>
          simp[gas_marked_exec_def]) >>
      fs[vv_post_initial_gas]) >>
  drule_all local_fixed_array_marked_abort >>
  disch_then (qspecl_then [`ArrayT et (Fixed cnt)`,`ann`] strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  simp[fragExecTheory.exit_result_def, expr_exit_def]
QED

Finalise local_fixed_array_producer
