(* Memory case of the body induction, assignment to a base target
   (bodyMemAssign's dispatch): a local held in memory, the value at its lowered type or a bytestring that fits
   (S1's body_assign_local_memory). *)
Theory bodyMemAssignLocalMem
Ancestors
  bodyMemoryPreds bodySim bodyExprPreFacts memoryLocalRhsProps
  bodyRhsRoomMemory exprSimAggregateLayout vyperTypeArgFits
  supportedStmtTraverse supportedStmts supportedExprs vyperTypeSystem
  vyperTypeEnv exprSimHyps exprSimHypsDefs exprSimDefs gasContext
  vyperTypeCallGraph vyperTypeInvariants gasOutcome exprSimMemDefs
  bodyDeclMemoryCounted bodyDeclMemoryCore stmtSimAssignStore stmtSimProps
  valueCopy valueEncoding localPtrsProps exprLoweringProps loweringPosts
  venomState venomExecSemantics compileEnv finite_map list
  vyperLookup loweringSlice bodyMemoryDefs stmtSimAssignMem stmtSimAssignSource
  bodyDeclEmptyMemory emitHelper emitHelperProps venomInst rich_list
  gasSummary gasSummaryCompose fragGasMode allocaFootprint
  stmtSimDefs stmtSimDeclMem valueEncodingProps vyperState
Libs
  monadsyntax

Theorem body_assign_local_rhs_pre[local]:
  !cx id e tops bindings ctx cenv env env' ret_ty es ty.
    body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    FLOOKUP env.var_types id = SOME ty ==>
    supported_expr tops e /\ well_typed_expr env e /\
    type_widens_to env.type_defs (expr_type e) ty /\
    expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  `supported_expr tops e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  `well_typed_expr env e /\ type_widens_to env.type_defs (expr_type e) ty` by
    (gvs[type_stmt_def, atarget_accepts_def, well_typed_expr_def, AllCaseEqs()] >>
     Cases_on `FLOOKUP env.var_assignable id` >> gvs[] >>
     rename1 `FLOOKUP env.var_assignable id = SOME asg` >> Cases_on `asg` >> gvs[]) >>
  simp[] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
      is_dynamic (vyper_to_abi_type (type_env tops) target)` by
    gvs[body_inv_def] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, int_calls_stmt_def,
      int_calls_atarget_def, int_calls_expr_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem assign_local_memory_bytes_pos[local]:
  !cenv cx env es ret_ty id e env' ty.
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    FLOOKUP env.var_types id = SOME ty ==>
    0 < type_memory_bytes cenv ty
Proof
  rpt strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `assignable_type env.type_defs ty` by
    (gvs[type_stmt_def, atarget_accepts_def, AllCaseEqs()] >>
     Cases_on `type_place_target env (NameTarget id)` >> gvs[] >>
     rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> gvs[] >>
     gvs[vyperTypeEnvTheory.type_place_target_NameTarget] >>
     metis_tac[vyperTypeArgFitsTheory.type_widens_to_assignable_type]) >>
  irule exprSimAggregateLayoutTheory.expr_sim_inv_memory_bytes_pos >>
  metis_tac[]
QED

Theorem assign_local_memory_type_cases[local]:
  !cenv e ty.
    (expr_type e = ty \/ lowered_value_type cenv e = ty \/
     is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
    expr_type e = ty \/ is_bytestring_type ty
Proof
  metis_tac[]
QED

Theorem body_assign_local_memory_read[local]:
  !cenv cx env e es tops id ty tyv v es1 entry.
    expr_body_pre cenv cx env e es /\ supported_expr tops e /\
    supported_program tops /\
    cenv.ce_func_return_type = build_func_return_type tops /\
    get_module_code cx NONE = SOME tops /\
    FLOOKUP env.var_types id = SOME ty /\
    type_widens_to env.type_defs (expr_type e) ty /\
    (expr_type e = ty \/ is_bytestring_type ty) /\
    evaluate_type (get_tenv cx) ty = SOME tyv /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) /\
    lookup_scopes id es1.scopes = SOME entry /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    entry.type = tyv /\ value_has_type tyv v /\
    val_footprint tyv v <= type_memory_bytes cenv (lowered_value_type cenv e)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `entry.type = tyv` by metis_tac[memory_rhs_read_local_type] >>
  simp[] >> irule memory_rhs_read_destination_footprint >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`cx`, `env`, `es`, `es1`, `tops`, `ty`] >> simp[]
QED

Theorem assign_local_memory_sizes[local]:
  !cenv cx env es ret_ty id e env' ty tops.
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    FLOOKUP env.var_types id = SOME ty /\
    supported_expr tops e /\ well_typed_expr env e /\
    type_widens_to env.type_defs (expr_type e) ty /\
    (expr_type e = ty \/ is_bytestring_type ty) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    0 < type_memory_bytes cenv ty /\ type_memory_bytes cenv ty < 2 ** 64 /\
    0 < type_memory_bytes cenv (lowered_value_type cenv e) /\
    type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_bytes cenv ty
Proof
  rpt gen_tac >> strip_tac >>
  `0 < type_memory_bytes cenv ty` by
    metis_tac[assign_local_memory_bytes_pos] >>
  `type_memory_bytes cenv ty < 2 ** 64` by
    metis_tac[locals_alloc_ok_def] >>
  metis_tac[memory_rhs_destination_bound]
QED

Theorem assign_local_rhs_located_mem[local]:
  !tops ctx func c cx env e es ltv etv.
    body_inv tops ctx c cx /\ expr_body_pre c cx env e es /\
    body_expr_mem_ok cx e /\ ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (lowered_value_type c e) = SOME ltv /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    type_memory_bytes c (expr_type e) = type_memory_size etv /\
    type_memory_size etv < 2 ** 64 /\ 0 < type_memory_size ltv ==>
    !sa sm sb vv op s0.
      compile_expr c (expr_type e) e sa = (vv, sm) /\
      unwrap_value c vv sm = (op, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved c sa /\
      gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
      stmt_state_rel ctx func c cx es s0 /\
      alloca_history func s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome T (cx_tops cx) (ctx, func)
        (bind (eval_expr cx e) (read_result cx)) (es, s0)
        (\res ee t. ?v. res = INL v /\
          expr_post ctx func c cx e es sa sb s0 ee v op t /\
          expr_store_bound cx (expr_type e) v op t /\
          (vv_location vv = SOME LocMemory ==>
           !sw. eval_operand op t = SOME sw ==>
                w2n sw + type_memory_size ltv <= t.vs_alloca_next) /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
        (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `expr_vv_sim_mem ctx func c cx (expr_type e) e es` by
    metis_tac[body_expr_mem_ok_def] >>
  drule expr_sim_mem_room >>
  disch_then (qspecl_then [`sa`, `sm`, `sb`, `vv`, `op`, `s0`] mp_tac) >>
  impl_tac >- (rpt strip_tac >> gvs[]) >> strip_tac >>
  irule gas_outcome_post_mono >>
  first_x_assum (irule_at (Pos last)) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  rpt strip_tac >> qpat_x_assum `vv_location _ = _ ==> _` drule >>
  disch_then drule >> strip_tac >> decide_tac
QED

Theorem local_memory_write_frame[local]:
  !ctx func cenv cx es s t sa id p sz w pre env entry rest v.
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\ local_ptrs_reserved cenv sa /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!b n. b + n <= w2n w \/ w2n w + type_memory_size entry.type <= b ==>
      mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    val_wf entry.type v /\ val_in_memory entry.type v (w2n w) t.vs_memory ==>
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
        pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t
Proof
  rpt gen_tac >> strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `local_backed func p s (w2n w) sz /\ type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  `local_region cenv es.scopes s id (w2n w) sz` by simp[local_region_def] >>
  `!q. ~not_local_ptr cenv es.scopes q ==> lookup_var q t = lookup_var q s` by
    (rpt strip_tac >>
     `not_fresh_at sa q` by
       (gvs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >> simp[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (`t.vs_data_section = s.vs_data_section` by
       (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
        simp[venom_state_component_equality]) >>
     irule immutables_rel_mem_agree >> qexists_tac `s` >>
     fs[stmt_state_rel_def, state_rel_def] >>
     fs[immutable_alloca_sep_def] >> rpt strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     `regions_disjoint off (type_memory_size tv) (w2n w) sz` by metis_tac[] >>
     `off + type_memory_size tv <= w2n w \/
      w2n w + type_memory_size entry.type <= off` by
       (fs[regions_disjoint_def] >> decide_tac) >>
     qpat_x_assum `!b n. _ ==> mem_bytes_at b n t.vs_memory = _`
       (qspecl_then [`off`, `type_memory_size tv`] mp_tac) >> simp[]) >>
  irule stmt_state_rel_write_local >> simp[] >>
  qexistsl_tac [`s`, `w`] >>
  simp[] >> conj_tac
  >- metis_tac[arithmeticTheory.ADD_COMM] >>
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
  simp[venom_state_component_equality]
QED

Theorem local_memory_store_body_path[local]:
  !ctx func cenv cx es s id p sz pre env entry rest v tyv src ty sa sb sw d.
    compile_store_memory cenv src (Var p) ty ty sa = ((), sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
    eval_operand src s = SOME sw /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    entry.type = tyv /\ value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory tyv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    w2n sw + val_store_size tyv v <= s.vs_alloca_next /\
    alloca_history func s /\ return_buf_frame d cenv sa s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      stmt_state_rel ctx func cenv cx
        (es with scopes :=
          pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      return_buf_frame d cenv sb t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)
Proof
  rpt gen_tac >> strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `?w. lookup_var p s = SOME w /\ w2n w + sz <= s.vs_alloca_next /\
       type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >> gvs[] >> metis_tac[]) >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  drule compile_store_memory_run_size_bound_with_capacity >>
  disch_then (qspecl_then [`s`, `get_tenv cx`, `tyv`, `v`, `sw`, `w`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `stmt_state_rel ctx func cenv cx
     (es with scopes :=
       pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t` by
    (irule local_memory_write_frame >> simp[] >>
     qexistsl_tac [`s`, `sa`, `w`] >> simp[] >>
     conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
     qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s`, `sa`] >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule body_typed_store_memory_mem_ok >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     qexistsl_tac [`w`, `get_tenv cx`, `tyv`, `v`, `sw`] >> simp[] >>
     conj_tac >- metis_tac[] >> gvs[] >> decide_tac) >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    metis_tac[compile_store_memory_same_no_gas] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `gas_path_mem ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s`, `sa`] >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx] >> conj_tac
  >- (Cases_on `d` >- fs[return_buf_frame_def] >>
      rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
      fs[return_buf_frame_def, lookup_var_def]) >>
  fs[lookup_var_def]
QED

Theorem local_header_store_path_mem[local]:
  !ctx func cenv cx es s id p sz w pre env entry rest v wd sa sb.
    emit_void MSTORE [Var p; Lit wd] sa = ((), sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es s /\ alloca_history func s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\ 32 <= type_memory_size entry.type /\
    val_wf entry.type v /\
    val_in_memory entry.type v (w2n w) (mstore (w2n w) wd s).vs_memory ==>
    ?t. stmt_state_rel ctx func cenv cx
          (es with scopes := pre ++
            (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. lookup_var x t = lookup_var x s) /\
        t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
        alloca_history func t /\ gas_path_mem ctx func s 0 (OK t)
Proof
  rpt gen_tac >> strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `w2n w + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  `w2n w + 32 <= s.vs_alloca_next` by decide_tac >>
  drule_all local_header_store_state >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  qabbrev_tac `u = mstore (w2n w) wd s` >>
  `run_inst_seq (emitted_insts sa sb) s = OK u` by
    (`step_inst_base (mk_inst sa.cs_next_id MSTORE [Var p; Lit wd] []) s = OK u` by
       (simp[Abbr `u`] >> irule step_MSTORE >> simp[eval_operand_def]) >>
     simp[run_inst_seq_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (qspecl_then [`Var p`, `Lit wd`, `sa`, `sb`, `s`, `w`] mp_tac
       emit_mstore_mem_ok >> simp[eval_operand_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[is_terminator_def] >>
     qexists_tac `sa` >> simp[is_terminator_def]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[is_terminator_def] >>
     qexistsl_tac [`s`, `sa`] >> simp[is_terminator_def]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx] >>
  simp[Abbr `u`, lookup_var_def, mstore_def]
QED

Theorem compile_assign_local_empty_stmt_frag_mem[local]:
  !d ctx func cx lctx RetQ cenv ty id e es p sz vtyp tyv.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    has_length_word (expr_type e) /\ is_empty_value_expr e /\
    has_length_word vtyp /\ evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    (!gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
      (INL (default_value tyv), es with gas_obs := gs)) /\
    (!entry. lookup_scopes id es.scopes = SOME entry ==> entry.type = tyv) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all assign_local_empty_code_parts >> strip_tac >> gvs[] >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := [] ++ tail) =
    (INL (default_value tyv), es with gas_obs := tail)` by simp[] >>
  drule_all assign_local_continuation_all_tails >> strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `entry.type = tyv` by metis_tac[] >>
  `?w. lookup_var p s0 = SOME w` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  `val_in_memory tyv (default_value tyv) (w2n w)
     (mstore (w2n w) 0w s0).vs_memory /\
   val_wf tyv (default_value tyv) /\ 32 <= type_memory_size tyv` by
    (irule memory_length_word_layout >> simp[mstore_mem_word_at_same] >> metis_tac[]) >>
  `val_wf entry.type (default_value tyv) /\
   32 <= type_memory_size entry.type /\
   val_in_memory entry.type (default_value tyv) (w2n w)
     (mstore (w2n w) 0w s0).vs_memory` by simp[] >>
  drule_all local_header_store_path_mem >> strip_tac >>
  `~block_is_terminated sb` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> Cases_on `sa.cs_current_insts` >>
     gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
         mk_inst_def, is_terminator_def]) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (drule emitted_insts_emit_void >> simp[]) >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]) >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL ()`, `es with scopes := pre ++
    (env |+ (id, entry with <|value := default_value tyv; popped := []|>)) :: rest`,
    `OK t`] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_marked_path_def, gas_explicit_def] >>
      gen_tac >> drule assign_local_admissible_run >>
      disch_then (qspec_then `tail` SUBST1_TAC) >> simp[bind_def]) >>
  disj1_tac >> simp[stmt_lands_def, cenv_top_ext_refl]
QED

Theorem body_assign_local_memory_mem:
  !cx id e ty d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME ty /\ ~is_word_type ty /\
    (expr_type e = ty \/ lowered_value_type cenv e = ty \/
     is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED
