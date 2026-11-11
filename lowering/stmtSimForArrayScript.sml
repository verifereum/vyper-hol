(* Array iteration boundaries shared by loop simulation and body adapters. *)
Theory stmtSimForArray
Ancestors
  supportedStmts vyperTypeSystem vyperTypeValues vyperValue
  arithmetic words vyperAST vyperInterpreter vyperState vyperValueOperation
  vyperArray vyperTypeEnv vyperTypeInvariants vyperTyping exprSimHyps
  compileEnv valueEncodingProps valueEncodingProofs valueCopy stmtLowering
  emitHelperProps exprLoweringProps venomState emitHelper rich_list
  immutableMemoryFrame stmtSimDeclStore loweringSlice localPtrsProps
  stmtSimForArrayFrame valueEncodingTyping memoryValueEncoding list alist pair
  exprSimHypsDefs exprSimProps

Theorem array_for_hypotheses:
  !tops bindings id ty e n body env ret_ty env'.
  supported_stmt tops bindings (For id ty (Array e) n body) /\
  type_stmt env ret_ty (For id ty (Array e) n body) = SOME env' ==>
  ?name env_b.
    e = Name (ArrayT ty (Fixed n)) name /\ env' = env /\
    well_typed_expr env (Name (ArrayT ty (Fixed n)) name) /\
    assignable_type env.type_defs ty /\ id NOTIN FDOM env.var_types /\
    iterator_unmodified (Array (Name (ArrayT ty (Fixed n)) name)) body /\
    type_stmts (extend_local env id ty F) ret_ty body = SOME env_b /\
    supported_stmts tops bindings body /\
    ~supported_stmts_expr_exists expr_internal_call_root body
Proof
  rpt gen_tac >> strip_tac >>
  `?name. e = Name (ArrayT ty (Fixed n)) name` by
    (irule supported_array_iterator_shape >>
     gvs[supported_stmt_def] >> metis_tac[]) >>
  gvs[type_stmt_def, supported_stmt_def, well_typed_iterator_def,
      expr_type_def, optionTheory.IS_SOME_EXISTS, AllCaseEqs()]
QED

Theorem evaluated_fixed_array_bound:
  evaluate_type tenv (ArrayT ty (Fixed n)) = SOME tv ==>
    0 < n /\ n < dimword (:256)
Proof
  simp[evaluate_type_def, AllCaseEqs(), type_slot_size_def,
       bound_length_def] >> rpt strip_tac >>
  rename1 `0 < type_slot_size elem_tv` >>
  `n <= n * type_slot_size elem_tv` by
    (irule LESS_EQ_TRANS >> qexists_tac `n * 1` >>
     simp[]) >> decide_tac
QED

Theorem eval_iterator_fixed_name:
  !cx ty n name es entry elem_tv av.
    lookup_scopes name es.scopes = SOME entry /\
    entry.value = ArrayV av /\
    evaluate_type (get_tenv cx) (ArrayT ty (Fixed n)) =
      SOME (ArrayTV elem_tv (Fixed n)) ==>
    eval_iterator cx (Array (Name (ArrayT ty (Fixed n)) name)) es =
      (INL (MAP Value (array_elements (ArrayTV elem_tv (Fixed n)) av)), es)
Proof
  rpt strip_tac >>
  simp[Once evaluate_def] >> simp[Once evaluate_def] >>
  simp[array_iterator_results_def, read_result_def, read_place_def,
       read_memory_path_def, evaluate_subscripts_def, get_scopes_def,
       type_check_def, vyperStateTheory.assert_def, lift_option_type_def, lift_sum_def,
       ignore_bind_def, vyperStateTheory.bind_def, vyperStateTheory.return_def,
       expr_type_def, extract_elements_def]
QED

Theorem fixed_array_elements_length:
  LENGTH (array_elements (ArrayTV elem_tv (Fixed n)) (SArrayV al)) = n
Proof
  simp[array_elements_def]
QED

Theorem array_name_local_binding:
  !cenv cx env es ty n name.
    expr_sim_inv cenv cx env es /\
    well_typed_expr env (Name (ArrayT ty (Fixed n)) name) ==>
    ?entry elem_tv ptr sz.
      lookup_scopes name es.scopes = SOME entry /\
      evaluate_type (get_tenv cx) ty = SOME elem_tv /\
      entry.type = ArrayTV elem_tv (Fixed n) /\
      value_has_type entry.type entry.value /\
      well_formed_type_value entry.type /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ptr) sz) /\
      cenv.ce_var_type name = SOME (ArrayT ty (Fixed n)) /\
      0 < n /\ n < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  `?entry. lookup_scopes name es.scopes = SOME entry` by
    (gvs[expr_sim_inv_def, well_typed_expr_def, env_consistent_def,
         env_scopes_consistent_def, optionTheory.IS_SOME_EXISTS] >>
     metis_tac[]) >>
  `evaluate_type (get_tenv cx) (ArrayT ty (Fixed n)) = SOME entry.type` by
    (fs[expr_sim_inv_def, well_typed_expr_def, env_consistent_def,
        env_scopes_consistent_def] >> metis_tac[]) >>
  drule evaluated_fixed_array_bound >> strip_tac >>
  drule evaluate_type_ArrayT_cases >> strip_tac >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    (irule scope_well_typed_lookup_scopes >>
     fs[expr_sim_inv_def, state_well_typed_def] >> metis_tac[]) >>
  fs[expr_sim_inv_def, well_typed_expr_def] >> metis_tac[]
QED

(* Project the source snapshot at the address used by an array iteration. *)
Theorem fixed_array_element_in_memory:
  !tv n kvs base mem k.
    val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) base mem /\
    k < n ==>
    val_in_memory tv
      (EL k (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs)))
      (base + k * type_memory_size tv) mem
Proof
  rpt strip_tac >>
  gvs[val_in_memory_sarray, array_elements_def] >>
  Cases_on `ALOOKUP kvs k` >> gvs[] >>
  drule_all kvs_in_memory_lookup >> simp[]
QED

Theorem fixed_array_element_extent:
  !base n sz k limit.
    base + n * sz <= limit /\ k < n ==>
    base + k * sz + sz <= limit
Proof
  rpt strip_tac >>
  `(k + 1) * sz <= n * sz` by simp[] >>
  qpat_x_assum `(k + 1) * sz <= _` mp_tac >>
  pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac
QED

Theorem fixed_array_element_address:
  !base n sz k.
    base + n * sz < dimword (:256) /\ k < n ==>
    w2n ((n2w base : bytes32) + n2w k * n2w sz) = base + k * sz
Proof
  rpt strip_tac >> rename1 `addr + n * sz < dimword (:256)` >>
  `addr + k * sz < dimword (:256)` by
    (`addr + n * sz <= dimword (:256) - 1` by decide_tac >>
     drule_all fixed_array_element_extent >> decide_tac) >>
  simp[word_add_n2w, word_mul_n2w, w2n_n2w]
QED

Theorem array_iter_composite_copy_run:
  !cenv src dst ty bytes sa sb s tenv tv v sw dw.
    ~is_word_type ty /\
    compile_iter_elem_copy cenv src dst bytes LocMemory F ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    val_in_memory tv v (w2n sw) s.vs_memory /\
    type_memory_size tv + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  irule compile_store_memory_run_size_bound_with_capacity >> simp[] >>
  qexistsl_tac [`cenv`, `dst`, `src`, `sw`, `tenv`, `ty`] >>
  gvs[compile_iter_elem_copy_def]
QED

(* Unlike fresh_vars_wrt, not_fresh_at is stable when this code is run
   again on a later iteration, after its temporary output has a value. *)
Theorem array_iter_word_copy_run:
  !cenv src dst ty bytes sa sb s sw dw.
    is_word_type ty /\
    compile_iter_elem_copy cenv src dst bytes LocMemory F ty ty sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      t.vs_memory = (mstore (w2n dw) (mload (w2n sw) s) s).vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  `!w. eval_operand dst
      (update_var (STRING #"%" (toString sa.cs_next_var)) w s) = SOME dw` by
    (Cases_on `dst` >>
     gvs[eval_operand_def, lookup_var_update_var, not_fresh_at_def]) >>
  gvs[compile_iter_elem_copy_def, emit_op_def, emit_void_def, comp_bind_def,
      comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def,
      comp_return_def, LET_THM] >>
  simp[emitted_insts_def, same_blocks_def, DROP_APPEND1,
       venomInstTheory.is_terminator_def] >>
  qpat_assum `eval_operand src s = SOME sw`
    (mp_then Any assume_tac step_MLOAD) >>
  simp[run_inst_seq_def, step_MSTORE, eval_operand_def, lookup_var_update_var] >>
  qmatch_goalsub_abbrev_tac `step_inst_base inst mid` >>
  `step_inst_base inst mid = OK (mstore (w2n dw) (mload (w2n sw) s) mid)` by
    (simp[Abbr `inst`] >> irule step_MSTORE >>
     simp[Abbr `mid`, eval_operand_def, lookup_var_update_var]) >>
  simp[] >> simp[Abbr `mid`, mstore_def, update_var_def, LET_THM] >>
  rpt strip_tac >> gvs[not_fresh_at_def, lookup_var_def,
                       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem array_iter_mload_mstore_value:
  !tv v src dst s.
    val_in_memory tv v src s.vs_memory /\ val_wf tv v /\
    type_memory_size tv <= 32 ==>
    val_in_memory tv v dst (mstore dst (mload src s) s).vs_memory
Proof
  rpt strip_tac >> irule valueEncodingPropsTheory.val_in_memory_relocate >>
  simp[] >> qexistsl_tac [`s.vs_memory`, `32`, `src`] >> simp[] >>
  irule mload_eq_mem_bytes_at_eq >>
  simp[GSYM mem_word_at_eq_mload, mstore_mem_word_at_same]
QED

Theorem array_iter_copy_run:
  !cenv src dst ty bytes sa sb s tenv tv v sw dw.
    compile_iter_elem_copy cenv src dst bytes LocMemory F ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    val_in_memory tv v (w2n sw) s.vs_memory /\
    type_memory_size tv + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_word_type ty`
  >- (drule_all array_iter_word_copy_run >> strip_tac >>
      drule_all word_tv_memory_size >> strip_tac >> simp[] >>
      conj_tac
      >- (irule array_iter_mload_mstore_value >> simp[]) >>
      conj_tac
      >- (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = _` mp_tac >>
          simp[venom_state_component_equality]) >>
      conj_tac
      >- (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]) >>
      simp[immutable_mstore_capacity, MAX_DEF]) >>
  drule_all array_iter_composite_copy_run >> simp[]
QED

(* An allocation-local copy preserves the constructor's immutable snapshot. *)
Theorem array_iter_copy_immutables:
  !func cenv cx es s t inst b sz bytes.
    stmt_state_rel ctx func cenv cx es s /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\ bytes <= sz /\
    t.vs_data_section = s.vs_data_section /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!a len. a + len <= b \/ b + bytes <= a ==>
      mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) ==>
    immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t
Proof
  rpt gen_tac >> strip_tac >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[stmt_state_rel_def, immutable_alloca_sep_def] >>
  strip_tac >> qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
  disch_then drule_all >> strip_tac >>
  `regions_disjoint off (type_memory_size tv) b sz` by metis_tac[] >>
  first_x_assum irule >> fs[regions_disjoint_def] >> decide_tac
QED

Theorem array_iter_copy_declare_rel:
  !ctx func cenv cx es s t id p sz w inst v tv sc rest a sa.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!q. q = p \/ ~not_local_ptr cenv es.scopes q ==> not_fresh_at sa q) /\
    (!b len. b + len <= w2n w \/ w2n w + type_memory_size tv <= b ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    type_memory_size tv <= sz /\ val_wf tv v /\ value_has_type tv v /\
    val_in_memory tv v (w2n w) t.vs_memory ==>
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
        (sc |+ (id, <|assignable := a; type := tv; value := v; popped := []|>)) :: rest) t
Proof
  rpt gen_tac >> strip_tac >>
  `memory_value_rel tv v (w2n w) t.vs_memory` by
    metis_tac[val_in_memory_memory_value_rel] >>
  `!n b len. n <> id /\ local_region cenv es.scopes s n b len ==>
      mem_bytes_at b len s.vs_memory = mem_bytes_at b len t.vs_memory` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) sz b len` by
       (irule local_ptrs_rel_alloca_disjoint >>
        qexistsl_tac [`cenv`, `func`, `inst`, `n`, `p`, `es.scopes`, `s`] >>
        fs[stmt_state_rel_def, state_rel_def]) >>
     irule EQ_SYM >> first_x_assum irule >>
     fs[regions_disjoint_def] >> decide_tac) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (`t.vs_data_section = s.vs_data_section` by
       (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = _` mp_tac >>
        simp[venom_state_component_equality]) >>
     drule_all array_iter_copy_immutables >> simp[]) >>
  irule stmt_state_rel_declare_memory >> simp[] >>
  qexistsl_tac [`inst`, `s`, `w`] >> simp[] >>
  qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = _` mp_tac >>
  simp[venom_state_component_equality] >> metis_tac[]
QED

Theorem fixed_array_elements_typed:
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV al)) /\
  well_formed_type_value (ArrayTV tv (Fixed n)) /\ k < n ==>
  value_has_type tv (EL k (array_elements (ArrayTV tv (Fixed n)) (SArrayV al))) /\
  val_wf tv (EL k (array_elements (ArrayTV tv (Fixed n)) (SArrayV al)))
Proof
  strip_tac >>
  `well_formed_type_value tv` by fs[well_formed_type_value_def] >>
  `value_has_type tv (EL k (array_elements (ArrayTV tv (Fixed n)) (SArrayV al)))` by
    (simp[array_elements_def] >> Cases_on `ALOOKUP al k` >> simp[]
     >- metis_tac[default_value_well_typed] >>
     fs[value_has_type_def] >> drule sparse_has_type_all_have_type >>
     simp[all_have_type_EVERY, EVERY_MEM, MEM_MAP] >>
     metis_tac[ALOOKUP_MEM, SND]) >>
  metis_tac[value_has_type_val_wf]
QED

Theorem array_snapshot_memory:
  !name ei entry tv n al cenv ptr sz ctx func cx s.
  lookup_scopes name ei.scopes = SOME entry /\
  entry.type = ArrayTV tv (Fixed n) /\
  entry.value = ArrayV (SArrayV al) /\
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV al)) /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ptr) sz) /\
  stmt_state_rel ctx func cenv cx ei s ==>
  ?base. eval_operand (Var ptr) s = SOME base /\
    (!k. k < n ==>
      val_in_memory tv
        (EL k (array_elements (ArrayTV tv (Fixed n)) (SArrayV al)))
        (w2n base + k * type_memory_size tv) s.vs_memory /\
      w2n base + k * type_memory_size tv < dimword (:256))
Proof
  rpt gen_tac >> strip_tac >>
  `local_ptrs_rel func cenv ei.scopes s /\ alloca_room ctx func s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule alloca_room_next_lt >> strip_tac >>
  qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
  simp[local_ptrs_rel_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `lookup_var p s = SOME w0` >>
  `val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV al)) (w2n w0)
     s.vs_memory` by metis_tac[memory_value_rel_val_in_memory] >>
  qexists_tac `w0` >> simp[eval_operand_def] >>
  rpt strip_tac
  >- (irule fixed_array_element_in_memory >> metis_tac[]) >>
  `w2n w0 + n * type_memory_size tv <= s.vs_alloca_next` by
    (gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  drule_all fixed_array_element_extent >> decide_tac
QED
