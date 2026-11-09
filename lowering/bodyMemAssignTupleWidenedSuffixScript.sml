(* Physical tuple loads preserve the RHS-owned allocation envelope. *)
Theory bodyMemAssignTupleWidenedSuffix
Ancestors
  tupleWidenedStores tupleWidenedLayout bodyMemAssignTupleTargetsSuffix
  bodyMemAssignTupleTargetsLoad bodyMemAssignTupleTargetsFacts tupleTypedLoad tupleStageProps
  loweringPosts valueEncoding vyperTyping compileEnv fragGasPathMem
  stmtSimDefs stmtSimProps freshWrites vyperTypeABI vyperValue
  tupleTargetStoreProps exprSimDefs stmtSimAssignTupleTargets tupleAssignParts
  typedMemoryCopy exprLoweringProps

Theorem tuple_widened_owned_envelope[local]:
  !cenv cx tys tvs vs sa su es op s ctx func.
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    expr_val_own cenv cx (TupleT tys) sa su es (ArrayV (TupleV vs)) op s /\
    expr_val_at cenv cx (TupleT tys) sa su es (ArrayV (TupleV vs)) op s /\
    expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op s /\
    0 < type_memory_size_list tvs /\ stmt_state_rel ctx func cenv cx es s ==>
    ?w b sz. eval_operand op s = SOME w /\
      tuple_in_memory vs tvs (w2n w) s.vs_memory /\ tuple_val_wf vs tvs /\
      b <= w2n w /\ w2n w + type_memory_size_list tvs <= b + sz /\
      b + sz <= s.vs_alloca_next /\ b + sz < dimword (:256) /\
      (?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) /\
      (!name lb len. local_region cenv es.scopes s name lb len ==>
         regions_disjoint b sz lb len)
Proof
  rpt gen_tac >> strip_tac >>
  `tuple_val_wf vs tvs` by
    (fs[expr_val_at_def, is_word_type_def, val_wf_def] >> gvs[]) >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` kall_tac >>
  gvs[expr_val_own_def, expr_val_rel_def, is_word_type_def,
      val_footprint_def, type_memory_size_def, val_in_memory_def, val_wf_def] >>
  `b + sz <= s.vs_alloca_next` by
    (irule tuple_container_frontier >>
     qexistsl_tac [`cenv`, `ctx`, `cx`, `es`, `func`] >> simp[] >> metis_tac[]) >>
  `b + sz < dimword (:256)` by
    (irule tuple_container_bound >>
     qexistsl_tac [`cenv`, `ctx`, `cx`, `es`, `func`, `s`] >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`b`, `sz`] >> simp[regions_disjoint_def] >> metis_tac[]
QED

Theorem tuple_widened_owned_prefix_path_mem:
  !ctx func cenv cx es tys tvs vs sa su ss op elems s d.
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    expr_val_own cenv cx (TupleT tys) sa su es (ArrayV (TupleV vs)) op s /\
    expr_val_at cenv cx (TupleT tys) sa su es (ArrayV (TupleV vs)) op s /\
    expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op s /\
    value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
    0 < type_memory_size_list tvs /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
    compile_tuple_load_all cenv op tys 0 su = (elems,ss) /\
    (!x. op = Var x ==> not_fresh_at su x) /\
    fn_has_code su ss func /\ fn_inst_ids_distinct func /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv su /\
    alloca_history func s /\ return_buf_frame d cenv su s /\ ~s.vs_halted /\
    s.vs_current_bb = su.cs_current_bb /\
    s.vs_inst_idx = LENGTH su.cs_current_insts ==>
    LENGTH elems = LENGTH tys /\ EVERY (\op. ?x. op = Var x) elems /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at ss x) elems /\
    local_ptrs_reserved cenv ss /\ tuple_val_wf vs tvs /\
    ?t (w:256 word) b sz. stmt_state_rel ctx func cenv cx es t /\ ~t.vs_halted /\
      t.vs_current_bb = ss.cs_current_bb /\ t.vs_inst_idx = LENGTH ss.cs_current_insts /\
      tuple_in_memory vs tvs (w2n w) t.vs_memory /\
      b <= w2n w /\ w2n w + type_memory_size_list tvs <= b + sz /\
      b + sz <= t.vs_alloca_next /\ b + sz < dimword (:256) /\
      (?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) /\
      (!name lb len. local_region cenv es.scopes t name lb len ==>
         regions_disjoint b sz lb len) /\
      (!i. i < LENGTH tys ==> ?v. eval_operand (EL i elems) t = SOME v /\
        if is_word_type (EL i tys) then
          v = typed_val_to_w256 (EL i tvs) (EL i vs)
        else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs))) /\
      (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x s) /\
      alloca_history func t /\ return_buf_frame d cenv ss t /\
      t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\ gas_path_mem ctx func s 0 (OK t)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all tuple_widened_owned_envelope >>
  disch_then (qx_choosel_then [`w`, `b`, `sz`]
    (map_every assume_tac o CONJUNCTS)) >>
  `LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs` by
    (irule evaluate_types_LIST_REL >>
     qpat_assum `evaluate_type _ (TupleT tys) = _` mp_tac >>
     simp_tac (srw_ss()) [evaluate_type_def, LET_THM, AllCaseEqs()] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  `values_have_types tvs vs` by fs[value_has_type_def] >>
  `w2n w + type_memory_size_list tvs < dimword (:256) /\
   w2n w + type_memory_size_list tvs <= s.vs_alloca_next` by decide_tac >>
  drule_all compile_tuple_load_all_typed_path_mem >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?t. gas_path_mem _ _ _ _ _ /\ _`
    (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)) >>
  `EVERY (\op. !x. op = Var x ==> not_fresh_at ss x) elems` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  asm_rewrite_tac [] >> qexistsl_tac [`t`, `w`, `b`, `sz`] >> simp[] >> gvs[]
QED

Theorem assign_tuple_widened_targets_suffix_mem:
  !ctx func cx lctx cenv gs e es ee vs tys tvs dtys dtvs
    sa su ss sf op elems s s0 d.
    expr_post ctx func cenv cx e es sa su s0 ee (ArrayV (TupleV vs)) op s /\
    post_value_type cenv e = TupleT tys /\
    expr_val_own cenv cx (TupleT tys) sa su ee (ArrayV (TupleV vs)) op s /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
    0 < type_memory_size_list tvs /\
    LENGTH gs = LENGTH tys /\ LENGTH tys = LENGTH tvs /\ LENGTH tvs = LENGTH vs /\
    LENGTH dtys = LENGTH gs /\ LENGTH dtvs = LENGTH gs /\
    (!i. i < LENGTH gs ==>
       tuple_target_aligned cenv cx (EL i gs) (EL i dtys) (EL i dtvs) /\
       tuple_target_layout ee.scopes (EL i gs) (EL i dtys) (EL i dtvs) (EL i vs) /\
       (is_word_type (EL i tys) = is_word_type (EL i dtys)) /\
       type_widens_to (get_tenv cx) (EL i tys) (EL i dtys) /\
       evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
       value_has_type (EL i tvs) (EL i vs) /\ val_wf (EL i tvs) (EL i vs) /\
       value_has_type (EL i dtvs) (EL i vs) /\ val_wf (EL i dtvs) (EL i vs) /\
       (is_word_type (EL i dtys) ==> type_memory_size (EL i dtvs) = 32) /\
       (~is_word_type (EL i tys) ==> type_memory_size (EL i dtvs) + 64 < dimword (:256))) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !tv.
         evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
       type_memory_bytes cenv ty = type_memory_size tv) /\ cenv.ce_target CapMcopy /\
    compile_tuple_load_all cenv op tys 0 su = (elems,ss) /\
    compile_tuple_store_all cenv tys gs elems ss = ((),sf) /\
    (!x. op = Var x ==> not_fresh_at su x) /\
    sa.cs_next_var <= su.cs_next_var /\ local_ptrs_reserved cenv su /\
    fn_has_code su ss func /\ fn_has_code ss sf func /\ fn_inst_ids_distinct func /\
    alloca_history func s /\ return_buf_frame d cenv su s /\ ~s.vs_halted /\
    s.vs_current_bb = su.cs_current_bb /\ s.vs_inst_idx = LENGTH su.cs_current_insts /\
    ee.gas_obs = [] /\ ~block_is_terminated ss ==>
    ?ee' t'.
      (!tail. assign_tuple_targets cx (TupleTarget gs) (ArrayV (TupleV vs))
         (ee with gas_obs := tail) = (INL (),ee' with gas_obs := tail)) /\
      gas_path_mem ctx func s 0 (OK t') /\
      alloca_history func t' /\ return_buf_frame d cenv sf t' /\
      s.vs_alloca_next <= t'.vs_alloca_next /\
      stmt_post ctx func cx lctx cenv cenv sa sf s0 (INL ())
        (ee' with gas_obs := []) t'
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel ctx func cenv cx ee s /\
   expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op s /\
   expr_val_at cenv cx (TupleT tys) sa su ee (ArrayV (TupleV vs)) op s` by
    fs[expr_post_def] >>
  `LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys tvs` by
    (simp[listTheory.LIST_REL_EL_EQN] >> rpt strip_tac >>
     first_x_assum irule >> first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
  drule_all tuple_widened_owned_prefix_path_mem >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?t w b sz. _`
    (qx_choosel_then [`t`, `w`, `b`, `sz`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "semantic"
QED

Resume assign_tuple_widened_targets_suffix_mem[semantic]:
  `LIST_REL (tuple_source_target cx ee.scopes) gs dtvs` by
    (simp[listTheory.LIST_REL_EL_EQN] >> rpt strip_tac >>
     irule tuple_target_aligned_source >>
     qexistsl_tac [`cenv`, `EL n dtys`, `EL n vs`] >> simp[]) >>
  `LIST_REL value_has_type dtvs vs` by simp[listTheory.LIST_REL_EL_EQN] >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all assign_tuple_targets_safe >> strip_tac >>
  rename1 `assign_tuple_targets _ _ _ ee = (INL (),ee')` >>
  qpat_assum `assign_tuple_targets _ _ _ _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [Once vyperInterpreterTheory.evaluate_def]) >>
  strip_tac >> suspend "stores"
QED

Resume assign_tuple_widened_targets_suffix_mem[stores]:
  `!i. i < LENGTH gs ==> ?v. eval_operand (EL i elems) t = SOME v /\
    if is_word_type (EL i tys) then
      v = typed_val_to_w256 (EL i dtvs) (EL i vs)
    else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs))` by
    suspend "operands" >>
  drule tuple_widened_stores_path_mem >> disch_then drule >>
  disch_then (qspecl_then [`tvs`, `dtys`, `dtvs`, `w2n w`, `b`, `sz`, `ctx`, `func`, `t`] mp_tac) >>
  disch_then (qspec_then `d` mp_tac) >>
  (impl_tac >- (asm_rewrite_tac [] >> rpt conj_tac >> simp[] >> metis_tac[])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?t. stmt_state_rel _ _ _ _ ee' t /\ _`
    (qx_choose_then `fin` (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`ee'`, `fin`] >> conj_tac
  >- (drule_all assign_tuple_target_list_gas_obs >>
      simp[Once vyperInterpreterTheory.evaluate_def]) >>
  conj_tac
  >- (irule (gas_path_mem_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
      qexists_tac `t` >> simp[]) >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >> suspend "frame"
QED

Resume assign_tuple_widened_targets_suffix_mem[operands]:
  gen_tac >> disch_tac >>
  qpat_assum `!i. i < LENGTH gs ==> tuple_target_aligned _ _ _ _ _ /\ _`
    (qspec_then `i` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!i. i < LENGTH tys ==> ?v. _`
    (qspec_then `i` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `is_word_type (EL i tys)`
  >- (`EL i tys = EL i dtys` by metis_tac[return_source_word_widens_eq] >>
      `evaluate_type (get_tenv cx) (EL i dtys) = SOME (EL i dtvs)` by
        metis_tac[tuple_target_aligned_sizes] >>
      `EL i tvs = EL i dtvs` by metis_tac[optionTheory.SOME_11] >> gvs[]) >>
  gvs[] >> metis_tac[]
QED

Resume assign_tuple_widened_targets_suffix_mem[frame]:
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `su.cs_next_var <= ss.cs_next_var` by
    metis_tac[stmtSimReturnTheory.compile_tuple_load_all_grows] >>
  reverse conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  rpt strip_tac >>
  `not_fresh_at su x` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `not_fresh_at ss x` by
    (irule not_fresh_at_mono >> qexists_tac `su` >> simp[]) >> simp[]
QED

Finalise assign_tuple_widened_targets_suffix_mem
