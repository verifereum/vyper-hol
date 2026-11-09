(* Physical tuple loads preserve the RHS-owned allocation envelope. *)
Theory bodyMemAssignTupleWidenedSuffix
Ancestors
  tupleWidenedStores tupleWidenedLayout bodyMemAssignTupleTargetsSuffix
  bodyMemAssignTupleTargetsLoad bodyMemAssignTupleTargetsFacts tupleTypedLoad tupleStageProps
  loweringPosts valueEncoding vyperTyping compileEnv fragGasPathMem
  stmtSimDefs stmtSimProps freshWrites vyperTypeABI vyperValue

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
