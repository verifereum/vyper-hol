(* Counted sparse storage assignment from a successful RHS memory outcome. *)
Theory bodyMemAssignSparseSuccess
Ancestors
  storeSlotsStorageRegion storeSlotsCountedRun gasPathAllocaHistory
  bodyMemAssignTopCopySuffix exprSimHash stmtSimAssignStorageSparse
  exprOperandVar freshWrites vyperStoragePlaceRegion
  stmtSimAssignStorageCopy bodyMemAssignTopCopyFacts exprLoweringProps
  exprSimDefs exprSimMemDefs stmtSimDefs loweringPosts compileEnv context
  valueEncodingProps vyperStorageBackend vyperStorage vyperValue vyperTyping venomState

Theorem storage_sparse_success_run_mem:
  !ctx func cenv cx e es es1 es' v tv tr mid id slot sa sm sf op loc s0 s1.
    expr_post ctx func cenv cx e es sa sm s0 es1 v op s1 /\
    expr_store_bound cx (expr_type e) v op s1 /\ alloca_history func s1 /\
    ~s1.vs_halted /\ s1.vs_current_bb = sm.cs_current_bb /\
    s1.vs_inst_idx = LENGTH sm.cs_current_insts /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    is_abi_dynamic cenv.ce_struct_fields (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
    ~has_length_word (expr_type e) /\
    (!elem n. expr_type e <> ArrayT elem (Dynamic n)) /\
    value_has_type tv v /\ lowered_value_type cenv e = expr_type e /\
    type_memory_bytes cenv (expr_type e) = type_memory_size tv /\
    declared_storage_region cx mid id [] = SOME (tr,n2w slot,tv) /\
    0 < type_slot_size tv /\ slot + type_slot_size tv <= dimword (:256) /\
    (!mid' id' subs' k' tv'.
       declared_storage_region cx mid' id' subs' = SOME (tr,k',tv') /\
       (k',tv') <> (n2w slot,tv) ==>
       ranges_disjoint slot (type_slot_size tv) (w2n k') (type_slot_size tv')) /\
    write_storage_slot cx tr (n2w slot) tv v es1 = (INL (),es') /\
    lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
    compile_assign_value cenv (Lit (n2w slot))
      (if tr then LocTransient else LocStorage) op F loc
      (expr_type e) (expr_type e) (type_memory_size tv) sm = ((),sf) /\
    fn_has_code sa sm func /\ fn_has_code sm sf func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
    ?t. gas_marked_path T ctx func s1 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
      t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
             lookup_var x t = SOME u) /\
      (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
                  FLOOKUP t.vs_allocas aid = SOME ent) /\
      t.vs_allocas = s1.vs_allocas /\ t.vs_alloca_next = s1.vs_alloca_next /\
      alloca_history func t
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_lower_value_var >> simp[] >> disch_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `post_value_type cenv e = expr_type e` by metis_tac[post_value_type_lowered] >>
  `stmt_state_rel ctx func cenv cx es1 s1 /\
   expr_val_rel cx (expr_type e) v op s1` by fs[expr_post_def] >>
  `?sw. eval_operand op s1 = SOME sw /\
    val_in_memory tv v (w2n sw) s1.vs_memory` by
    (fs[expr_val_rel_def] >> metis_tac[]) >>
  `val_footprint tv v = type_memory_size tv` by metis_tac[topcopy_val_footprint] >>
  `w2n sw + type_memory_size tv < dimword (:256)` by
    (drule_all hash_post_footprint_bound >> simp[]) >>
  `0 < type_memory_size tv` by simp[type_memory_size_slots] >>
  `w2n sw + type_memory_size tv <= s1.vs_alloca_next` by
    (drule_all topcopy_source_bound >> simp[]) >>
  `alloca_inv s1 /\ ~s1.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `slot < dimword (:256)` by decide_tac >>
  `?writes. encode_value tv v = SOME writes` by metis_tac[value_has_type_equiv, optionTheory.IS_SOME_EXISTS] >>
  `compile_store_slots cenv op (Lit (n2w slot)) (expr_type e) tr sm = ((),sf)` by
    (qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `tr` >> simp[stmtLoweringTheory.compile_assign_value_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  `?t ks. gas_marked_path T ctx func s1 0 (OK t) /\
    store_copy_normalize s1 t = FOLDL (\q j. (if tr then tstore else sstore)
      (n2w slot + n2w j) (mload (w2n sw + 32*j) s1) q) s1 ks /\
    (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s1) /\
    t.vs_allocas = s1.vs_allocas /\ t.vs_alloca_next = s1.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts` by suspend "rank" >>
  `stmt_state_rel ctx func cenv cx es' t` by suspend "semantic" >>
  qexists_tac `t` >> simp[] >>
  `alloca_history func t` by metis_tac[gas_marked_path_alloca_history] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[ci_mono_def]) >>
  fs[expr_post_def] >> metis_tac[]
QED

Resume storage_sparse_success_run_mem[rank]:
  qspec_then `type_rank cenv.ce_struct_fields (expr_type e)` mp_tac store_slots_rank_run_mem >>
  disch_then (qspecl_then [`cenv`, `get_tenv cx`, `ctx`] mp_tac) >>
  disch_then (qspecl_then [`expr_type e`, `tv`, `v`] mp_tac) >>
  simp[] >> disch_then (drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`func`, `s1`, `sw`, `n2w slot`] mp_tac) >>
  simp[eval_operand_def] >> metis_tac[]
QED
Resume storage_sparse_success_run_mem[semantic]:
  `es' = set_storage cx es1 tr
    (apply_writes (n2w slot) writes (get_storage cx es1 tr))` by
    (fs[write_storage_slot_eq, AllCaseEqs()] >> metis_tac[]) >>
  pop_assum SUBST1_TAC >>
  irule (INST_TYPE [alpha |-> ``:256``] store_slots_semantic_endpoint_layout) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `store_copy_normalize _ _ = _`)) >>
  goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
  goal_assum (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  qexistsl_tac [`0`, `[]`, `sm`] >>
  simp[storage_subregion_def] >> gvs[]
QED
Finalise storage_sparse_success_run_mem
