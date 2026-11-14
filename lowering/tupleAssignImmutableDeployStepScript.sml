(* Loaded immutable head execution, independent of the original RHS. *)
Theory tupleAssignImmutableDeployStep
Ancestors
  tupleAssignImmutableDeployWord tupleAssignImmutableDeployAggregate
  tupleAssignImmutableDeployRestore tupleAssignImmutableDeploySource
  tuplePlaceHeadOpen immutableAssignMetadata immutableDeployAssignRanges
  immutableDeployAssignAdmissible immutableAssignOpen stmtLoweringMono

Theorem tuple_immutable_loaded_head_step:
  tuple_place_head ctx func ce cx es lo sp tys ltys ltvs vs elems w i s0 /\
  ~block_is_terminated sp /\ body_inv tops ctx ce cx /\ cx.in_deploy /\
  expr_sim_inv ce cx env es /\
  supported_immutable_type tops (src,id) = SOME ity /\
  well_typed_target env (TopLevelNameTarget (src,id)) (EL i tys) /\
  call_evaluation_safe cx (int_calls_target (TopLevelNameTarget (src,id))) /\
  compile_get_target_ptr compile_expr ce (TopLevelNameTarget (src,id)) sp = (place,sa) /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  (!j. j < LENGTH tys /\ ~is_word_type (EL j tys) ==>
    type_memory_size (EL j tvs)+64 < dimword (:256) /\
    type_memory_size (EL j ltvs)+64 < dimword (:256)) /\
  (EXISTS (\t. ~is_word_type t) ltys ==> ce.ce_target CapMcopy) /\
  type_alloc_ok ce (TupleT tys) /\ i < LENGTH tys /\
  (let dst = FST place; loc_opt = FST (SND place); dst_ty_opt = SND (SND place);
       loc = case loc_opt of SOME l => l | NONE => LocMemory;
       dty = case dst_ty_opt of SOME (ValPT t) => t | _ => EL i ltys
   in (if is_word_type (EL i ltys) then
         if is_word_type dty then
           compile_store_at_loc ce.ce_imm_alloca dst (EL i elems) loc_opt
         else emit_void INVALID []
       else compile_assign_value ce dst loc (EL i elems) (is_word_type dty)
         NONE dty (EL i ltys) (type_memory_bytes ce dty)) sa) = ((),sb) /\
  acyclic_struct_metadata ce.ce_struct_fields /\ local_ptrs_reserved ce sa /\
  fn_has_code sp sa func /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  sp.cs_next_var <= sa.cs_next_var /\
  write_place cx (ImmutablePlace src id []) (EL i vs) es = (INL (),ff) ==>
  ?q. gas_marked_path F ctx func s0 0 (OK q) /\ expr_sim_inv ce cx env ff /\
    ~block_is_terminated sb /\
    tuple_place_head ctx func ce cx ff lo sb tys ltys ltvs vs elems w (SUC i) q /\
    (!x. not_fresh_at sp x ==> lookup_var x q = lookup_var x s0) /\
    (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
      FLOOKUP q.vs_allocas aid = SOME entry) /\
    alloca_frame ce es sp s0 ce ff q
Proof
  strip_tac >>
  drule_all immutable_assign_bare_global >> strip_tac >>
  drule_all immutableDeployAssignFactsTheory.immutable_assign_target_layout >>
  disch_then (qspec_then `compile_expr` strip_assume_tac) >>
  `sa = sp /\ place = (Lit (n2w off),SOME LocCode,SOME (ValPT ity))` by
    gvs[compileEnvTheory.comp_return_def] >>
  gvs[] >>
  `ity = EL i tys` by
    (fs[vyperTypeSystemTheory.well_typed_target_def,
        vyperTypeSystemTheory.well_typed_expr_def, AllCaseEqs()] >>
     fs[exprSimHypsDefsTheory.expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
     metis_tac[optionTheory.SOME_11]) >>
  drule_all tuplePlaceSourceTheory.tuple_place_type_facts >> strip_tac >>
  `evaluate_type (get_tenv cx) ity = SOME (EL i tvs) /\
   evaluate_type (get_tenv cx) (EL i ltys) = SOME (EL i ltvs) /\
   type_widens_to (get_tenv cx) (EL i ltys) ity /\
   i < LENGTH ltys` by metis_tac[] >>
  `stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
   s0.vs_current_bb = sa.cs_current_bb /\
   s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
   value_has_type (EL i ltvs) (EL i vs) /\
   (!x. EL i elems = Var x ==> not_fresh_at sa x)` by
    (fs[tuplePlaceHeadTheory.tuple_place_head_def,
        vyperTypeDefaultsTheory.values_have_types_LIST_REL,
        listTheory.LIST_REL_EL_EQN] >> metis_tac[listTheory.EL_MEM]) >>
  `value_has_type (EL i tvs) (EL i vs)` by
    (drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >>
     strip_tac >> gvs[]) >>
  `well_typed_target env (TopLevelNameTarget (NONE,id)) ity` by simp[] >>
  `expr_sim_inv ce cx env ff` by
    (drule_all tuple_immutable_source_write >> strip_tac >> gvs[]) >>
  `!region. ce.ce_imm_alloca = SOME region ==>
      eval_operand region s0 = SOME 0w` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.immutable_base_zero_def] >>
  Cases_on `is_word_type (EL i ltys)`
  >- ( `EL i ltys = ity` by
         metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq] >>
       `is_word_type ity /\ EL i ltvs = EL i tvs` by metis_tac[optionTheory.SOME_11] >>
       `eval_operand (EL i elems) s0 =
          SOME (typed_val_to_w256 (EL i tvs) (EL i vs))` by
         (fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
          qpat_x_assum `!j. i <= j /\ j < LENGTH tys ==> _`
            (qspec_then `i` mp_tac) >> gvs[]) >>
       `compile_store_at_loc ce.ce_imm_alloca (Lit (n2w off))
          (EL i elems) (SOME LocCode) sa = ((),sb)` by gvs[] >>
       `off < dimword (:256)` by
         (first_x_assum (qspec_then `EL i tvs` mp_tac) >> simp[]) >>
       `eval_operand (Lit (n2w off)) s0 = SOME (n2w off)` by
         simp[venomStateTheory.eval_operand_def] >>
       drule_all tuple_immutable_loaded_word_store >>
       disch_then (qspec_then `ctx` strip_assume_tac) >>
       `ci_mono sa sb` by
         (fs[stmtLoweringTheory.compile_store_at_loc_def] >>
          metis_tac[exprLoweringPropsTheory.ci_mono_compile_imm_store_word,
                    pairTheory.SND]) >>
       `same_blocks sa sb /\ ~block_is_terminated sb` by
         (qpat_x_assum `compile_store_at_loc _ _ _ _ _ = _` mp_tac >>
          Cases_on `ce.ce_imm_alloca` >>
          simp[stmtLoweringTheory.compile_store_at_loc_def,
               contextTheory.compile_imm_store_word_def, emitHelperTheory.emit_op_def,
               emitHelperTheory.emit_void_def, compileEnvTheory.fresh_var_def,
               compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
               compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
               compileEnvTheory.comp_ignore_bind_def] >>
          strip_tac >> gvs[exprLoweringPropsTheory.same_blocks_def,
                           compileEnvTheory.block_is_terminated_def] >>
          Cases_on `sa.cs_current_insts` >>
          gvs[compileEnvTheory.block_is_terminated_def, listTheory.LAST_APPEND_CONS,
              venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
          once_rewrite_tac[GSYM listTheory.APPEND] >>
          simp[venomInstTheory.is_terminator_def]) >>
       qmatch_asmsub_abbrev_tac `gas_marked_path F ctx func s0 0 (OK q)` >>
       `type_memory_size (EL i tvs) = 32` by
         metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
       `immutable_value_admissible (EL i tvs) (EL i vs)` by
         metis_tac[immutableDeployAssignAdmissibleTheory.evaluated_immutable_admissible] >>
       qpat_assum `u with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = s0`
         mp_tac >> simp[venomStateTheory.venom_state_component_equality] >> strip_tac >>
       qexists `q` >> simp[] >>
       irule tuple_immutable_endpoint_restore >>
       qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
       qexistsl [`s0`, `off`, `ity`, `EL i tvs`, `id`, `env`] >>
       fs[Abbr `q`, venomStateTheory.lookup_var_def,
            exprLoweringPropsTheory.same_blocks_def,
            venomMemPropsTheory.LENGTH_mstore_eq,
            stmtSimDefsTheory.alloca_frame_same,
            venomStateTheory.venom_state_component_equality] >>
       conj_tac >> rpt strip_tac >>
       irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
       fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  drule_all tuplePlacePointerReadyTheory.tuple_place_index_sizes >> strip_tac >>
  `?sw. eval_operand (EL i elems) s0 = SOME sw /\
     w2n sw = w2n w + SUM (MAP type_memory_size (TAKE i ltvs))` by
    (fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
     qpat_x_assum `!j. i <= j /\ j < LENGTH tys ==> _`
       (qspec_then `i` mp_tac) >> gvs[]) >>
  `val_in_memory (EL i ltvs) (EL i vs) (w2n sw) s0.vs_memory /\
   tuple_place_snapshot ce cx es lo sa.cs_next_id tys ltys ltvs w s0` by
    fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
  `val_wf (EL i ltvs) (EL i vs) /\ val_wf (EL i tvs) (EL i vs)` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields)` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def] >> metis_tac[]) >>
  `type_memory_bytes ce ity = type_memory_size (EL i tvs)` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
   ce.ce_module_var_type (ce.ce_module,id) = SOME ity` by simp[] >>
  drule_all immutableDeployAssignFactsTheory.immutable_assign_declared_region >> strip_tac >>
  `LENGTH ltvs = LENGTH ltys` by simp[] >>
  `w2n sw + type_memory_size (EL i ltvs) < dimword (:256) /\
   w2n sw + type_memory_size (EL i ltvs) <= s0.vs_alloca_next /\
   regions_disjoint (w2n sw) (type_memory_size (EL i ltvs))
     off (type_memory_size (EL i tvs)) /\
   (ity <> EL i ltys /\ ~is_bytestring_type ity ==>
    !b sz. FLOOKUP s0.vs_allocas sa.cs_next_id = SOME (b,sz) ==>
     w2n sw + type_memory_size (EL i ltvs) <= b \/ b+sz <= w2n sw)` by
    (drule_all tuplePlacePointerReadyTheory.tuple_place_snapshot_element_bounds >> strip_tac
     >- (`b+sz <= s0.vs_alloca_next` by
           (fs[exprLoweringPropsTheory.stmt_state_rel_def,
               venomMemDefsTheory.alloca_inv_def,
               venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
         `regions_disjoint off (type_memory_size (EL i tvs)) b sz` by metis_tac[] >>
         simp[] >> conj_tac
         >- (fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
         rpt strip_tac >>
         `alloca_inv s0` by fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
         fs[venomMemDefsTheory.alloca_inv_def,
            venomMemDefsTheory.allocas_non_overlapping_def] >>
         `aid <> sa.cs_next_id` by decide_tac >>
         qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule_all >>
         gvs[] >> decide_tac) >>
     `b+sz <= s0.vs_alloca_next` by
       (irule bodyMemoryDefsTheory.body_local_region_frontier >> metis_tac[]) >>
     `regions_disjoint off (type_memory_size (EL i tvs)) b sz` by metis_tac[] >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> gvs[] >> decide_tac) >>
  `eval_operand (Lit (n2w off)) s0 = SOME (n2w off)` by
    simp[venomStateTheory.eval_operand_def] >>
  `!region x. ce.ce_imm_alloca = SOME region /\ region = Var x ==>
     not_fresh_at sa x` by
    (rpt strip_tac >> gvs[] >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_imm_base]) >>
  drule_at (Pat `stmt_state_rel _ _ _ _ _ _`) tuple_immutable_aggregate_store >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `ce.ce_module_var_type _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  simp[] >>
  disch_then (qspecl_then [`type_slot_size (EL i tvs)`, `ltys`, `i`, `elems`] mp_tac) >>
  (impl_tac >- gvs[valueEncodingPropsTheory.type_memory_size_slots]) >>
  strip_tac >>
  `compile_assign_value ce (Lit (n2w off)) LocCode (EL i elems)
     (is_word_type ity) NONE ity (EL i ltys)
     (type_memory_bytes ce ity) sa = ((),sb)` by gvs[] >>
  `~block_is_terminated sb` by
    metis_tac[immutable_assign_loccode_open] >>
  `ci_mono sa sb` by
    metis_tac[cj 1 ci_mono_stmt_helpers, pairTheory.SND] >>
  `immutable_value_admissible (EL i tvs) (EL i vs)` by
    metis_tac[immutableDeployAssignAdmissibleTheory.evaluated_immutable_admissible] >>
  qexists `q` >> simp[] >>
  `tuple_place_head ctx func ce cx ff lo sb tys ltys ltvs vs elems w (SUC i) q /\
   (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s0) /\
   (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
      FLOOKUP q.vs_allocas aid = SOME entry) /\
   alloca_frame ce es sa s0 ce ff q` suffices_by simp[] >>
  irule tuple_immutable_endpoint_restore >>
  qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qexistsl [`r`, `off`, `ity`, `EL i tvs`, `id`, `env`] >>
  gvs[GSYM valueEncodingPropsTheory.type_memory_size_slots] >>
  gvs[]
QED
