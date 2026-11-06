(*
 * Whitelist removal: for loops over array iterables other than a local
 * fixed-size array.
 *
 * supported_iterator admits only Array (Name (ArrayT ty (Fixed n)) x) with
 * the AST bound equal to the array's size, which body_for_array covers.
 * The checker admits any array-typed iterable; compile_stmt's For Array
 * case handles them all, location-aware, as Python's _lower_iter_loop does,
 * so no form is unhandled on the lowering side.  This theory covers them one
 * form at a time, each stated as body_for_array is, with supported_stmt's
 * For clause minus supported_iterator.  The AST bound only has to be at
 * least the array's capacity (#1202 makes it equal).
 *
 * Survey: what each iterable form needs.
 *
 * The fixed case (stmtSimForArray{,Parts,Frag,Loop,Frame}) is built for one
 * code shape: array_for_code's condition is EQ [Var idx; Lit n], the element
 * copy is a LocMemory copy from a base held in a local's alloca pointer, and
 * the snapshot argument is that the body never writes the local
 * (iterator_unmodified with typed_stmts_projection_frame).  Reusable as is:
 * the copy run (array_iter_copy_run), the round and body lemmas of
 * stmtSimForArrayLoop (array_body_continue_iteration_framed,
 * array_ret_pc_update), the allocation and outcome lemmas of
 * stmtSimForArrayFrag (array_allocate_ready, array_allocation_safe,
 * array_outcome_stmt_post, stmt_frag_start_gas_obs), the block lookups of
 * stmtSimForArrayParts, and the body callbacks of bodySimDeclCases
 * (array_body_scope_callback; array_body_fragment_callback is copied here
 * since that theory is frozen and keeps it local).
 *
 * 1. Local DynArray name (here).  The code loads the length word (MLOAD),
 *    asserts it is at most the capacity (GT/ISZERO/ASSERT), compares the
 *    index with the length register, and reads element k at base + 32 +
 *    k * size.  whitelistForIterDynLoop has the loop, with the length in a
 *    register of the caller frame; whitelistForIterDynFrag the code shape,
 *    the loop entry and the stmt_frag.  The snapshot is the fixed case's,
 *    read through val_in_memory_dynarray.
 * 2. Memory-valued expressions (a list literal, a call result, a struct
 *    member or subscript of a local).  compile_expr runs before the loop;
 *    the fixed or dynamic memory loop then reads a temporary buffer or a
 *    place inside a local.  Needs the compile_expr simulation to give the
 *    base pointer, and a snapshot from "the body never writes that buffer":
 *    alloca freshness for temporaries, iterator_unmodified for places.
 * 3. Storage/transient (self.arr, self.s.arr, self.m[k]).  The loop copies
 *    one element per iteration from its slots (slot_to_memory).  The source
 *    snapshots the array at loop entry while the compiled code re-reads
 *    storage, so for now that leaf takes the premise that the body has no
 *    internal call and no non-static external call; the premise is
 *    temporary, pending a source-semantics change that reads elements per
 *    iteration from their slots.
 * 4. Immutables and calldata.  Byte-addressed loads or a code/calldata
 *    copy per element; the snapshot is free, since both are read-only.
 *
 * TOP-LEVEL:
 *   body_for_dynarray_name - iteration over a local DynArray
 *)
Theory whitelistForIter
Ancestors
  bodySimDeclCases whitelistForIterDynFrag whitelistForIterImm
  exprSimSource bodyExprPreFacts stmtSimProps exprSimHypsDefs list finite_map
  bodySim bodySimStmtCases allocLimits exprSimHyps exprLoweringProps
  stmtSimDecl stmtSimFor stmtSimForParts stmtLowering stmtLoweringMono
  stmtSimForArray stmtSimForArrayFrag vyperTyping fragExec compileEnv
  supportedStmts supportedStmtTraverse compileVyper vyperTypeCallGraph vyperTypeCallStackSoundness vyperAST vyperInterpreter vyperState vyperValue
  vyperValueOperation vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperTypeEnv valueEncoding valueEncodingProps valueEncodingTyping exprSimAggregateEncoding
  venomState arithmetic
Libs
  monadsyntax

Theorem eval_iterator_dynamic_name[local]:
  !cx ty c name es entry elem_tv vs.
    lookup_scopes name es.scopes = SOME entry /\
    entry.value = ArrayV (DynArrayV vs) /\
    evaluate_type (get_tenv cx) (ArrayT ty (Dynamic c)) =
      SOME (ArrayTV elem_tv (Dynamic c)) ==>
    eval_iterator cx (Array (Name (ArrayT ty (Dynamic c)) name)) es =
      (INL vs, es)
Proof
  rpt strip_tac >>
  simp[Once evaluate_def] >> simp[Once evaluate_def] >>
  simp[read_result_def, read_place_def,
       read_memory_path_def, evaluate_subscripts_def, get_scopes_def,
       type_check_def, vyperStateTheory.assert_def, lift_option_type_def,
       lift_sum_def, ignore_bind_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, expr_type_def, extract_elements_def,
       array_elements_def]
QED

Theorem dynarray_elements_typed[local]:
  value_has_type (ArrayTV tv (Dynamic c)) (ArrayV (DynArrayV vs)) /\
  well_formed_type_value (ArrayTV tv (Dynamic c)) /\ k < LENGTH vs ==>
  value_has_type tv (EL k vs) /\ val_wf tv (EL k vs)
Proof
  strip_tac >>
  `value_has_type tv (EL k vs)` by
    fs[value_has_type_def, all_have_type_EVERY, EVERY_EL] >>
  metis_tac[value_has_type_val_wf]
QED

(* The local's alloca holds the length word, then the elements. *)
Theorem dynarray_snapshot_memory[local]:
  !name ei entry tv c vs cenv dp sz ctx func cx s.
  lookup_scopes name ei.scopes = SOME entry /\
  entry.type = ArrayTV tv (Dynamic c) /\
  entry.value = ArrayV (DynArrayV vs) /\ LENGTH vs <= c /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var dp) sz) /\
  stmt_state_rel ctx func cenv cx ei s ==>
  ?base. eval_operand (Var dp) s = SOME base /\
    mload (w2n base) s = n2w (LENGTH vs) /\
    (!k. k < LENGTH vs ==>
      val_in_memory tv (EL k vs)
        (w2n base + (k * type_memory_size tv + 32)) s.vs_memory /\
      w2n base + (k * type_memory_size tv + 32) < dimword (:256))
Proof
  rpt gen_tac >> strip_tac >>
  `local_ptrs_rel func cenv ei.scopes s /\ alloca_room ctx func s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule alloca_room_next_lt >> strip_tac >>
  qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
  simp[local_ptrs_rel_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `lookup_var dp s = SOME w0` >>
  qexists_tac `w0` >> simp[eval_operand_def] >>
  gvs[val_in_memory_dynarray, GSYM mem_word_at_eq_mload] >>
  rpt strip_tac
  >- (drule_all elems_in_memory_EL >> simp[]) >>
  `w2n w0 + (32 + c * type_memory_size tv) <= s.vs_alloca_next` by
    (gvs[type_memory_size_def] >> decide_tac) >>
  `k <= c` by decide_tac >>
  `k * type_memory_size tv <= c * type_memory_size tv` by simp[] >>
  decide_tac
QED

Theorem dynarray_for_source_ready[local]:
  (!tenv s tyv t s3 vs t3 s4 x t4.
    tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tyv,t) /\
    eval_iterator cx (Array (Name (ArrayT typ (Dynamic c)) name)) s3 = (INL vs,t3) /\
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s4 = (INL x,t4)
    ==> body_for_ok cx tyv id stmts vs) /\
  c <= n /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  type_stmt env ret_ty
    (For id typ (Array (Name (ArrayT typ (Dynamic c)) name)) n stmts) = SOME env' ==>
  ?entry tv dp sz vs env_b.
    env' = env /\
    FLOOKUP env.var_types name = SOME (ArrayT typ (Dynamic c)) /\
    id NOTIN FDOM env.var_types /\
    iterator_unmodified (Array (Name (ArrayT typ (Dynamic c)) name)) stmts /\
    type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
    lookup_scopes name es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) typ = SOME tv /\
    entry.type = ArrayTV tv (Dynamic c) /\
    value_has_type entry.type entry.value /\
    well_formed_type_value entry.type /\
    entry.value = ArrayV (DynArrayV vs) /\ LENGTH vs <= c /\
    c < dimword (:256) /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var dp) sz) /\
    (!gs. eval_iterator cx (Array (Name (ArrayT typ (Dynamic c)) name))
            (es with gas_obs := gs) = (INL vs, es with gas_obs := gs)) /\
    body_for_ok cx tv id stmts vs /\
    FLOOKUP cenv.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE
Proof
  strip_tac >>
  `env' = env /\ FLOOKUP env.var_types name = SOME (ArrayT typ (Dynamic c)) /\
   id NOTIN FDOM env.var_types /\
   iterator_unmodified (Array (Name (ArrayT typ (Dynamic c)) name)) stmts /\
   ?env_b. type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b` by
    gvs[type_stmt_def, well_typed_iterator_def, well_typed_expr_def,
        expr_type_def, optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >>
  `?entry. lookup_scopes name es.scopes = SOME entry` by
    (gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def,
         optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  `evaluate_type (get_tenv cx) (ArrayT typ (Dynamic c)) = SOME entry.type` by
    (fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     metis_tac[]) >>
  `c < dimword (:256)` by
    (qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
     simp[evaluate_type_def, AllCaseEqs(), type_slot_size_def,
          bound_length_def] >> rpt strip_tac >>
     rename1 `0 < type_slot_size elem_tv` >>
     `c <= c * type_slot_size elem_tv` by
       (irule LESS_EQ_TRANS >> qexists_tac `c * 1` >> simp[]) >>
     decide_tac) >>
  drule evaluate_type_ArrayT_cases >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME tv` >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    (irule scope_well_typed_lookup_scopes >>
     fs[expr_sim_inv_def, state_well_typed_def] >> metis_tac[]) >>
  `?vs. entry.value = ArrayV (DynArrayV vs) /\ LENGTH vs <= c` by
    (Cases_on `entry.value` >> gvs[value_has_type_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def]) >>
  `?dp sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var dp) sz)` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  `!gs. eval_iterator cx (Array (Name (ArrayT typ (Dynamic c)) name))
          (es with gas_obs := gs) = (INL vs, es with gas_obs := gs)` by
    (gen_tac >> irule eval_iterator_dynamic_name >>
     conj_tac >- (qexists_tac `tv` >> gvs[]) >>
     qexists_tac `entry` >> simp[]) >>
  `eval_iterator cx (Array (Name (ArrayT typ (Dynamic c)) name)) es =
     (INL vs, es)` by
    (`es = es with gas_obs := es.gas_obs` by
       simp[vyperStateTheory.evaluation_state_component_equality] >>
     pop_assum SUBST1_TAC >>
     qpat_assum `!gs. eval_iterator _ _ _ = _` (fn th => rewrite_tac [th])) >>
  `LENGTH vs <= n` by decide_tac >>
  `body_for_ok cx tv id stmts vs` by
    (qpat_x_assum `!tenv s tyv t s3 vs t3 s4 x t4. _` mp_tac >>
     simp[lift_option_type_def, return_def, check_def, assert_def,
          compatible_bound_def] >> disch_then irule >> simp[] >>
     qexistsl_tac [`es`, `es`] >> simp[]) >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  qexistsl_tac [`entry`, `tv`, `dp`, `sz`, `vs`, `env_b`] >> simp[]
QED

(* A copy of bodySimDeclCases' local array_body_fragment_callback, which
   that frozen theory doesn't export. *)
Theorem dynarray_body_fragment_callback[local]:
  !cx stmts tops ctx cenv bindings env ei id typ tv v env_b ret_ty
   func RetQ st0 bc sd ex inc.
    body_stmts_ok cx stmts /\ body_inv tops ctx cenv cx /\
    supported_stmts tops bindings stmts /\
    (!target. supported_stmts_expr_exists
       (expr_abi_decode_target_root target) stmts ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env ei /\
    ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
    id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) typ = SOME tv /\ value_has_type tv v /\
    type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
    EVERY (stmt_exprs_ok cenv) stmts /\
    type_memory_bytes cenv typ < 2 ** 64 /\
    call_evaluation_safe cx (int_calls_stmts stmts) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    declare_local cenv id typ st0 = (bc,sd) ==>
    stmt_frag ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ret_ty stmts)
      (eval_stmts cx stmts)
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v;
                          popped := []|>)) :: ei.scopes)
Proof
  rpt gen_tac >> strip_tac >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (Cases_on `FLOOKUP cenv.ce_vars id` >> gvs[ce_locals_declared_def] >>
     metis_tac[]) >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `same_frame cenv bc` by
    (drule_then irule declare_local_same_frame >> simp[]) >>
  `body_inv tops ctx bc cx` by metis_tac[body_inv_same_frame] >>
  qpat_x_assum `body_stmts_ok _ _`
    (irule o REWRITE_RULE [body_stmts_ok_def]) >>
  simp[] >> rpt conj_tac
  >- metis_tac[stmt_exprs_ok_same_frame]
  >- (qexistsl_tac [`bindings`, `tops`] >> simp[])
  >- (qexistsl_tac [`extend_local env id typ F`, `env_b`] >> simp[] >>
      `bc.ce_struct_fields = cenv.ce_struct_fields` by
        metis_tac[same_frame_struct_fields] >>
      conj_tac >- metis_tac[ce_locals_declared_declare_local] >>
      conj_tac >- metis_tac[locals_alloc_ok_extend] >>
      irule expr_sim_inv_for_scope >> metis_tac[]) >>
  metis_tac[frame_ret_ok_same_frame]
QED

(* A local DynArray: the lowering loads the length word at the local's
   pointer, asserts it is at most the capacity c, and reads element k at
   base + 32 + k * size.  The source iterates the snapshot's elements; the
   body cannot write the array (iterator_unmodified). *)
Theorem body_for_dynarray_name:
  !cx id typ c name n stmts tops bindings ctx func cenv env env' ret_ty lctx
   RetQ es.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\
       eval_iterator cx (Array (Name (ArrayT typ (Dynamic c)) name)) s'3' =
       (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ok cx tyv id stmts vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_ok cx (Array (Name (ArrayT typ (Dynamic c)) name))) /\
    body_inv tops ctx cenv cx /\
    supported_type_namespace typ /\ supported_stmts tops bindings stmts /\
    ~supported_stmts_expr_exists expr_internal_call_root stmts /\ c <= n /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target)
       (For id typ (Array (Name (ArrayT typ (Dynamic c)) name)) n stmts) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty
      (For id typ (Array (Name (ArrayT typ (Dynamic c)) name)) n stmts) =
      SOME env' /\
    stmt_exprs_ok cenv
      (For id typ (Array (Name (ArrayT typ (Dynamic c)) name)) n stmts) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (For id typ (Array (Name (ArrayT typ (Dynamic c)) name)) n stmts)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (For id typ (Array (Name (ArrayT typ (Dynamic c)) name)) n stmts))
      (eval_stmt cx
         (For id typ (Array (Name (ArrayT typ (Dynamic c)) name)) n stmts)) es
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dynarray_for_source_ready >> strip_tac >> gvs[] >>
  `!target. supported_stmts_expr_exists
      (expr_abi_decode_target_root target) stmts ==>
      occurs_abi_decode_target target tops` by
    fs[supported_stmt_expr_exists_def] >>
  drule_all array_for_layout_ready >> strip_tac >>
  `name <> id` by metis_tac[optionTheory.NOT_NONE_SOME] >>
  `cenv.ce_alloca_locals /\ supported_program tops /\
   get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `EVERY (stmt_exprs_ok cenv) stmts /\ type_memory_bytes cenv typ < 2 ** 64` by
    fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       stmts_exprs_ok_EVERY, alloc_limits_stmt_def, stmt_valued_return_def] >>
  `call_evaluation_safe cx (int_calls_stmts stmts)` by
    (fs[int_calls_stmt_def] >> metis_tac[call_evaluation_safe_append_right]) >>
  MATCH_MP_TAC
    (Q.GENL [`arr_ptr`, `arr_sz`, `tv`, `vs`]
      (BETA_RULE (Q.SPEC `\ei. expr_sim_inv cenv cx env ei /\
                              lookup_scopes name ei.scopes = SOME entry`
                   (Q.GEN `P` (SPEC_ALL compile_for_dynarray_frag))))) >>
  qexistsl_tac [`dp`, `sz`, `tv`, `vs`] >>
  simp[] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule (SIMP_RULE std_ss [cs_mono_def] (cj 2 compile_stmt_cs_mono)) >>
      simp[])
  >- (gen_tac >> strip_tac >> irule dynarray_elements_typed >>
      simp[] >> qexists_tac `c` >> gvs[])
  >- (rpt strip_tac >> irule dynarray_snapshot_memory >> metis_tac[])
  >- (rpt strip_tac >>
      `body_stmts_ok cx stmts` by
        (fs[body_for_ok_def] >> Cases_on `vs` >> fs[]) >>
      irule dynarray_body_fragment_callback >>
      metis_tac[dynarray_elements_typed]) >>
  rpt gen_tac >> strip_tac >>
  drule_all dynarray_elements_typed >> strip_tac >>
  `expr_sim_inv cenv cx env (ei with gas_obs := gs) /\
   lookup_scopes name (ei with gas_obs := gs).scopes = SOME entry /\
   lookup_scopes id (ei with gas_obs := gs).scopes = NONE` by simp[] >>
  `eval_stmts cx stmts
     ((ei with gas_obs := gs) with scopes :=
       (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs;
                         popped := []|>)) :: (ei with gas_obs := gs).scopes) =
     (r, es2)` by simp[] >>
  drule_at (Pat `eval_stmts`) array_body_scope_callback >>
  disch_then drule_all >> simp[] >> metis_tac[]
QED
