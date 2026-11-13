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
 * (array_body_scope_callback and array_body_fragment_callback).
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
 * 4. Immutables.  Byte-addressed loads or a code copy per element.  Runtime
 *    immutables are read-only; constructor snapshots use iterator_unmodified.
 *    Calldata-origin arguments are decoded to memory before the body and
 *    belong to form (2); compile_expr has no raw LocCalldata producer.
 *
 * TOP-LEVEL:
 *   body_for_dynarray_name - iteration over a local DynArray
 *)
Theory whitelistForIter
Ancestors
  vyperTypeContract
  bodyDynArraySource bodySimDeclCases whitelistForIterDynFrag whitelistForIterMem whitelistForIterImm
  exprSimSource bodyExprPreFacts stmtSimProps exprSimHypsDefs list finite_map
  bodySim bodySimStmtCases allocLimits exprSimHyps exprLoweringProps
  stmtSimDecl stmtSimFor stmtSimForParts stmtLowering stmtLoweringMono
  stmtSimForArray stmtSimForArrayFrag vyperTyping fragExec compileEnv loweringStateRelDefs
  supportedStmts supportedStmtTraverse compileVyper vyperTypeCallGraph vyperTypeCallStackSoundness vyperAST vyperInterpreter vyperState vyperValue
  vyperValueOperation vyperTypeSystem vyperTypeInvariants vyperTypeValues
  targetPlaceSim exprSimTopLevelProps bodyStorageMetadata
  vyperTypeEnv valueEncoding valueEncodingProps valueEncodingTyping exprSimAggregateEncoding
  venomState arithmetic
Libs
  monadsyntax

val _ = Parse.hide "body";

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
            (es with gas_obs := gs) = (INL (MAP Value vs), es with gas_obs := gs)) /\
    body_for_ok cx tv id stmts (MAP Value vs) /\
    FLOOKUP cenv.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE
Proof
  strip_tac >>
  drule_all dynarray_name_source_ready >> strip_tac >>
  rename1 `entry.value = ArrayV (DynArrayV vs)` >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME tv` >>
  rename1 `FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var dp) sz)` >>
  `eval_iterator cx (Array (Name (ArrayT typ (Dynamic c)) name)) es =
     (INL (MAP Value vs), es)` by
    (`es = es with gas_obs := es.gas_obs` by
       simp[vyperStateTheory.evaluation_state_component_equality] >>
     pop_assum SUBST1_TAC >>
     qpat_assum `!gs. eval_iterator _ _ _ = _` (fn th => rewrite_tac [th])) >>
  `LENGTH vs <= n` by decide_tac >>
  `body_for_ok cx tv id stmts (MAP Value vs)` by
    (qpat_x_assum `!tenv s tyv t s3 vs t3 s4 x t4. _` mp_tac >>
     simp[lift_option_type_def, return_def, check_def, assert_def,
          compatible_bound_def] >> disch_then irule >> simp[] >>
     qexistsl_tac [`es`, `es`] >> simp[]) >>
  qexistsl_tac [`entry`, `tv`, `dp`, `sz`, `vs`, `env_b`] >> simp[]
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
    body_stmt_safe tops (For id typ (Array (Name (ArrayT typ (Dynamic c)) name)) n stmts) /\
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
  imp_res_tac body_stmt_safe_for_body >>
  drule_all dynarray_for_source_ready >> strip_tac >> gvs[] >>
  `!target. supported_stmts_expr_exists
      (expr_abi_decode_target_root target) stmts ==>
      occurs_abi_decode_target target tops` by
    fs[supported_stmt_expr_exists_def] >>
  drule_all array_for_layout_ready >> strip_tac >>
  `name <> id` by metis_tac[optionTheory.NOT_NONE_SOME] >>
  `cenv.ce_alloca_locals /\ supported_program tops /\
   get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `stmts_exprs_ok (cenv with ce_var_type updated_by (id =+ SOME typ)) stmts /\ type_memory_bytes cenv typ < 2 ** 64` by
    fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       stmts_exprs_ok_thm, alloc_limits_stmt_def, stmt_valued_return_def] >>
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
        (fs[body_for_ok_def] >> Cases_on `vs` >>
         gvs[read_result_def, return_def]) >>
      irule array_body_fragment_callback >>
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

(* ADMITTED (out-of-packet key, allowed by the plan session): a For over a
   memory iterable, an array that is not rooted at a top-level name, has no
   ternary in it (#1254) and whose lowered value has the annotated type (no
   widened internal call, #767): a temporary or a projection of a local. The unused keep-hook compilation
   bridge was deleted; the real proof must also derive the iterator's source
   place classification, alongside stmt_post's alloca_frame and vv_at's
   local_place_at. *)
Theorem body_for_memory_iterable:
  !cx id typ it n body tops bindings ctx func cenv env env' ret_ty lctx RetQ
   es.
    body_stmt_safe tops (For id typ it n body) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_ok cx it) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (For id typ it n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    (?e. it = Array e /\ ~(?t v. e = Name t v) /\ ~(?t nid. e = TopLevelName t nid) /\
       ~supported_expr_exists (\x. ?t c l r. x = IfExp t c l r) e /\
       post_value_type cenv e = expr_type e /\
       !tgt nid. loop_iterator_place e = SOME tgt ==> target_root tgt <> TopLevelNameTarget nid) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (eval_stmt cx (For id typ it n body)) es
Proof
  cheat
QED

(* The For case of body_sim_mutual over every iterator but a range of two
   literals: it dispatches each array form to its case lemma. *)
Theorem body_for_other:
  !cx id typ it n body tops bindings ctx func cenv env env' ret_ty lctx RetQ
   es res es'.
    body_stmt_safe tops (For id typ it n body) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_ok cx it) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (For id typ it n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    ~(?a1 n1 a2 n2. it = Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (eval_stmt cx (For id typ it n body)) es
Proof
  rpt strip_tac >>
  imp_res_tac body_stmt_safe_for_body >> Cases_on `it`
  >~ [`For _ _ (Range _ _) _ _`] >- (irule body_for_range >> simp[] >> metis_tac[]) >>
  rename1 `For id typ (Array e) n body` >>
  `supported_type_namespace typ /\ supported_iterator tops typ (Array e) n /\
   supported_stmts tops bindings body /\
   ~supported_stmts_expr_exists expr_internal_call_root body` by
    fs[supported_stmt_def] >>
  `well_typed_expr env e /\ ?bd. expr_type e = ArrayT typ bd` by
    gvs[type_stmt_def, well_typed_iterator_def, AllCaseEqs()] >>
  `!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
              (For id typ (Array e) n body) ==> occurs_abi_decode_target target tops` by
    metis_tac[] >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   cenv.ce_func_return_type = build_func_return_type tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops))` by
    fs[bodySimTheory.body_inv_def] >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_declared_return >> qexists_tac `tops` >>
     simp[] >> rpt strip_tac >>
     gvs[supported_iterator_def]) >>
  Cases_on `(?t v. e = Name t v) \/ (?t nid. e = TopLevelName t nid)`
  >- (pop_assum strip_assume_tac >>
      gvs[supported_iterator_def, expr_type_def, place_access_root]
      >~ [`Name (ArrayT _ bd) arr`]
      >- (Cases_on `bd` >> gvs[]
          >- (irule body_for_array >> simp[] >> metis_tac[]) >>
          irule body_for_dynarray_name >> simp[] >> metis_tac[]) >>
      rename1 `TopLevelName (ArrayT _ bd) nid` >>
      PairCases_on `nid` >> gvs[optionTheory.IS_SOME_EXISTS] >>
      drule_all supported_immutable_type_find_NONE >> strip_tac >> gvs[] >>
      `FLOOKUP env.bare_globals (NONE,nid1) = SOME (ArrayT typ bd)` by
        (irule toplevel_find_NONE_bare_global >>
         fs[expr_sim_inv_def] >> metis_tac[]) >>
      `IS_SOME (supported_immutable_type tops (NONE,nid1))` by simp[] >>
      irule body_for_immutable_array >> simp[] >> metis_tac[]) >>
  `~supported_expr_exists (\x. ?t c l r. x = IfExp t c l r) e /\
   !tgt nid. loop_iterator_place e = SOME tgt ==> target_root tgt <> TopLevelNameTarget nid` by
    (Cases_on `e` >> gvs[supported_iterator_def, place_access_root]) >>
  irule body_for_memory_iterable >> simp[] >> metis_tac[]
QED

Theorem body_for_case:
  !cx id typ it n body.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_ok cx it) ==>
    body_stmt_ok cx (For id typ it n body)
Proof
  rpt gen_tac >> strip_tac >> REWRITE_TAC [body_stmt_ok_def] >>
  rpt strip_tac >>
  Cases_on `?a1 n1 a2 n2. it = Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))`
  >- (qpat_x_assum `?a1 n1 a2 n2. _`
        (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) >>
      drule_all body_for_range_lit >> simp[]) >>
  drule_all body_for_other >> simp[]
QED
