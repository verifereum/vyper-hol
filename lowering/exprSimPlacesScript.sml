(*
 * Expression simulation: places (#636, Places)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for subscripts,
 * attributes and pop.  Proved: pop on a local (compile_pop_name_case, by
 * exprSimPop's compile_pop_name_sim, for the body simulation too),
 * attributes (exprSimAttribute's compile_attribute_vv_sim), tuple
 * subscripts (exprSimTuple's compile_subscript_tuple_sim), a dispatch that
 * disagrees with the base's type and subscripts of any base but an array, a
 * tuple or a mapping, which do not type.  Array and mapping subscripts
 * are compile_subscript_array_case (exprSimSubscriptArray) and
 * compile_subscript_map_case (exprSimSubscriptMap).  Pop on a storage variable is
 * compile_pop_storage_sim; pop on a nested target is compile_pop_nested_sim,
 * by exprSimPopNested's pop_nested_sim, whose residuals are listed there.
 * Root immutable pop is rejected by the source checker, as in Python.
 *
 * TOP-LEVEL:
 *   compile_subscript_case — static and dynamic arrays with the
 *                           bounds-check abort, hashmaps, tuples (#558),
 *                           Places row 1, over expr_vv_case: by place_type
 *                           of the base, compile_subscript_map_case for a
 *                           mapping, compile_subscript_mismatch_case for a
 *                           dispatch type other than the base's,
 *                           compile_subscript_tuple_sim for a tuple,
 *                           compile_subscript_array_case for an array
 *   compile_subscript_sim — compile_subscript_case with nocalls = T
 *   compile_attribute_sim — struct fields (#558), row 2: by
 *                           compile_attribute_vv_sim
 *   compile_pop_sim       — pop on a dynamic array, with the empty-array
 *                           abort, row 3: compile_pop_name_sim for a local,
 *                           compile_pop_other_sim for the rest
 *
 * The case lemmas take the base's expr_vv_case and the index's
 * expr_sim_case; expr_vv_case describes a base's value_vv, captured memory,
 * storage and transient places included.  It does not cover a hashmap
 * base: that evaluates to a HashMapRef and is typed by type_place_expr, not
 * well_typed_expr.  A mapping base is judged by expr_map_case
 * (exprSimMapDefs) instead, which compile_subscript_case takes for a
 * MapPT base and compile_subscript_sim supplies via expr_map_case_below.
 *
 * compile_subscript dispatches on place_type of the base, the base's own
 * type for a nested place, and pop takes its target's place from
 * compile_get_target_ptr, so nested subscripts and pops are lowered at
 * their element type.  (compile_attribute finds the struct from the base's
 * type.)
 *)

Theory exprSimPlaces
Ancestors
  exprSimSubscriptMap exprSimSubscriptArray exprSimPopNestedTargetFrag
  exprSimSource exprSimHypsDefs list exprSimHyps exprSimPop exprSimAttribute exprSimTuple exprSimPopStorage exprSimPopNested
  exprSimArrayIndex targetPlaceSim targetPlaceSimCases exprSimPopNestedBase
  exprLowering placeTypingProps vyperAST vyperTypeSystem vyperTypeCallGraph

(* ===== Subscripts ===== *)

(* The case lemmas take the judgments a shared case lemma takes
   (expr_vv_case, expr_sim_case: exprSimHyps), so the body simulation's
   body_subscript_case (bodySimExprCases), where an operand may call an
   internal function, uses them with nocalls = F, as compile_subscript_sim
   does with T. *)

(* The compiler's dispatch type disagrees with the base's type: place_type
   says ValPT bt with bt not the base's expr_type.  Unreachable: under
   expr_sim_inv's map table clauses a well-typed base's place_type is its
   own type, and a place-typed base's is that of its vtype. *)
Theorem compile_subscript_mismatch_case:
  !nocalls ctx func cenv cx ann obj idx bt.
    place_type cenv obj = ValPT bt /\ bt <> expr_type obj ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  rw[expr_vv_case_def, expr_body_pre_def, expr_sim_inv_def] >>
  gvs[Once well_typed_expr_def]
  >- (drule_all place_type_well_typed_on_defined >> simp[]) >>
  drule_all place_type_checked_place_on_defined >> strip_tac >>
  drule type_place_expr_vtype_annotation >>
  Cases_on `vt` >> gvs[value_type_place_def, vtype_annotation_ok_def]
QED

(* A subscript's base whose dispatch type is its own is an array or a
   tuple: subscript_type_ok is false of every other type, and a place-typed
   base whose place_type is ValPT has a value vtype, which subscript_vtype
   indexes only for an array. *)
Theorem subscript_base_array_or_tuple[local]:
  !cenv cx env ann obj idx es.
    expr_body_pre cenv cx env (Subscript ann obj idx) es /\
    place_type cenv obj = ValPT (expr_type obj) ==>
    (?et bd. expr_type obj = ArrayT et bd) \/ (?tys. expr_type obj = TupleT tys)
Proof
  rpt gen_tac >> simp[expr_body_pre_def, expr_sim_inv_def] >>
  simp[Once well_typed_expr_def] >> rpt strip_tac
  >- (Cases_on `expr_type obj` >> gvs[subscript_type_ok_def]) >>
  drule_all place_type_checked_place_on_defined >> strip_tac >>
  Cases_on `vt` >> gvs[value_type_place_def] >>
  Cases_on `expr_type obj` >> gvs[subscript_vtype_def]
QED

(* By place_type of the base: compile_subscript_map_case for a mapping,
   compile_subscript_mismatch_case for a dispatch type other than the
   base's, exprSimTuple's compile_subscript_tuple_sim for a tuple and
   compile_subscript_array_case for an array; no other base types. *)
Theorem compile_subscript_case:
  !nocalls ctx func cenv cx ann obj idx.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!kt vt. place_type cenv obj = MapPT kt vt ==>
             expr_map_case nocalls ctx func cenv cx obj) /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  rpt strip_tac >> Cases_on `place_type cenv obj`
  >- metis_tac[compile_subscript_map_case] >>
  rename1 `ValPT bt` >>
  Cases_on `bt <> expr_type obj`
  >- (irule compile_subscript_mismatch_case >> qexists_tac `bt` >> simp[]) >>
  gvs[] >> simp[expr_vv_case_def] >> rpt gen_tac >> strip_tac >>
  drule_all subscript_base_array_or_tuple >> strip_tac
  >- (`expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)` by
        metis_tac[compile_subscript_array_case] >>
      qpat_x_assum `expr_vv_case _ _ _ _ _ (Subscript _ _ _)` mp_tac >>
      simp[expr_vv_case_def] >>
      disch_then (qspecl_then [`env`, `ty`, `es`] mp_tac) >> fs[]) >>
  `expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)` by
    (irule compile_subscript_tuple_sim >> gvs[]) >>
  qpat_x_assum `expr_vv_case _ _ _ _ _ (Subscript _ _ _)` mp_tac >>
  simp[expr_vv_case_def] >>
  disch_then (qspecl_then [`env`, `ty`, `es`] mp_tac) >> fs[]
QED

Theorem compile_subscript_sim:
  !cenv ann obj idx.
    expr_sim_below cenv (expr_size (Subscript ann obj idx)) ==>
    expr_vv_ok cenv (Subscript ann obj idx)
Proof
  rpt strip_tac >>
  `expr_ok cenv obj /\ expr_ok cenv idx` by
    (fs[expr_sim_below_def] >> rpt strip_tac >> first_x_assum irule >>
     simp[expr_size_def]) >>
  `expr_sim_below cenv (expr_size obj)` by
    (irule expr_sim_below_mono >>
     qexists_tac `expr_size (Subscript ann obj idx)` >> simp[expr_size_def]) >>
  gvs[expr_ok_case, expr_vv_ok_case] >> rpt gen_tac >>
  irule compile_subscript_case >> simp[expr_map_case_below]
QED

(* ===== Attributes ===== *)

Theorem compile_attribute_sim:
  !cenv ann obj fld.
    expr_sim_below cenv (expr_size (Attribute ann obj fld)) ==>
    expr_vv_ok cenv (Attribute ann obj fld)
Proof
  rpt strip_tac >>
  `expr_vv_ok cenv obj` by
    (fs[expr_sim_below_def, expr_ok_def] >> first_x_assum irule >>
     simp[expr_size_def]) >>
  rw[expr_vv_ok_def] >>
  drule_all compile_attribute_vv_sim >> simp[] >> metis_tac[]
QED

(* pop on a local: exprSimPop's compile_pop_name_sim.  Its target has no
   operand that can call, so expr_body_pre is expr_sim_pre here. *)
Theorem compile_pop_name_case:
  !nocalls ctx func cenv cx ann id.
    expr_sim_case nocalls ctx func cenv cx (Pop ann (NameTarget id)) /\
    expr_vv_case nocalls ctx func cenv cx (Pop ann (NameTarget id))
Proof
  rpt gen_tac >>
  `expr_vv_case nocalls ctx func cenv cx (Pop ann (NameTarget id))` by
    (rw[expr_vv_case_def] >> irule compile_pop_name_sim >>
     gvs[expr_sim_pre_body, int_calls_expr_def] >> metis_tac[]) >>
  simp[expr_sim_case_of_vv]
QED

(* pop on a module variable in storage or transient storage.  The target's
   pointer is the variable's slot (compile_get_target_ptr_toplevel, from
   storage_vars_rel and expr_sim_inv's module variable clause), and
   compile_dynarray_pop loads the length with SLOAD (TLOAD), aborts on zero
   as the source's check raises, stores the length less one, and hands out
   the last element's slot, as pop_place does.  The element is past the new
   length, so its slots are dead in the array: storage_holds asks for the
   element's slots to agree with Venom's (storage_range_agree), which holds
   before the pop by storage_rel (the element is live) and after it since
   only the header slot changed (dead_bytes_frame).  stmt_state_rel after
   the header write: the dead set only grows as the length shrinks, which
   is what accounts_rel_sstore and accounts_rel_tstore take. *)
Theorem compile_pop_storage_sim:
  !cenv ann src id ctx func cx env ty es ts d.
    expr_sim_below cenv (expr_size (Pop ann (TopLevelNameTarget (src,id)))) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    expr_sim_pre cenv cx env (Pop ann (TopLevelNameTarget (src,id))) es ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann (TopLevelNameTarget (src,id))) es
Proof
  rpt strip_tac >>
  `well_typed_expr env (Pop ann (TopLevelNameTarget (src,id))) /\
   env_consistent env cx es` by fs[expr_sim_pre_def, expr_sim_inv_def] >>
  drule_all pop_storage_target_facts >> strip_tac >> gvs[] >>
  irule compile_pop_storage_normalized_sim >> metis_tac[]
QED

(* Python requires an immutable's constructor assignment and rejects a second
   modification, including root pop. The checker therefore excludes bare
   globals here; a typed module target must have a storage declaration. *)
Theorem compile_pop_immutable_sim:
  !cenv ann src id ctx func cx env ty es.
    expr_sim_below cenv (expr_size (Pop ann (TopLevelNameTarget (src,id)))) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) /\
    expr_sim_pre cenv cx env (Pop ann (TopLevelNameTarget (src,id))) es ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann (TopLevelNameTarget (src,id))) es
Proof
  rpt strip_tac >>
  fs[expr_sim_pre_def, expr_sim_inv_def,
     vyperTypeInvariantsTheory.env_consistent_def,
     vyperTypeInvariantsTheory.env_context_consistent_def,
     Once well_typed_expr_def,
     vyperTypeEnvTheory.type_place_target_TopLevelNameTarget] >>
  Cases_on `FLOOKUP env.bare_global_assignable (src,id)` >> gvs[] >>
  qpat_x_assum
    `!src id ty. FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\
                 FLOOKUP env.bare_globals (src,id) = NONE ==> _`
    (qspecl_then [`src`, `id`, `ArrayT ann (Dynamic n)`] mp_tac) >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!ts. get_module_code cx src = SOME ts ==> _`
    (qspec_then `ts` mp_tac) >> simp[]
QED

(* pop on a nested target (x.a.pop(), x[i].pop(), self.s.a.pop()):
   exprSimPopNested's pop_nested_sim, by the target's root, with the
   target's fragment judgment from pop_nested_expr_target_frag and, for an
   immutable root in the constructor, the compile-env premises from
   pop_nested_immutable_root_ctor. *)
Theorem compile_pop_nested_sim:
  !cenv ann tgt.
    (!id. tgt <> NameTarget id) /\ (!nid. tgt <> TopLevelNameTarget nid) /\
    expr_sim_below cenv (expr_size (Pop ann tgt)) ==>
    expr_vv_ok cenv (Pop ann tgt)
Proof
  rewrite_tac[expr_vv_ok_def] >> rpt strip_tac >>
  irule pop_nested_sim >> conj_tac
  >- (strip_tac >> qexists_tac `T` >>
      `int_calls_target tgt = []` by
        gvs[expr_sim_pre_def, int_calls_expr_def] >>
      simp[] >> irule target_idx_case_ok >> rw[] >>
      fs[expr_sim_below_def] >> first_x_assum irule >>
      drule nested_pop_index_size >> simp[expr_size_def]) >>
  qexists_tac `env` >> rpt conj_tac
  >~ [`pop_target_frag`] >- metis_tac[pop_nested_expr_target_frag]
  >~ [`cenv.ce_is_ctor`]
  >- (strip_tac >> gvs[immutable_root_def, expr_sim_pre_body, expr_body_pre_def] >>
      drule_all pop_nested_immutable_root_ctor >> simp[]) >>
  gvs[expr_sim_pre_body]
QED

(* pop on a target other than a local: compile_pop_storage_sim,
   compile_pop_immutable_sim and compile_pop_nested_sim, by kind. *)
Theorem compile_pop_other_sim:
  !cenv ann tgt.
    (!id. tgt <> NameTarget id) /\ expr_sim_below cenv (expr_size (Pop ann tgt)) ==>
    expr_vv_ok cenv (Pop ann tgt)
Proof
  rpt strip_tac >> Cases_on `?src id. tgt = TopLevelNameTarget (src,id)`
  >- (qpat_x_assum `?src id. _` strip_assume_tac >>
      rpt BasicProvers.VAR_EQ_TAC >> simp[expr_vv_ok_def] >> rpt strip_tac >>
      Cases_on `?ts d. get_module_code cx src = SOME ts /\
                       find_var_decl_by_name id ts = SOME d`
      >- (irule compile_pop_storage_sim >> metis_tac[]) >>
      irule compile_pop_immutable_sim >> rpt conj_tac
      >- (rpt strip_tac >> Cases_on `find_var_decl_by_name id ts` >>
          metis_tac[]) >>
      metis_tac[]) >>
  irule compile_pop_nested_sim >> rw[] >> Cases_on `nid` >> gvs[]
QED

Theorem compile_pop_sim:
  !cenv ann tgt.
    expr_sim_below cenv (expr_size (Pop ann tgt)) ==>
    expr_vv_ok cenv (Pop ann tgt)
Proof
  rpt strip_tac >> Cases_on `?id. tgt = NameTarget id`
  >- (gvs[] >> rw[expr_vv_ok_def] >> irule compile_pop_name_sim >>
      metis_tac[]) >>
  irule compile_pop_other_sim >> gvs[]
QED
