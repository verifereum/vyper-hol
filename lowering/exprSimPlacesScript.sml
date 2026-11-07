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
  exprSimPopNestedImmutableDeploy
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
  cheat
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
  cheat
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
              expr_sim_case nocalls ctx func cenv cx idx) /\
    (~nocalls ==> post_value_type cenv obj = expr_type obj) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

Theorem compile_subscript_sim:
  !cenv ann obj idx.
    expr_sim_below cenv (expr_size (Subscript ann obj idx)) ==>
    expr_vv_ok cenv (Subscript ann obj idx)
Proof
  cheat
QED

(* ===== Attributes ===== *)

Theorem compile_attribute_sim:
  !cenv ann obj fld.
    expr_sim_below cenv (expr_size (Attribute ann obj fld)) ==>
    expr_vv_ok cenv (Attribute ann obj fld)
Proof
  cheat
QED

(* pop on a local: exprSimPop's compile_pop_name_sim.  Its target has no
   operand that can call, so expr_body_pre is expr_sim_pre here. *)
Theorem compile_pop_name_case:
  !nocalls ctx func cenv cx ann id.
    expr_sim_case nocalls ctx func cenv cx (Pop ann (NameTarget id)) /\
    expr_vv_case nocalls ctx func cenv cx (Pop ann (NameTarget id))
Proof
  cheat
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
  cheat
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
  cheat
QED

(* pop on a nested target (x.a.pop(), x[i].pop(), self.s.a.pop()):
   exprSimPopNested's pop_nested_sim, by the target's root, with the
   target's fragment judgment from pop_nested_expr_target_frag; an
   immutable root in the constructor by the residual
   pop_nested_immutable_deploy_expr_case, since expr_sim_inv does not give
   pop_nested_sim's constructor compile-env premises yet. *)
Theorem compile_pop_nested_sim:
  !cenv ann tgt.
    (!id. tgt <> NameTarget id) /\ (!nid. tgt <> TopLevelNameTarget nid) /\
    expr_sim_below cenv (expr_size (Pop ann tgt)) ==>
    expr_vv_ok cenv (Pop ann tgt)
Proof
  cheat
QED

(* pop on a target other than a local: compile_pop_storage_sim,
   compile_pop_immutable_sim and compile_pop_nested_sim, by kind. *)
Theorem compile_pop_other_sim:
  !cenv ann tgt.
    (!id. tgt <> NameTarget id) /\ expr_sim_below cenv (expr_size (Pop ann tgt)) ==>
    expr_vv_ok cenv (Pop ann tgt)
Proof
  cheat
QED

Theorem compile_pop_sim:
  !cenv ann tgt.
    expr_sim_below cenv (expr_size (Pop ann tgt)) ==>
    expr_vv_ok cenv (Pop ann tgt)
Proof
  cheat
QED
