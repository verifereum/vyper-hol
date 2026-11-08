(*
 * Statement simulation: a tuple assigned to places (#637, #851)
 *
 * (t1, ..., tn) = e where each ti is a base target of a value type that is
 * not inside an immutable: a local or a field or element of one, a storage
 * or transient variable or a field or element of one, or a mapping's
 * value.  The source evaluates e and reads its tuple value, then for each
 * ti in order evaluates its place and writes the element there
 * (assign_tuple_targets).  The lowering, in the same order, evaluates e,
 * loads every element (from a staged copy when e is a memory view with an
 * aggregate element), then for each ti computes its pointer
 * (compile_get_target_ptr, simulated by targetPlaceSim's target_sim) and
 * stores the element there (placeStore).  The elements are loaded at the
 * RHS's lowered type (an internal call's declared return type, which the
 * call site may annotate with a wider type), and each store converts from
 * that layout to its target's.
 *
 * TOP-LEVEL:
 *   compile_assign_tuple_places_stmt_frag — the statement for every outcome
 *)

Theory stmtSimAssignTuplePlaces
Ancestors
  supportedTargets placeStore targetPlaceSimCases targetPlaceSim targetPlaceSimDefs
  stmtSimDefs exprSimHypsDefs exprSimDefs loweringPosts
  stmtLowering exprLowering compileEnv
  vyperInterpreter vyperState vyperTypeSystem
  list

Theorem compile_assign_tuple_places_stmt_frag:
  !ctx func cx lctx RetQ cenv ty env tops gs e es tys tvs ltys ltvs.
    expr_type e = TupleT tys /\ gs <> [] /\
    LIST_REL (\g t. well_typed_atarget env g t) gs tys /\
    assignable_type (get_tenv cx) (TupleT tys) /\
    lowered_value_type cenv e = TupleT ltys /\ arg_types_fit ltys tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
    (EXISTS (\t. ~is_word_type t) ltys ==> cenv.ce_target CapMcopy) /\
    (is_memory_view e /\ EXISTS (\t. ~is_word_type t) ltys ==>
      type_memory_size (TupleTV ltvs) < dimword (:256)) /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
      type_memory_size (EL i tvs) + 64 < dimword (:256) /\
      type_memory_size (EL i ltvs) + 64 < dimword (:256)) /\
    EVERY (\g. ?bt. g = BaseTarget bt /\ supported_target_pure tops bt /\
                    target_case F ctx func cenv cx bt /\
                    ~immutable_root cx bt /\ target_indices_pre cenv cx env bt)
      gs /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    expr_sim_inv cenv cx env es /\
    expr_body_pre cenv cx env e es /\
    expr_sim ctx func cenv cx (TupleT tys) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED
