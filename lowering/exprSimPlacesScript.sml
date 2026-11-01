(*
 * Expression simulation: places (#636, Places)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for subscripts,
 * attributes and pop.  Proved: pop on a local (compile_pop_name_case, by
 * exprSimPop's compile_pop_name_sim, for the body simulation too),
 * attributes (exprSimAttribute's compile_attribute_vv_sim), tuple
 * subscripts (exprSimTuple's compile_subscript_tuple_sim), and subscripts
 * of a struct, which do not type.  Cheated, for the later #636 PRs: array
 * and mapping subscripts, a dispatch that disagrees with the base's type,
 * the tuple popped-clash case below, and pop on any other target, by kind
 * (compile_pop_storage_sim, compile_pop_immutable_sim,
 * compile_pop_nested_sim).
 *
 * TOP-LEVEL:
 *   compile_subscript_sim — static and dynamic arrays with the bounds-check
 *                           abort, hashmaps, tuples (#558), Places row 1:
 *                           by place_type of the base,
 *                           compile_subscript_map_sim for a mapping,
 *                           compile_subscript_mismatch_sim for a dispatch
 *                           type other than the base's,
 *                           compile_subscript_tuple_case_sim for a tuple,
 *                           compile_subscript_array_sim for an array
 *   compile_attribute_sim — struct fields (#558), row 2: by
 *                           compile_attribute_vv_sim
 *   compile_pop_sim       — pop on a dynamic array, with the empty-array
 *                           abort, row 3: compile_pop_name_sim for a local,
 *                           compile_pop_other_sim for the rest
 *
 * The induction hypothesis is expr_ok of every smaller expression, so of
 * the index and of the whole base chain; its expr_vv_ok describes a base's
 * value_vv, captured memory, storage and transient places included.  It
 * does not cover a hashmap base: that evaluates to a HashMapRef and is typed by
 * type_place_expr, not well_typed_expr.  The mapping lemma's proof needs a
 * place judgment for hashmap bases, proved by induction on the place chain
 * with this hypothesis for the indices.
 *
 * compile_subscript dispatches on place_type of the base, the base's own
 * type for a nested place, so nested subscripts are lowered at their
 * element type.  pop still falls back to a dynamic uint256 array in memory
 * when the target is not a Name.
 *)

Theory exprSimPlaces
Ancestors
  list exprSim exprSimHyps exprSimPop exprSimAttribute exprSimTuple
  exprSimArrayIndex
  exprLowering vyperAST vyperTypeSystem vyperTypeCallGraph

(* ===== Subscripts ===== *)

(* A subscript of a mapping (place_type MapPT).  Cheated: the base
   evaluates to a HashMapRef, which expr_vv_res_ok, and so the induction
   hypothesis, leaves out, and which well_typed_expr does not type
   (type_place_expr does).  The proof needs a place judgment for mapping
   bases, the operand holding the mapping's slot, proved by induction on the
   place chain with the hypothesis for the keys, and the slot computation:
   compile_mapping_subscript's SHA3 over the slot and key words stored in a
   64-byte buffer against hashmap_slot slot (encode_hashmap_key kt kv), with
   compile_keccak256_key for a bytes or string key. *)
Theorem compile_subscript_map_sim:
  !cenv ann obj idx kt vt.
    expr_sim_below cenv (expr_size (Subscript ann obj idx)) /\
    place_type cenv obj = MapPT kt vt ==>
    expr_vv_ok cenv (Subscript ann obj idx)
Proof
  cheat
QED

(* The compiler's dispatch type disagrees with the base's type: place_type
   says ValPT bt with bt not the base's expr_type.  Cheated: this is the
   case of a spurious ce_hashmap_info, a map base (place_type MapPT) whose
   value type disagrees with the subscript's annotation.  expr_sim_inv has
   no clause relating ce_hashmap_info to env's toplevel_vtypes and
   bare_globals (placeTypingProps's place_map_tables_agree covers
   toplevel_vtypes only), so the case is not excluded yet. *)
Theorem compile_subscript_mismatch_sim:
  !cenv ann obj idx bt.
    expr_sim_below cenv (expr_size (Subscript ann obj idx)) /\
    place_type cenv obj = ValPT bt /\ bt <> expr_type obj ==>
    expr_vv_ok cenv (Subscript ann obj idx)
Proof
  cheat
QED

(* The base evaluates to a local's place that memory no longer holds,
   whose popped history holds a snapshot exactly at the element
   (exprSimTuple's tuple_popped_clash).  Cheated, and false as stated, as
   the attribute case was before popped_keys_indexed: read_popped may read
   that snapshot rather than the element of the base's.  record_pop only
   records snapshots at dynamic-array elements, but expr_sim_inv's
   popped_keys_indexed says only that every popped key ends in an index,
   which a tuple element's path does as well (exprSimAttributeFields's
   popped_keys_indexed_not_at_field rules out the field case only). *)
Theorem compile_subscript_tuple_popped_clash_sim:
  !ctx func cenv cx env ty ann obj idx es.
    expr_vv_ok cenv obj /\
    expr_sim_pre cenv cx env (Subscript ann obj idx) es /\
    tuple_popped_clash cx obj idx es ==>
    expr_vv_sim ctx func cenv cx ty (Subscript ann obj idx) es
Proof
  cheat
QED

Theorem compile_subscript_tuple_case_sim:
  !cenv ann obj idx tys.
    expr_sim_below cenv (expr_size (Subscript ann obj idx)) /\
    expr_type obj = TupleT tys /\
    place_type cenv obj = ValPT (TupleT tys) ==>
    expr_vv_ok cenv (Subscript ann obj idx)
Proof
  rpt strip_tac >>
  `expr_vv_ok cenv obj` by
    (fs[expr_sim_below_def, expr_ok_def] >> first_x_assum irule >>
     simp[expr_size_def]) >>
  rw[expr_vv_ok_def] >>
  Cases_on `tuple_popped_clash cx obj idx es`
  >- (irule compile_subscript_tuple_popped_clash_sim >> metis_tac[]) >>
  drule_all compile_subscript_tuple_sim >> simp[] >> metis_tac[]
QED

(* A struct is not subscripted: subscript_type_ok is false of a struct,
   and a place-typed base is an array or a mapping. *)
Theorem subscript_struct_base_untyped[local]:
  !cenv cx env ann obj idx es sid.
    expr_sim_pre cenv cx env (Subscript ann obj idx) es ==>
    expr_type obj <> StructT sid
Proof
  rpt gen_tac >> simp[expr_sim_pre_def, Once well_typed_expr_def] >>
  rpt strip_tac >> gvs[subscript_type_ok_def] >>
  drule type_place_expr_vtype_annotation >>
  Cases_on `vt` >> TRY (rename1 `Type t` >> Cases_on `t`) >>
  gvs[subscript_vtype_def, vtype_annotation_ok_def]
QED

(* An element of a static or dynamic array, with the bounds-check abort.
   Cheated: compile_subscript lowers the index after the base, and the
   base's value_vv must still hold its value when the index's fragment
   ends.  Where the base points into a live local's region (x[i] for a
   local x), the index can change that local (x[x.pop()]), and expr_post
   then says only that the local holds its new value, at its region: the
   base's pointer is the local's place at a path, but vv_holds does not say
   so, so the element's value at the base's pointer does not follow.  The
   proof needs vv_holds to relate a pointer into a local's region to the
   place it reads (a place-pointer relation), or a fragment for the index
   that keeps the base's bytes (exprSimOperands keeps a base in the
   expression's own allocations only).  The bounds check itself, a source
   RuntimeError for an index out of range against compile_array_subscript's
   ASSERT, which aborts, is in expr_exit's allowance. *)
Theorem compile_subscript_array_sim:
  !cenv ann obj idx bt.
    expr_sim_below cenv (expr_size (Subscript ann obj idx)) /\
    place_type cenv obj = ValPT bt /\ bt = expr_type obj /\
    (!tys. bt <> TupleT tys) /\ (!sid. bt <> StructT sid) ==>
    expr_vv_ok cenv (Subscript ann obj idx)
Proof
  cheat
QED

Theorem compile_subscript_sim:
  !cenv ann obj idx.
    expr_sim_below cenv (expr_size (Subscript ann obj idx)) ==>
    expr_vv_ok cenv (Subscript ann obj idx)
Proof
  rpt strip_tac >> Cases_on `place_type cenv obj`
  >- (irule compile_subscript_map_sim >> metis_tac[]) >>
  rename1 `ValPT bt` >>
  Cases_on `bt <> expr_type obj`
  >- (irule compile_subscript_mismatch_sim >> metis_tac[]) >>
  gvs[] >>
  Cases_on `?tys. expr_type obj = TupleT tys`
  >- (gvs[] >> irule compile_subscript_tuple_case_sim >> simp[]) >>
  Cases_on `?sid. expr_type obj = StructT sid`
  >- (gvs[] >> rw[expr_vv_ok_def] >>
      metis_tac[subscript_struct_base_untyped]) >>
  irule compile_subscript_array_sim >> gvs[] >> metis_tac[]
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

(* pop on a module variable in storage or transient storage.  Cheated:
   the source reads the popped element from its slots (read_storage_slot),
   which raises a RuntimeError where the slots do not decode, while the
   lowering never reads it and hands out the slot; expr_sim_inv's storage
   clauses keep the slots decoding (as in exprSimLeaves's
   compile_toplevel_storage_undecodable_sim), but the proof also needs
   expr_sim_inv to give ce_var_type of the module variable's key, from
   which the lowering reads the element type.
   It also breaks expr_post's frame on the live locals (locals_kept): the
   lowering MSTOREs at the slot's fixed memory address, where an allocation
   holding a local can sit (allocation starts at 0). *)
Theorem compile_pop_storage_sim:
  !cenv ann src id ctx func cx env ty es ts d.
    expr_sim_below cenv (expr_size (Pop ann (TopLevelNameTarget (src,id)))) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    expr_sim_pre cenv cx env (Pop ann (TopLevelNameTarget (src,id))) es ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann (TopLevelNameTarget (src,id))) es
Proof
  cheat
QED

(* pop on an immutable, in the constructor.  Cheated: the lowering pops at
   LocCode with MLOAD and MSTORE at the immutable's data offset, which is
   not where immutables_rel keeps it, and that offset can hold a live
   local's allocation (locals_kept). *)
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

(* pop on a nested target (x.a.pop(), x[i].pop()).  Cheated: the lowering
   falls back to a uint256 array in memory at the base's operand when the
   target is not a name (this file's header), and MSTOREs at the base's
   first word, which for x.a.pop() is a live local's (locals_kept). *)
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
