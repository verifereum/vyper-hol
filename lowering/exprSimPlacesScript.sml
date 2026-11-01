(*
 * Expression simulation: places (#636, Places)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for subscripts,
 * attributes and pop.  Proved: pop on a local (compile_pop_name_case, by
 * exprSimPop's compile_pop_name_sim, for the body simulation too),
 * attributes (exprSimAttribute's compile_attribute_vv_sim), tuple
 * subscripts (exprSimTuple's compile_subscript_tuple_sim), a dispatch that
 * disagrees with the base's type and subscripts of any base but an array, a
 * tuple or a mapping, which do not type.  Cheated, for the later #636 PRs:
 * array and mapping subscripts and pop on any other target, by kind
 * (compile_pop_storage_sim, compile_pop_immutable_sim,
 * compile_pop_nested_sim).
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
 * well_typed_expr, so for a nested mapping (m[a][b]) nothing judges the
 * inner key a.  The mapping lemma's proof needs expr_vv_case to describe a
 * HashMapRef result (the operand holding the mapping's slot), which then
 * carries the inner keys' simulation to the outer subscript.
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
  exprLowering placeTypingProps vyperAST vyperTypeSystem vyperTypeCallGraph

(* ===== Subscripts ===== *)

(* The case lemmas take the judgments a shared case lemma takes
   (expr_vv_case, expr_sim_case: exprSimHyps), so the body simulation's
   body_subscript_case (bodySimExprCases), where an operand may call an
   internal function, uses them with nocalls = F, as compile_subscript_sim
   does with T. *)

(* A subscript of a mapping (place_type MapPT).  Cheated: the base
   evaluates to a HashMapRef, which expr_vv_res_ok, and so the base's
   judgment, leaves out, and which well_typed_expr does not type
   (type_place_expr does), so for a nested mapping the hypotheses say
   nothing of the inner keys.  The proof needs expr_vv_case to describe a
   HashMapRef result, the operand holding the mapping's slot (see the
   header), and the slot computation:
   compile_mapping_subscript's SHA3 over the slot and key words stored in a
   64-byte buffer against hashmap_slot slot (encode_hashmap_key kt kv), with
   compile_keccak256_key for a bytes or string key.  expr_sim_inv's map
   table clauses make MapPT mean a declared mapping.  For a storage or
   transient subscript, here and in compile_subscript_array_case,
   storage_holds also asks that the element's or hashmap leaf's slots are in
   range (slots_in_range); the proof gets that from static_/dyn_slots_in_range
   and the hashmap regions of contract_storage_well_formed, as
   toplevel_storage_slots_in_range and storage_field_slots_in_range do for
   names and struct fields. *)
Theorem compile_subscript_map_case:
  !nocalls ctx func cenv cx ann obj idx kt vt.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    place_type cenv obj = MapPT kt vt ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

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
   ASSERT, which aborts, is in expr_exit's allowance (exprSimArrayIndex).
   A dynamic array in code (an immutable, LocCode) reads its length with
   compile_ptr_load's compile_imm_load_word (ILOAD or DLOAD), for which
   exprSimArrayIndex has no array_len_ok lemma yet. *)
Theorem compile_subscript_array_case:
  !nocalls ctx func cenv cx ann obj idx et bd.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
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
  gvs[expr_ok_case, expr_vv_ok_case] >> rpt gen_tac >>
  irule compile_subscript_case >> simp[]
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
