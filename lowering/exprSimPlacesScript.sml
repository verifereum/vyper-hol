(*
 * Expression simulation: places (#636, Places)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for subscripts,
 * attributes and pop.  Proved: pop on a local (exprSimPop's
 * compile_pop_name_sim) and attributes (exprSimAttribute's
 * compile_attribute_vv_sim).  Cheated, for the later #636 PRs: subscripts
 * and pop on any other target (compile_pop_other_sim).
 *
 * TOP-LEVEL:
 *   compile_subscript_sim — static and dynamic arrays with the bounds-check
 *                           abort, hashmaps, tuples (#558), Places row 1
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
 * type_place_expr, not well_typed_expr.  The subscript lemma's proof needs a
 * place judgment for hashmap bases, proved by induction on the place chain
 * with this hypothesis for the indices.
 *
 * The lowering also needs fixing first for nested places: compile_subscript
 * and pop fall back to a dynamic uint256 array in memory when the base or
 * target is not a Name.  (compile_attribute finds the struct from the
 * base's type, so attributes of nested places are lowered right.)
 *)

Theory exprSimPlaces
Ancestors
  list exprSim exprSimHyps exprSimPop exprSimAttribute vyperAST

(* Cheated.  For a storage or transient subscript, storage_holds also asks
   that the element's or hashmap leaf's slots are in range (slots_in_range);
   the proof gets that from static_/dyn_slots_in_range and the hashmap
   regions of contract_storage_well_formed, as toplevel_storage_slots_in_range
   and storage_field_slots_in_range do for names and struct fields. *)
Theorem compile_subscript_sim:
  !cenv ann base idx.
    expr_sim_below cenv (expr_size (Subscript ann base idx)) ==>
    expr_vv_ok cenv (Subscript ann base idx)
Proof
  cheat
QED

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

(* pop on a target other than a local.  Cheated:
   - a module variable (TopLevelNameTarget) in storage or transient
     storage: the source reads the popped element from its slots
     (read_storage_slot), which raises a RuntimeError where the slots do not
     decode, while the lowering never reads it and hands out the slot;
     expr_sim_inv's storage clauses keep the slots decoding (as in
     exprSimLeaves's compile_toplevel_storage_undecodable_sim), but the
     proof also needs expr_sim_inv to give ce_var_type of the module
     variable's key, from which the lowering reads the element type;
   - an immutable in the constructor: the lowering pops at LocCode with
     MLOAD and MSTORE at the immutable's data offset, which is not where
     immutables_rel keeps it;
   - a nested target (x.a.pop(), x[i].pop()): the lowering falls back to a
     uint256 array in memory at the base's operand when the target is not a
     name (exprSimPlaces's header).
   Each of these also breaks expr_post's frame on the live locals
   (locals_kept): the lowering MSTOREs at the base's first word, which for
   x.a.pop() is a live local's, and for a module variable or an immutable is
   the fixed memory address slot or offset, where an allocation holding a
   local can sit (allocation starts at 0). *)
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
  rpt strip_tac >> Cases_on `?id. tgt = NameTarget id`
  >- (gvs[] >> rw[expr_vv_ok_def] >> irule compile_pop_name_sim >>
      metis_tac[]) >>
  irule compile_pop_other_sim >> gvs[]
QED
