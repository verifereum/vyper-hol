(*
 * Expression simulation: places (#636, Places)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for subscripts,
 * attributes and pop.  Proved: pop on a local (exprSimPop's
 * compile_pop_name_sim) and attributes of a base not in code
 * (exprSimAttribute's compile_attribute_loc_sim).  Cheated, for the later
 * #636 PRs: subscripts, pop on any other target (compile_pop_other_sim),
 * and the two attribute cases below.
 *
 * TOP-LEVEL:
 *   compile_subscript_sim — static and dynamic arrays with the bounds-check
 *                           abort, hashmaps, tuples (#558), Places row 1
 *   compile_attribute_sim — struct fields (#558), row 2: by
 *                           compile_attribute_loc_sim, but for
 *                           compile_attribute_code_sim and
 *                           compile_attribute_popped_clash_sim
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

Theorem compile_subscript_sim:
  !cenv ann base idx.
    expr_sim_below cenv (expr_size (Subscript ann base idx)) ==>
    expr_vv_ok cenv (Subscript ann base idx)
Proof
  cheat
QED

(* An attribute of a base in code: an immutable, or a field of one.
   Cheated, and false as stated: the lowering hands out the base's code
   pointer plus the field's offset, while immutable_holds asks a code
   pointer to be an immutable's own data offset (ImmutableLoc), as for
   exprSimLeaves's compile_toplevel_immutable_sim. *)
Theorem compile_attribute_code_sim:
  !cenv ann obj fld.
    expr_sim_below cenv (expr_size (Attribute ann obj fld)) /\
    (?ty st. vv_location (FST (compile_expr cenv ty obj st)) =
             SOME LocCode) ==>
    expr_vv_ok cenv (Attribute ann obj fld)
Proof
  cheat
QED

(* The base evaluates to a local's place that memory no longer holds (a
   popped element), whose popped history holds a snapshot exactly at the
   field (exprSimAttribute's attr_popped_clash).  Cheated, and false as
   stated: read_popped reads the newest matching snapshot, so where that
   snapshot is newer than the one the base reads, it reads that snapshot's
   value while memory at the field's pointer holds the base's field.
   record_pop only records snapshots at array elements, so the case never
   arises, but expr_sim_inv has no clause saying so. *)
Theorem compile_attribute_popped_clash_sim:
  !ctx func cenv cx env ty ann obj fld es.
    expr_vv_ok cenv obj /\
    expr_sim_pre cenv cx env (Attribute ann obj fld) es /\
    attr_popped_clash cx obj fld es ==>
    expr_vv_sim ctx func cenv cx ty (Attribute ann obj fld) es
Proof
  cheat
QED

Theorem compile_attribute_sim:
  !cenv ann obj fld.
    expr_sim_below cenv (expr_size (Attribute ann obj fld)) ==>
    expr_vv_ok cenv (Attribute ann obj fld)
Proof
  rpt strip_tac >>
  Cases_on `!ty st. vv_location (FST (compile_expr cenv ty obj st)) <>
                    SOME LocCode`
  >- (`expr_vv_ok cenv obj` by
        (fs[expr_sim_below_def, expr_ok_def] >> first_x_assum irule >>
         simp[expr_size_def]) >>
      rw[expr_vv_ok_def] >>
      Cases_on `attr_popped_clash cx obj fld es`
      >- (irule compile_attribute_popped_clash_sim >> metis_tac[]) >>
      drule_all compile_attribute_loc_sim >> simp[] >> metis_tac[]) >>
  irule compile_attribute_code_sim >> gvs[] >> metis_tac[]
QED

(* pop on a target other than a local.  Cheated:
   - a module variable (TopLevelNameTarget) in storage or transient
     storage: the source reads the popped element from its slots
     (read_storage_slot), which raises a RuntimeError where the slots do not
     decode, while the lowering never reads it and hands out the slot, so
     this is false as stated until a storage invariant keeps slots
     decodable (as for exprSimLeaves's
     compile_toplevel_storage_undecodable_sim).  Where they decode, the
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
