(*
 * Expression simulation: compile_subscript_map_case, a case of exprSimPlaces on its
 * own so it can be proved apart (see the comment on the theorem).
 *)

Theory exprSimSubscriptMap
Ancestors
  exprSimMapDefs exprSimSource exprSimHypsDefs list exprSimHyps exprSimPop exprSimAttribute exprSimTuple exprSimPopStorage exprSimPopNested
  exprSimArrayIndex
  exprLowering placeTypingProps vyperAST vyperTypeSystem vyperTypeCallGraph

(* A top-level mapping variable: compile_expr lowers it to a pointer
   literal holding the mapping's declared slot (env_consistent's hashmap
   clause, lookup_global_mapping_region), and the source lookup returns the
   HashMapRef at that slot. *)
Theorem compile_toplevel_map_case:
  !nocalls ctx func cenv cx ty id.
    expr_map_case nocalls ctx func cenv cx (TopLevelName ty id)
Proof
  cheat
QED

(* A mapping that is a value of a mapping (m[a] for m : HashMap[K,
   HashMap[...]]): the base's slot, the key lowered after it, and
   compile_mapping_subscript's SHA3 over the two (in a fresh 64-byte
   buffer) against hashmap_slot slot (encode_hashmap_key kt kv), with
   compile_keccak256_key for a bytes or string key. *)
Theorem compile_subscript_map_map_case:
  !nocalls ctx func cenv cx ann obj idx.
    expr_map_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) ==>
    expr_map_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

(* With every smaller expression simulating, an expression naming a
   mapping simulates: its keys are smaller. *)
Theorem expr_map_case_below:
  !obj cenv ctx func cx.
    expr_sim_below cenv (expr_size obj) ==>
    expr_map_case T ctx func cenv cx obj
Proof
  measureInduct_on `expr_size obj` >> rpt strip_tac >>
  Cases_on `obj`
  >~ [`TopLevelName`] >- simp[compile_toplevel_map_case]
  >~ [`Subscript _ _ _`]
  >- (rename1 `Subscript ann obj0 idx` >>
      irule compile_subscript_map_map_case >> conj_tac
      >- (rpt strip_tac >>
          `expr_ok cenv idx` by
            (fs[expr_sim_below_def] >> first_x_assum irule >>
             simp[expr_size_def]) >>
          gvs[expr_ok_case]) >>
      first_x_assum irule >> simp[expr_size_def] >>
      irule expr_sim_below_mono >>
      qexists_tac `expr_size (Subscript ann obj0 idx)` >>
      simp[expr_size_def]) >>
  irule expr_map_case_other >> simp[]
QED

(* A subscript of a mapping (place_type MapPT) whose value is not a
   mapping: the base's expr_map_case gives the operand holding the
   mapping's slot, the key is lowered after it, and the slot computation
   is compile_subscript_map_map_case's.  expr_sim_inv's map table clauses
   make MapPT mean a declared mapping.  For a storage or transient leaf,
   storage_holds also asks that the leaf's slots are in range
   (slots_in_range); the proof gets that from static_/dyn_slots_in_range
   and the hashmap regions of contract_storage_well_formed, as
   toplevel_storage_slots_in_range and storage_field_slots_in_range do for
   names and struct fields. *)
Theorem compile_subscript_map_case:
  !nocalls ctx func cenv cx ann obj idx kt vt.
    expr_map_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    place_type cenv obj = MapPT kt vt ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED
