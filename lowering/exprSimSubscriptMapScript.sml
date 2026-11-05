(*
 * Expression simulation: compile_subscript_map_case, a case of exprSimPlaces on its
 * own so it can be proved apart (see the comment on the theorem).
 *)

Theory exprSimSubscriptMap
Ancestors
  exprSimSource exprSimHypsDefs list exprSimHyps exprSimPop exprSimAttribute exprSimTuple exprSimPopStorage exprSimPopNested
  exprSimArrayIndex
  exprLowering placeTypingProps vyperAST vyperTypeSystem vyperTypeCallGraph

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
