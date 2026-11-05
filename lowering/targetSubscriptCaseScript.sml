(*
 * The target/place judgment for an element of an array or a mapping
 * (target_subscript_case), on its own so it can be proved apart from the
 * other steps (targetPlaceSimCasesBase).
 *)

Theory targetSubscriptCase
Ancestors
  targetPlaceSimCasesBase targetPlaceLive
  exprSimFieldLayout
  exprSimSource
  targetPlaceSimDefs
  stmtSimProps
  exprSimProps
  exprSimHypsDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pair
  fragExec  exprSimHyps exprSimBuffer exprSimAttributeFields
  freshWrites stmtLoweringMono targetPlaceSim
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv
  valueEncoding vyperAST vyperInterpreter vyperState vyperValue
  vyperTypeSystem vyperTypeCallGraph vyperTypeEnv vyperTypeInvariants
  vyperTypeExprSoundness vyperPlaceFrames vyperEvalMisc
  venomState venomInst
Libs
  pairLib

(* An element of an array or a mapping: the base's fragment, the index's
   (lower_value), then, by the base's place type, the slot of the key
   (compile_mapping_subscript, with compile_keccak256_key for a bytes or
   string key) or the bounds check and the element's pointer
   (compile_array_subscript).  Cheated, for the later #636 PRs:
   - a nested pop in an index, such as x[0][x[0].pop()], writes an inner
     length word, which the shared locals_kept frame exempts, but the
     index's expr_vv_case for such a pop is exprSimPlaces' cheated
     compile_pop_nested_sim;
   - the index runs after the base, so the base's target_post must survive
     its fragment: place_ptr_rel does (place_ptr_rel_vars_frame: the local
     pointers and the base's operand are not fresh at the index's start),
     but place_readable does not, as the index can pop the base's array;
     the source then reads the base from the popped history
     (read_memory_path), and the element's bytes are still in memory, as
     a root pop writes only its exempt length word, but nothing relates
     the popped history to memory yet;
   - the bounds check: a source RuntimeError for an index out of range
     (evaluate_subscripts array_index for a local's place,
     resolve_array_element's checks for a storage one) against
     compile_array_subscript's ASSERT, which aborts, and an index in range
     against the length the loader reads (an MLOAD at the base's pointer,
     an SLOAD or TLOAD at its slot);
   - the mapping slot: compile_mapping_subscript's SHA3 over the slot and
     key words in a fresh 64-byte buffer against hashmap_slot slot
     (encode_hashmap_key kt kv).
   Given those, the element's place is at the base's pointer plus the
   element's offset (mem_step_offset) for a local, and at the element's
   slot for storage. *)
Theorem target_subscript_case:
  !nocalls ctx func cenv cx bt e.
    target_case nocalls ctx func cenv cx bt /\
    ((?s pv s1. eval_base_place cx bt s = (INL pv, s1)) ==>
     expr_sim_case nocalls ctx func cenv cx e /\
     expr_vv_case nocalls ctx func cenv cx e) ==>
    target_case nocalls ctx func cenv cx (SubscriptTarget bt e)
Proof
  cheat
QED
