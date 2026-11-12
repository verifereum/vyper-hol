(*
 * Seam of bodyPtrSubscript's subscript_expr_ptr_ok: a subscript of a
 * mapping whose value is not a mapping, given the base's mapping judgment
 * (bodyPtrSubscriptMapDefs' expr_map_sim_ptr), which
 * bodyPtrSubscriptMapResidual supplies.
 *
 * TOP-LEVEL:
 *   subscript_map_ptr
 *)
Theory bodyPtrSubscriptSeamMap
Ancestors
  bodyPtrSubscriptSeamMapConsumer
  bodyPtrSubscriptScratchTransfer bodyPtrSubscriptMapDefs bodyPtrPreds
  bodyPtrDefs bodySim exprSimHypsDefs exprLowering vyperInterpreter
  vyperState vyperContext vyperAST

(* The pointer twin of S1's compile_subscript_map_case
   (exprSimSubscriptMap): the base's expr_map_sim_ptr gives the operand
   holding the mapping's slot, the key is lowered after it (lower_value at
   the key's own type), a bytestring key is hashed (compile_keccak256_key),
   and compile_mapping_subscript stores the slot and the key word in a fresh
   64-byte buffer and takes its SHA3, which hashmap_slot slot
   (encode_hashmap_key kt kv) matches.  The result is a storage or
   transient place, whose ptr_vv_ok owes the taint bound over the leaf's
   dead bytes (stor_taint_ok in ghost_inv), and, when the subscript has no
   effect, vv_post's vv_storage_live.
   Hints: the S1 proof is exprSimSubscriptMap in this tree
   (compile_mapping_subscript_outcome, mapping_leaf_vv_holds);
   bodyPtrSubscriptScratchStore and bodyPtrSubscriptScratchTransfer have
   counted MSTOREs into a covered scratch buffer; taint_ok lets SHA3 read
   no tainted byte, so the stored slot and key must be untainted. *)
Theorem subscript_map_ptr:
  !cx ann e1 e2 d PG tops ctx func cenv env ty es kt vt.
    (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_ptr_ok cx e2) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Subscript ann e1 e2) es /\
    place_type cenv e1 = MapPT kt vt /\
    expr_map_sim_ptr d ctx PG func cenv cx ty e1 es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Subscript ann e1 e2) es
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[expr_vv_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  irule compile_mapping_subscript_outcome_ptr >> metis_tac[]
QED
