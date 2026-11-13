(* The element suffix of a subscript into a mapping target on the joint
   line: the key's hash (for a bytestring key) and the slot computation
   after the index (subscript_tail_full, bodyFullTargetSubscript).

   TOP-LEVEL:
     target_mapping_tail_full -- subscript_tail_full when the base is a
       mapping *)
Theory bodyFullTargetMapping
Ancestors
  bodyFullTargetSubscript bodyFullTargetDefs bodySimFull targetPlaceSim
  vyperTypeSystem vyperInterpreter vyperState

Theorem target_mapping_tail_full:
  body_inv tops ctx cenv cx /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  type_place_target env bt = SOME (HashMapT kt vt) ==>
  subscript_tail_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt e es
Proof
  cheat
QED
