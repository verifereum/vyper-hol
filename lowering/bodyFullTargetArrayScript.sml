(* The element suffix of a subscript into an array target on the joint
   line: the bounds guard and element-pointer arithmetic after the index
   (subscript_tail_full, bodyFullTargetSubscript).

   TOP-LEVEL:
     target_array_tail_full -- subscript_tail_full when the base is an array *)
Theory bodyFullTargetArray
Ancestors
  bodyFullTargetSubscript bodyFullTargetDefs bodySimFull targetPlaceSim
  vyperTypeSystem vyperInterpreter vyperState

Theorem target_array_tail_full:
  body_inv tops ctx cenv cx /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  type_place_target env bt = SOME (Type (ArrayT et bd)) ==>
  subscript_tail_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt e es
Proof
  cheat
QED
