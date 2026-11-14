(* The element suffix of a subscript into an array target on the joint
   line: the bounds guard and element-pointer arithmetic after the index
   (subscript_tail_full, bodyFullTargetSubscript).

   TOP-LEVEL:
     target_array_tail_full -- subscript_tail_full when the base is an array *)
Theory bodyFullTargetArray
Ancestors
  bodyFullTargetArraySource bodyFullTargetArraySuffix
  bodyFullTargetSubscript bodyFullTargetDefs bodySimFull targetPlaceSim
  vyperTypeSystem vyperInterpreter vyperState

Theorem target_array_tail_full:
  body_inv tops ctx cenv cx /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  type_place_target env bt = SOME (Type (ArrayT et bd)) ==>
  subscript_tail_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt e es
Proof
  strip_tac >> simp[subscript_tail_full_def] >> rpt gen_tac >> strip_tac >>
  irule target_array_suffix_full >>
  simp[array_tail_packet_def] >> metis_tac[]
QED
