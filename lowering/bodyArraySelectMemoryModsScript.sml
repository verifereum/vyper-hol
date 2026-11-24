(* Memory-place selection at the linked no-copy array cut. *)
Theory bodyArraySelectMemoryMods
Ancestors
  bodyArrayNoCopyCutsMods bodyArrayNoCopySourceMods bodySubscriptArrayRouteDefsMods
  bodyFullPostsMods loweringPosts exprLoweringProps compileEnv vyperAST
  exprBodyPreProps vyperTypeSystem

Theorem array_memory_base_post[local]:
  vv_post_mods H ctx func cenv cx obj es sa sm s0 mid
    (PlaceR (MemoryPlace id path)) bvv s /\
  post_value_type cenv obj = ArrayT et bd ==>
  ?p. bvv = LocatedValue (ArrayT et bd) p /\ p.ptr_location = LocMemory /\
      vv_post H ctx func cenv cx obj es sa sm s0 mid
        (PlaceR (MemoryPlace id path)) bvv s /\
      immutable_frame_mods func cenv cx mid s
Proof
  Cases_on `bvv` >> simp[vv_post_mods_def, vv_at_def, is_word_type_def] >>
  strip_tac >> rename1 `p.ptr_location = LocMemory` >>
  Cases_on `p.ptr_location = LocMemory` >> fs[] >>
  fs[vv_holds_mods_def, vv_holds_def, is_bytestring_type_def] >>
  gvs[vv_post_def, vv_at_def, vv_holds_def, vv_place_ptr_mods_def,
      is_word_type_def, is_bytestring_type_def] >> metis_tac[]
QED
