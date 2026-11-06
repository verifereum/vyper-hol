Theory bodyPtrIfExpLocatedTag
Ancestors loweringPosts bodyPtrIfExpUnwrapContract

(* The post projection already exists as vv_post_located_type in
   bodyPtrIfExpUnwrapContract; only the more primitive boundary is missing. *)
Theorem vv_holds_located_type:
  vv_holds cenv cx t tv (LocatedValue r p) es s ==> r = t
Proof
  simp[vv_holds_def]
QED
