Theory exprSimIfExpWidenedPhysicalType
Ancestors
  exprSimIfExp exprSimHyps exprSimHypsDefs loweringPosts
  exprLowering vyperAST vyperTypeArgFits vyperTypeSystem exprSimLayoutTransport

Theorem post_value_type_nonword:
  expr_body_pre ce cx env e es /\ ~is_word_type (expr_type e) ==>
  ~is_word_type (post_value_type ce e)
Proof
  strip_tac >> Cases_on `post_value_type ce e = expr_type e`
  >- gvs[] >>
  `~is_bytestring_type (expr_type e)` by
    metis_tac[post_value_type_bytestring] >>
  `?ann fid args drv. e = Call ann (IntCall fid) args drv` by
    (spose_not_then assume_tac >>
     `post_value_type ce e = expr_type e` by
       (irule post_value_type_not_int_call >> metis_tac[]) >> gvs[]) >>
  gvs[expr_type_def] >>
  drule_all ifexp_intcall_copy_source >> strip_tac >>
  fs[type_widens_to_def] >> metis_tac[compatible_word_type]
QED
