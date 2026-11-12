Theory bodyPtrIfExpArmLower
Ancestors
  exprLowering compileEnv

Theorem ifexp_arm_lower_value:
  compile_expr ce ty e sa = (vv,sc) /\
  compile_ifexp_arm ce rt at vv sc = (op,sn) /\
  (is_word_type rt \/ same_memory_layout ce at rt) ==>
  lower_value compile_expr ce ty e sa = (op,sn)
Proof
  strip_tac >>
  gvs[compile_ifexp_arm_def, lower_value_def, comp_bind_def]
QED
