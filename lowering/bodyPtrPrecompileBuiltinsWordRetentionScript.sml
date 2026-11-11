Theory bodyPtrPrecompileBuiltinsWordRetention
Ancestors wordArgsPtr bodyPtrDefs loweringPosts ptrDiscipline venomState

Theorem clean_word_operand_frame:
  wb_frame cenv es es' sa s0 s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (!l. op <> Label l) /\ eval_operand op s0 = SOME w /\
  op_taint tn0 op = {} ==>
  eval_operand op s = SOME w /\ op_taint tn op = {}
Proof
  strip_tac >> drule_all word_operand_frame >> simp[]
QED
