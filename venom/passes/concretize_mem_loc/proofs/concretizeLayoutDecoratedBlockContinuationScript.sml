Theory concretizeLayoutDecoratedBlockContinuation
Ancestors concretizeLayoutCompletedJump frameFiniteJointDecoration
  frameJointTransition frameJointTrace concretizeLayoutPhaseOrigin
  frameRelocationEnvironment venomExecSemantics venomState list arithmetic

Theorem layout_path_block_edge:
  es = MAP FST (pre ++ wb ++ [(SOME (OriginBlock fuel post),qn)] ++ wr ++ suffix) /\
  qs = MAP SND (pre ++ wb ++ [(SOME (OriginBlock fuel post),qn)] ++ wr ++ suffix) /\
  c = LENGTH pre + LENGTH wb ==>
  c < LENGTH es /\ EL c es = SOME (OriginBlock fuel post) /\
  EL (SUC c) (q0::qs) = qn
Proof
  strip_tac >> gvs[] >>
  simp[MAP_APPEND, EL_APPEND_EQN]
QED

val _ = export_theory();
