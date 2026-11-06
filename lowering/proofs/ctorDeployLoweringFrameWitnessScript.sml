Theory ctorDeployLoweringFrameWitness
Ancestors
  ctorDeployLoweringDefs ctorDeployLoweringFrameRegion o1PipelineCorrect
  concretizeMemLocDefs callTrace alist integer_word vyperEvmBoundary
  vfmContext vfmState vfmExecution vfmBuffer finite_set
Libs finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

(* Candidate 1: real deployment lowering and configured pipeline, with a
   hostile embedded runtime segment. No source/entry premise is assumed. *)
Theorem string_pass_ctor_compilation_probe:
  IS_SOME
    (case resolve_o1_policy (o1_policy all_capabilities) of
       NONE => NONE
     | SOME rp =>
       case lower_vyper_deploy_unit
         [VariableDecl Private Storage "s" (BaseT (StringT 1)) (SOME 0);
          FunctionDecl Deploy Payable F F "__init__" [] [] NoneT [Pass]]
         rp [0x5bw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0xf1w;0x00w] of
         NONE => NONE
       | SOME u => checked_unit_pipeline
           o1PipelineCorrect$o1_pipeline (K SOME) rp u)
Proof
  EVAL_TAC
QED

Theorem string_pass_ctor_bytecode_probe:
    (case resolve_o1_policy (o1_policy all_capabilities) of
       NONE => NONE
     | SOME rp =>
       case lower_vyper_deploy_unit
         [VariableDecl Private Storage "s" (BaseT (StringT 1)) (SOME 0);
          FunctionDecl Deploy Payable F F "__init__" [] [] NoneT [Pass]]
         rp [0x5bw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0xf1w;0x00w] of
         NONE => NONE
       | SOME u => checked_unit_pipeline
           o1PipelineCorrect$o1_pipeline (K SOME) rp u) = SOME
      [91w;96w;10w;95w;144w;129w;97w;0w;19w;144w;57w;
       96w;10w;144w;243w;91w;95w;128w;253w;
       0x5bw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0xf1w;0x00w]
Proof
  EVAL_TAC
QED

