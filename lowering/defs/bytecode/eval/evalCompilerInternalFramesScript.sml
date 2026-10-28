(* Independent pinned-oracle regressions for issue #545 internal frames.
   Captures use VYPER_PIN with python_o1_bytecode_oracle.py settings.
   The fixtures are checked in evalCompilerInternalFrames1 and
   evalCompilerInternalFrames2, which build in parallel. *)
Theory evalCompilerInternalFrames
Ancestors evalCompilerInternalFramesDiamond evalCompilerInternalFramesExtCall evalCompilerInternalFrames1 evalCompilerInternalFrames2
