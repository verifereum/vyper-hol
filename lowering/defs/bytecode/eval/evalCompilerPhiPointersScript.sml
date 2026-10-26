(* Independent checked-frontend bytecode witnesses for memory pointers merged
   by a PHI: uint2str and ternaries (IfExp) of non-word type (#561).
   The fixtures are checked in evalCompilerPhiPointers1 and
   evalCompilerPhiPointers2, which build in parallel. *)
Theory evalCompilerPhiPointers
Ancestors evalCompilerPhiPointers1 evalCompilerPhiPointers2
