(* Independent checked-frontend bytecode witnesses for extract32, concat,
   slice (bytes32 and .code sources) and ceil (#566).  The fixtures are
   checked in evalCompilerBuiltinForms1, 2 and 4, which build in parallel. *)
Theory evalCompilerBuiltinForms
Ancestors
  evalCompilerBuiltinForms1 evalCompilerBuiltinForms2
  evalCompilerBuiltinForms4
