(* Independent checked-frontend bytecode witnesses for the keyword operands
   of extcall/staticcall (value=, gas=, default_return_value=,
   skip_contract_check=) and for send with and without gas=.
   The fixtures are checked in evalCompilerExternalCallKwargs1 and
   evalCompilerExternalCallKwargs2, which build in parallel. *)
Theory evalCompilerExternalCallKwargs
Ancestors evalCompilerExternalCallKwargs1 evalCompilerExternalCallKwargs2
