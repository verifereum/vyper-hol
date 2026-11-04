(* Independent checked-frontend bytecode witnesses for raw_call: byte-string
   data in statement and expression position, max_outsize, is_static_call,
   is_delegate_call, revert_on_failure=False with the bool and the
   (bool, Bytes) results, and value=/gas= in source order. The fixtures are
   checked in evalCompilerRawCalls1 and evalCompilerRawCalls2, which build in
   parallel. *)
Theory evalCompilerRawCalls
Ancestors evalCompilerRawCalls1 evalCompilerRawCalls2
