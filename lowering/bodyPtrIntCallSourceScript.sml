(* Source lookup boundaries for the pointer internal-call case. *)
Theory bodyPtrIntCallSource
Ancestors
  supportedProgram supportedDecls vyperTypeContractStaticMaps
  vyperInterpreter list

val _ = Parse.hide "body";

Theorem intcall_runtime_no_defaults:
  supported_program ts /\
  lookup_callable_function F fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
  dflts = []
Proof
  simp[lookup_callable_function_def, AllCaseEqs()] >>
  strip_tac >>
  drule lookup_function_Internal_SOME_MEM >> strip_tac >>
  fs[supported_program_def, supported_declaration_headers_def, EVERY_MEM] >>
  qpat_x_assum `!e. MEM e ts ==> supported_declaration_header ts e` drule >>
  simp[supported_function_header_contract, NULL_EQ]
QED

Theorem intcall_runtime_needed_defaults:
  supported_program ts /\
  lookup_callable_function F fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
  DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts = []
Proof
  strip_tac >> drule_all intcall_runtime_no_defaults >> simp[]
QED
