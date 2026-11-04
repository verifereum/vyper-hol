(* A raw-return flag is admitted by support but erased by callable lookup.
   This probe refutes the auxiliary raw=F selection, not body_intcall_case. *)
Theory bodyIntCallSourceProbe
Ancestors
  supportedProgram vyperInterpreter

Theorem raw_internal_selection_obstruction:
  supported_program [FunctionDecl Internal Pure F T "raw" [] [] NoneT []] /\
  lookup_callable_function F "raw"
    [FunctionDecl Internal Pure F T "raw" [] [] NoneT []] =
    SOME (Pure,F,[],[],NoneT,[]) /\
  ~MEM (FunctionDecl Internal Pure F F "raw" [] [] NoneT [])
    [FunctionDecl Internal Pure F T "raw" [] [] NoneT []]
Proof
  EVAL_TAC
QED
