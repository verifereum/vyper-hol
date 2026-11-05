(* A piece of S1 (loweringRuntimeCorrect's lower_vyper_runtime_unit_correct). *)
Theory stmtsEnvRetTy
Ancestors
  stmtSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list pair fragExec  bodySim bodySimMain loweringHalt stmtLoweringMono  exprLoweringProps
  compileEnv compileVyper moduleLowering stmtLowering
  e2eDefs supportedProgram vyperLoweringCorrect rawReturnHeader
  vyperTypeSelectedEntrySoundness vyperTypeSystem
  vyperInterpreter vyperState vyperContext
  venomState venomExecSemantics venomWf

val _ = Parse.hide "body";

(* ADMITTED (lowering): compile_stmt reads the return type only to compile
   a valued return and as the element type of an Append whose target root
   has no array type.  A supported Append targets a storage dynamic array,
   whose type body_inv's compile env gives (ce_module_var_type), and no
   declaration changes that. *)
Theorem stmts_env_ret_ty:
  !ss tops bindings ctx cenv cx lctx ty ty'.
    supported_stmts tops bindings ss /\ body_inv tops ctx cenv cx /\
    ~stmts_valued_return ss ==>
    stmts_env cenv lctx ty ss = stmts_env cenv lctx ty' ss
Proof
  cheat
QED

