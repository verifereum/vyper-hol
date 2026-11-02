(* Task-scoped oracle-tag inventory. Only the named, preexisting expression
   simulation admissions are allowed; any other debt fails the build. *)
Theory conversionProofAudit
Ancestors
  builtinIntClamp builtinConvertPrefix builtinTypeConvert1 builtinTypeConvert2
  exprLoweringProps vyperTypeConversions vyperTypeBuiltins vyperTypeSystem
  vyperFixedBytesConvertTest vyperBytesDecimalConvertTest vyperBytesAddressConvertTest
  loweringBoundaryChecks e2eDeployChecks e2eBoundaryTest
  supportedExprFormProps supportedExprForms supportedExprs supportedTypes
  evalCompilerBytecodeScalarConvertBytes32ToDecimal
  evalCompilerBytecodeScalarConvertDecimal evalCompilerBytecodeScalarConvertIntToDecimal
  evalCompilerBytecodeScalarWordEval

val audited = ["builtinIntClamp", "builtinConvertPrefix", "builtinTypeConvert1",
  "builtinTypeConvert2", "exprLoweringProps", "vyperTypeConversions",
  "vyperTypeBuiltins", "vyperFixedBytesConvertTest", "vyperBytesDecimalConvertTest",
  "vyperBytesAddressConvertTest", "loweringBoundaryChecks", "e2eDeployChecks",
  "e2eBoundaryTest", "supportedExprFormProps", "vyperTypeSystem",
  "supportedExprForms", "supportedExprs", "supportedTypes",
  "evalCompilerBytecodeScalarConvertBytes32ToDecimal",
  "evalCompilerBytecodeScalarConvertDecimal",
  "evalCompilerBytecodeScalarConvertIntToDecimal",
  "evalCompilerBytecodeScalarWordEval"]
(* Main proves compile_name_correct and compile_expr_extends_insts without
   admissions; neither may regress to the branch's former allowed debt. *)
val existing_debt = ["compile_neg_correct", "compile_expr_correct",
  "compile_binop_correct"]
fun audit thy = let
  val thms = DB.thms thy
  fun check (name,th) = let
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
    val debt = List.filter (fn s => s <> "DISK_THM") oracles @ axioms
    val known = thy = "exprLoweringProps" andalso
      List.exists (fn n => n = name) existing_debt
    val _ = if null (Thm.hyp th) then () else
      raise Fail ("unexpected kernel hypotheses: " ^ thy ^ "." ^ name)
  in if null debt then ()
     else if known andalso null axioms andalso
       List.all (fn s => s = "cheat") debt then print
       ("ORACLE_DEBT " ^ thy ^ "." ^ name ^ " " ^ String.concatWith "," debt ^ "\n")
     else raise Fail ("unexpected oracle debt: " ^ thy ^ "." ^ name ^ " " ^
       String.concatWith "," debt) end
in List.app check thms;
   print ("AUDITED " ^ thy ^ " " ^ Int.toString (length thms) ^ "\n") end
val () = List.app audit audited
