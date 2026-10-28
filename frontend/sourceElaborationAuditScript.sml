Theory sourceElaborationAudit
Ancestors
  sourceConstASTLibTest sourceConstEvalProps sourceConstBuiltinTest
  sourceConstEnvTest sourceConstValueTest sourceSyntaxLibTest
  sourceResolveTest sourceTypeTest sourceTypeProvenance sourceTypeFrontendLibTest
  powerDomainProps vyperPowerDomainTest abiBuiltinDispatchTest abiAliasRegression

(* Audit only the new, locally verified work. Existing lowering simulations
   contain admissions and are deliberately NOT certified by this audit.
   Nor does export closure establish whole-program elaboration or parity. *)
fun audit_source_elaboration thy =
  let
    val exports = DB.thms thy
    fun check (name, th) =
      let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
      in
        if null (Thm.hyp th) andalso null axioms andalso
           List.all (fn s => s = "DISK_THM") oracles then ()
        else raise Fail ("source elaboration kernel audit failed: " ^ thy ^ "." ^ name)
      end
  in
    if null exports then raise Fail ("empty audit theory: " ^ thy) else ();
    List.app check exports;
    print ("SOURCE_ELABORATION_KERNEL_CLOSED " ^ thy ^ " exports=" ^
           Int.toString (length exports) ^ "\n")
  end;

val () = List.app audit_source_elaboration
  ["sourceConstAST", "sourceConstAnnotation", "sourceConstASTLibTest",
   "sourceConstBuiltin", "sourceConstBuiltinCompute", "sourceConstBuiltinProps",
   "sourceConstBuiltinTest", "sourceConstEval", "sourceConstEvalProps",
   "sourceConstEnv", "sourceConstEnvProps", "sourceConstEnvTest",
   "sourceConstValue", "sourceConstValueProps", "sourceConstValueTest",
   "sourceSyntax", "sourceSyntaxLibTest", "sourceResolve", "sourceResolveModules",
   "sourceResolveProps", "sourceResolveTest", "sourceTypeDefs", "sourceTypeResolve",
   "sourceTypeProps", "sourceTypeProvenance", "sourceTypeTest",
   "sourceTypeFrontendLibTest", "powerDomainProps", "vyperPowerDomainTest",
   "abiBuiltinDispatchTest", "abiAliasRegression"];
