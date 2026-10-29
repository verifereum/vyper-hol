(* Re-open exported theory objects and reconstruct public wrapper statements
   from current source JSON and independently retained pinned byte arrays. *)
val () = OS.FileSys.chDir "tests";
val () = app load ["sourceModuleParityTheory", "sourceModuleParityLib", "wordsLib"];
open HolKernel Parse boolLib bossLib;
val () = app sourceModuleParityLib.audit
  ["sourceModuleCompile", "sourceModuleParityInput", "sourceModuleParity"];
val () = app (fn name => let
  val th = DB.fetch "sourceModuleParityInput" (name ^ "_source")
  val () = if aconv (lhs (concl th)) (sourceModuleParityLib.phase name) then ()
    else raise Fail ("export source identity: " ^ name)
  in if name = "method_id_var" then () else let
    val th = DB.fetch "sourceModuleParityInput" (name ^ "_checked")
    in if aconv (lhs (concl th)) (sourceModuleParityLib.check name) then ()
      else raise Fail ("export checked modules: " ^ name) end
  end) sourceModuleParityLib.names;
val () = app (fn name => let
  val th = DB.fetch "sourceModuleParity" (name ^ "_python_parity")
  val () = if aconv (lhs (concl th)) (sourceModuleParityLib.compile name) then ()
    else raise Fail ("export wrapper identity: " ^ name)
  val payload = hd (#2 (strip_comb (rhs (concl th))))
  val (_,rest) = pairSyntax.dest_pair payload
  val (_,bytes) = pairSyntax.dest_pair rest
  val expected = sourceModuleParityLib.expected name
  val equal = EVAL (mk_eq (bytes,expected))
  in if aconv (rhs (concl equal)) T then
    print ("SOURCE_PARITY_EXPORT_EXACT " ^ name ^ " deploy+runtime\n")
    else raise Fail ("export oracle bytes: " ^ name) end) sourceModuleParityLib.certified;
val () = print "SOURCE_PARITY_EXPORT_AUDIT_PASS 37 source rows; 9 exact wrapper byte pairs; no admissions\n";
