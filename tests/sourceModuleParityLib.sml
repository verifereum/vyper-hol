(* Full-Source certificates extend the shared test-only fixture utilities. *)
structure sourceModuleParityLib = struct
open HolKernel Parse boolLib bossLib
open sourceModuleCompileTheory sourceModuleElaborateTheory sourceModuleDefsTheory
open sourceSyntaxTheory vyperASTTheory finite_mapTheory
open sourceBytecodeFixtureLib
fun phase name = let val p = program name val tr = trust name in
  ``source_module_elaborate_simple 80 ^tr ^keys ^p`` end;
fun check name = let val p = program name val tr = trust name val ls = layouts name in
  ``source_module_check_simple 80 ^tr ^keys ^p ^ls ^address`` end;
fun compile name = let val p = program name val tr = trust name val ls = layouts name in
  ``source_module_compile 80 ^tr ^keys ^p ^ls ^address
      (K SOME) (o1_policy all_capabilities)`` end;

(* Reusing a kernel phase certificate is safe only at the identical freshly
   decoded original-source input, not merely at the same fixture name. *)
fun certified_phase name = let
  val suffix = if name = "method_id_var" then "_reject" else "_ast"
  val th = DB.fetch "sourceModuleFrontendLibTest" ("source_module_" ^ name ^ suffix)
  val () = if aconv (lhs (concl th)) (phase name) then ()
    else raise Fail ("stale source phase certificate: " ^ name)
  in th end;
fun certified_check name = let
  val th = DB.fetch "sourceModuleFrontendLibTest" ("source_module_" ^ name ^ "_composition")
  val () = if aconv (lhs (concl th)) (check name) then ()
    else raise Fail ("stale source checker certificate: " ^ name)
  in th end;
fun tops name = let
  val retained = hd (#2 (strip_comb (rhs (concl (certified_phase name)))))
  val modules = List.nth (#2 (strip_comb retained),1)
  val entries = #1 (listSyntax.dest_list modules)
  in case entries of [entry] => let val (src,tls) = pairSyntax.dest_pair entry in
    if optionSyntax.is_none src then tls else raise Fail "non-main module" end
  | _ => raise Fail "multiple modules" end;
fun wrapper name compiler = let
  val th = simpLib.SIMP_CONV (srw_ss())
    [source_module_compile_def,certified_check name,source_module_bind_def,
     retained_executable_def,compiler] (compile name)
  val head = #1 (strip_comb (rhs (concl th)))
  val () = if same_const head ``SM_Ok`` orelse same_const head ``SM_Error`` then ()
    else raise Fail ("residual source wrapper: " ^ name)
  in th end;
end
