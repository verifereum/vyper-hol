(* Observe the actual post-pipeline context at the existing compiler evaluator
   boundary, then suspend planning with a reflexive kernel equation. RESIDUAL
   is expected here; this diagnostic target makes no bytecode parity claim. *)
Theory nestedPlacePlanTrace
Ancestors
  compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute
  stackPlanGen byte option alist integer_word
Libs
  vyperCheckContractFrontendLib jsonASTLib finite_mapLib wordsLib
  evalCompilerBytecodeLib memoryStoreWitnessLib

fun holbuild_extra_deps (_ : string list) = ();
fun holbuild_extra_outputs (_ : string list) = ();
val () = holbuild_extra_deps
  ["nested_place_driver.py", "nested-places/diagnostic.tar.gz"];
val () = holbuild_extra_outputs ["nested-places/s20-context-0.term"];
val python = case OS.Process.getEnv "NESTED_PLACE_PYTHON" of
  SOME path => path | NONE => "/home/lukasz/.local/share/uv/tools/vyper/bin/python3";
val () = if OS.Process.isSuccess (OS.Process.system
  ("'" ^ python ^ "' nested_place_driver.py trace-prepare")) then ()
  else raise Fail "cannot unpack diagnostic inputs";
val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset;
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos]);
val contexts = ref 0;
fun observe_plan tm = let
  val path = "nested-places/s20-context-" ^ Int.toString (!contexts) ^ ".term"
  val () = contexts := !contexts + 1
  val () = memoryStoreWitnessLib.write path (term_to_string (rand tm))
  val th = REFL tm
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
in
  if null (hyp th) andalso null axioms andalso
     List.all (fn s => s = "DISK_THM") oracles andalso
     aconv (lhs (concl th)) tm
  then th else raise Fail "untrusted observed plan equation"
end;
(* Reinstall direct callers against the observer's dispatch cell, as the
   production selector bridge does when replacing its computation cell. *)
val head = ``generate_context_plan``;
val rules = List.concat (List.concat (map
  (fn (_,xs) => map (fn clauses.RRules ths => ths
                     | clauses.Conversion _ => []) xs)
  (computeLib.listItems (computeLib.the_compset ()))));
val callers = List.filter (fn th =>
  let val (_,body) = strip_forall (concl th)
      val (_,r) = dest_eq body
  in can (find_term (aconv head)) r end
  handle HOL_ERR _ => false) rules;
val () = computeLib.del_funs [generate_context_plan_def];
val () = computeLib.add_convs [(head,1,observe_plan)];
val () = computeLib.add_funs callers;
val _ = memoryStoreWitnessLib.evaluate "nested-places/oracle"
  "s20_nested_map_read_key_order";
val () = if !contexts > 0 then () else raise Fail "runtime context was not observed";
