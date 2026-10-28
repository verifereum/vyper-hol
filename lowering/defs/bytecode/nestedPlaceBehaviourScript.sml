(* Opt-in independent EVM transaction validation; no logical oracle facts. *)
Theory nestedPlaceBehaviour

fun holbuild_extra_deps (_ : string list) = ();
fun holbuild_extra_outputs (_ : string list) = ();
val () = holbuild_extra_deps
  ["nested-places/validation.tar.gz", "nested_place_driver.py",
   "nested_place_execute.py", "nested_place_behaviour_cases.py",
   "memory_store_witnesses.py"];
val () = holbuild_extra_outputs
  ["nested-places/behaviour.json", "nested-places/behaviour-status.json"];
val python = case OS.Process.getEnv "NESTED_PLACE_PYTHON" of
  SOME path => path | NONE => "/home/lukasz/.local/share/uv/tools/vyper/bin/python3";
val result = OS.Process.system ("'" ^ python ^ "' nested_place_driver.py execute");
val () = if OS.Process.isSuccess result then ()
  else raise Fail "independent nested place EVM execution failed (see log)";
