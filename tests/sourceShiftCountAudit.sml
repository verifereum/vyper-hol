(* Re-open exported objects, not just in-script proof states. *)
val () = app load ["sourceExprPropsTheory", "sourceExprTestTheory",
  "sourceModuleFrontendLibTestTheory", "sourceShiftCountTestTheory",
  "sourceShiftCountModuleTestTheory"];
val audited = ref 0;
fun audit thy = app (fn (name,th) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  val () = if null (Thm.hyp th) andalso null axioms andalso
      List.all (fn s => s = "DISK_THM") oracles then ()
    else raise Fail ("non-kernel/assumed theorem: " ^ thy ^ "." ^ name)
  in audited := !audited + 1 end) (DB.thms thy);
val () = app audit ["sourceExprProps", "sourceExprTest", "sourceModuleFrontendLibTest",
  "sourceShiftCountTest", "sourceShiftCountModuleTest"];
val () = print ("SOURCE_SHIFT_KERNEL_AUDIT " ^ Int.toString (!audited) ^
  " exported theorems; hyp=0 axioms=0 oracles=DISK_THM-only\n");
val () = OS.Process.exit OS.Process.success;
