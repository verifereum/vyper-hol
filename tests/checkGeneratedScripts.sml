(* Read-only check using the library built by the default test root. *)
val () = load "vyperTestLib";
val () = OS.FileSys.chDir "tests";
val () = vyperTestLib.check_generated_scripts ();
val () = OS.Process.exit OS.Process.success;
