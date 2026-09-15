(* Emit the current Vyper export-selection baseline without generating theories.
   Load project libraries from the repository root, then use the test library's
   expected paths relative to tests/. *)
load "vyperTestLib";
OS.FileSys.chDir "tests";
vyperTestLib.report_coverage ();
