(* Opt-in external validation capability check. No compiler result is asserted. *)
Theory nestedPlaceCapability
Ancestors bool

val () = print ("VALIDATION_CWD " ^ OS.FileSys.getDir () ^ "\n");

val () =
  if OS.Process.isSuccess (OS.Process.system "python3 --version") then ()
  else raise Fail "nested places: python3 unavailable";
val () =
  if OS.Process.isSuccess (OS.Process.system "vyper --version") then ()
  else raise Fail "nested places: pinned Vyper unavailable; use external operator recipe";
