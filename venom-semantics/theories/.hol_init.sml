(* Initialization for venom-semantics HOL4 development *)
(* Uses VFMDIR environment variable for verifereum path *)
val vfmdir = case OS.Process.getEnv "VFMDIR" of
    SOME d => d
  | NONE => raise Fail "VFMDIR environment variable not set";

Meta.loadPath := [
  vfmdir ^ "/util",
  vfmdir ^ "/spec"
] @ (!Meta.loadPath);
