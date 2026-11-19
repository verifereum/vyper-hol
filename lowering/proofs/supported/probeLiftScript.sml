(* Gate-off parity probe only (never merged): row flags the native runner sets. *)
Theory probeLift
Ancestors arithmetic

val _ = new_constant ("probe_lift", ``:num -> bool``);
