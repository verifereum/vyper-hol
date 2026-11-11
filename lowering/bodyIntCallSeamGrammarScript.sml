(* Keep the count interface's combinatorics notation out of caller statements. *)
Theory bodyIntCallSeamGrammar
Ancestors
  bodyIntCallArgumentCountInterface bodyIntCallInvokeExistence

val _ = Parse.gen_remove_ovl_mapping "tops" ``tops``;
