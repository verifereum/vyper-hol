(* Public HOL JSON decoders; parsing is shared with standalone imports. *)
val () = load "jsonImportTerm";
val () = load "JsonImportHol";
val () = load "JsonASTDecodeFn";
structure jsonASTLib :> jsonASTLib = struct
  open Abbrev
  structure Decode = JsonASTDecodeFn (JsonImportHol)
  open Decode
end
