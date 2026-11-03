(* Public HOL JSON decoders; parsing is shared with standalone imports. *)
structure jsonASTLib :> jsonASTLib = struct
  open Abbrev
  structure Decode = JsonASTDecodeFn (JsonImportHol)
  open Decode
end
