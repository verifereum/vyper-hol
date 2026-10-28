signature sourceModuleLoaderLib = sig
  include Abbrev
  (* Syntax/provenance are claims from a trusted source loader, NOT HOL parsing
     correctness or compiler-metadata authenticity theorems. *)
  type loaded = {program:term, keys:term, nonreentrant_defaults:term,
                 declaration_only:term, provenance:JSON.value}
  val source_capture : loaded JSONDecode.decoder
  val load_file : string -> loaded
  val policies : loaded -> term
end
