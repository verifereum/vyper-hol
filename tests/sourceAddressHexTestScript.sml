Theory sourceAddressHexTest
Ancestors
  sourceAddressHexExprTest vyperTypeContract vyperAST
Libs
  vyperCheckContractFrontendLib

fun holbuild_extra_deps (_ : string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract/address_bytes20.json"];
val address = ``0w:address``;
fun audit th = let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
  if null (hyp th) andalso null axioms andalso
     List.all (fn s => s = "DISK_THM") oracles then ()
  else raise Fail "address/hex theorem has assumptions, axioms or oracles" end;

(* Retained legacy regression: both checker modes accept exactly this AST.
   Source-domain validation remains in sourceAddressHexExprTest and the
   ordinary paired-source address_bytes20 acceptance row. *)
val expected = ``[(NONE:num option,[FunctionDecl External Pure F F "f"
  [("a",BaseT AddressT)] [] (BaseT (BytesT (Fixed 20)))
  [Return (SOME (TypeBuiltin (BaseT (BytesT (Fixed 20))) Convert
    (BaseT (BytesT (Fixed 20))) [Name (BaseT AddressT) "a"]))]])]``;
val () = app (fn deploy => let
  val ordinary = vyperCheckContractFrontendLib.check_contract_file_legacy
    {in_deploy=deploy,address=address,path="fixtures/check_contract/address_bytes20.json"}
  val modules = List.last (#2 (strip_comb (lhs (concl ordinary))))
  val () = if aconv modules expected then () else raise Fail "legacy address_bytes20 AST mismatch"
  val () = audit ordinary
  val _ = save_thm (if deploy then "address_bytes20_ordinary_deploy" else "address_bytes20_ordinary_runtime",ordinary)
in () end) [false,true];
