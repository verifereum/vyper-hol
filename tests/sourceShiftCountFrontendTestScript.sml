Theory sourceShiftCountFrontendTest
Ancestors
  sourceShiftCountTest vyperTypeContract vyperAST
Libs
  vyperCheckContractFrontendLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["fixtures/check_contract"];

(* Retained #135 compatibility successes. The paired ordinary public route
   separately checks both rows (exact modules and independent artifacts) in
   sourceOrdinaryProgramCoreTest; there is no independent Source API here. *)
val address = ``0w : address``;
fun audit th = let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
  if null (hyp th) andalso null axioms andalso
     List.all (fn s => s = "DISK_THM") oracles then ()
  else raise Fail "source shift regression theorem has assumptions/axioms/oracles" end;
val () = app (fn name => let
  val legacy = vyperCheckContractFrontendLib.check_constant_contract_file_legacy
    {address=address,path="fixtures/check_contract/" ^ name ^ ".json"}
  val () = audit legacy
  val _ = save_thm (name ^ "_legacy",legacy)
in () end) ["constant_bound","constant_shifts"];
