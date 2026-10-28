Theory sourceAddressHexTest
Ancestors
  sourceAddressHexExprTest sourceModuleElaborate sourceModuleDefs sourceSyntax sourceExprElaborate
  sourceExprDefs sourceConstBuiltinCompute sourceConstBuiltin sourceConstAST
  vyperTypeContract vyperAST finite_map
Libs
  vyperCheckContractFrontendLib cv_transLib

fun holbuild_extra_deps (_ : string list) = ();
val () = holbuild_extra_deps ["sourceAddressHexFixtures", "fixtures/check_contract/address_bytes20.json"];

val () = computeLib.add_funs [address_checksum_keccak,address_zero_keccak];

val address = ``0w:address``;
val trust = ``<| smt_ids := [(["main"],NONE)]; smt_nominals := [];
  smt_type_defs := FEMPTY; smt_slots := [] |>``;
val keys = ``[["main"]]``;
val layouts = ``[(^address,([]:storage_layout,[]:storage_layout))]``;
fun input program : vyperCheckContractFrontendLib.source_input =
  {fuel=``80:num``,trust=trust,keys=keys,program=program,layouts=layouts,address=address};
fun audit th = let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
  if null (hyp th) andalso null axioms andalso
     List.all (fn s => s = "DISK_THM") oracles then ()
  else raise Fail "address/hex theorem has assumptions, axioms or oracles" end;
fun poison (JSON.OBJECT fields) = JSON.OBJECT
      (("type",JSON.STRING "not a compiler type") ::
       ("func_type",JSON.NULL) :: ("folded_value",JSON.OBJECT
         [("ast_type",JSON.STRING "Int"),("value",JSON.INT 777)]) ::
       map (fn (k,v) => (k,poison v))
         (List.filter (fn (k,_) => k <> "type" andalso k <> "func_type" andalso k <> "folded_value") fields))
  | poison (JSON.ARRAY xs) = JSON.ARRAY (map poison xs)
  | poison x = x;
fun original name = let
  val raw = JSONDecode.decodeFile JSONDecode.raw ("sourceAddressHexFixtures/" ^ name ^ ".json")
  val clean = JSONDecode.decode sourceSyntaxLib.annotated_ast raw
  val poisoned = JSONDecode.decode sourceSyntaxLib.annotated_ast (poison raw)
  val () = if aconv clean poisoned then () else raise Fail ("hex metadata dependency: " ^ name)
in (clean,poisoned) end;

val addr = ``BaseT AddressT``;
val b20 = ``BaseT (BytesT (Fixed 20))``;
val octets = ``[171w;205w;239w;171w;205w;239w;171w;205w;239w;171w;205w;239w;
  171w;205w;239w;171w;205w;239w;171w;205w]:word8 list``;
fun literal ty = ``Literal ^ty (BytesL ^octets)``;
fun conversion ty e = ``TypeBuiltin ^ty Convert ^ty [^e]``;
fun module params ty e = ``[(NONE:num option,[FunctionDecl External Pure F F "f" ^params [] ^ty
  [Return (SOME ^e)]])]``;
val no_params = ``[]:(string # type) list``;
fun constant_module cty ty = ``[(NONE:num option,
  [VariableDecl Private (Constant (Literal ^cty (BytesL (REPLICATE 20 0w)))) "C" ^cty NONE;
   FunctionDecl External Pure F F "f" [] [] ^ty
    [Return (SOME (TypeBuiltin ^ty Convert ^ty [Literal ^cty (BytesL (REPLICATE 20 0w))]))]])]``;
val valid =
  [("address_bytes20",module ``[("a",^addr)]`` b20 (conversion b20 ``Name ^addr "a"``)),
   ("bytes20_address",module ``[("a",^b20)]`` addr (conversion addr ``Name ^b20 "a"``)),
   ("address_checksum",module no_params addr (literal addr)),
   ("address_zero",module no_params addr ``Literal ^addr (BytesL (REPLICATE 20 0w))``),
   ("bytes20_lower",module no_params b20 (literal b20)),
   ("bytes20_upper",module no_params b20 (literal b20)),
   ("convert_checksum",module no_params b20 (conversion b20 (literal addr))),
   ("convert_lower_address",module no_params addr (conversion addr (literal b20))),
   ("constant_bytes20_address",constant_module b20 addr),
   ("constant_address_bytes20",constant_module addr b20)];

fun check (name,expected) = let
  val (program,poisoned) = original name
  val checked = vyperCheckContractFrontendLib.Source.check_contract_result (input program)
  val public = vyperCheckContractFrontendLib.Source.check_contract (input poisoned)
  val actual = #modules (#elaboration checked)
  val () = if aconv (rhs (concl (EVAL actual))) (rhs (concl (EVAL expected))) then ()
    else raise Fail ("address/hex exact module mismatch: " ^ name ^ "\nactual: " ^
      term_to_string (rhs (concl (EVAL actual))) ^ "\nexpected: " ^
      term_to_string (rhs (concl (EVAL expected))))
  val exact = prove (``source_module_elaborate_simple 80 ^trust ^keys ^program =
      SM_Ok (SourceRetained ^program ^expected)``,
    CONV_TAC (LAND_CONV (REWR_CONV (#equation (#elaboration checked)))) >> EVAL_TAC)
  val () = app audit [exact,#checking checked,#composition checked,public]
  val () = if aconv (concl public) (concl (#checking checked)) then ()
    else raise Fail ("poisoned Source.check_contract mismatch: " ^ name)
  val _ = save_thm (name ^ "_exact_source_module",exact)
  val _ = save_thm (name ^ "_source_check",#checking checked)
  val _ = save_thm (name ^ "_source_composition",#composition checked)
  val _ = save_thm (name ^ "_poisoned_source_check",public)
in () end;
val () = app check valid;

(* No legacy fallback: all eight pin-invalid ORIGINAL trees fail Source itself. *)
val () = app (fn name => let
  val (program,_) = original name
  val equation = EVAL ``source_module_elaborate_simple 80 ^trust ^keys ^program``
  val expected = ``SM_Error (SME_Constant SCErr_Type):
    (num option # toplevel list) list source_retained source_module_result``
  val () = if aconv (rhs (concl equation)) expected then ()
    else raise Fail ("address/hex rejection mismatch: " ^ name ^ "\n" ^ term_to_string (rhs (concl equation)))
  val () = audit equation
  val _ = save_thm (name ^ "_source_reject",equation)
in () end) ["address_bad_checksum","bytes20_mixed","address_short","bytes20_short",
           "convert_same_address","convert_same_bytes20",
           "constant_same_address","constant_same_bytes20"];

(* The ordinary compatible compiler AST from #600 is exactly the Source AST,
   not merely a second successful artifact. Both legacy modes still accept. *)
val expected = #2 (hd valid);
val () = app (fn deploy => let
  val ordinary = vyperCheckContractFrontendLib.check_contract_file_legacy
    {in_deploy=deploy,address=address,path="fixtures/check_contract/address_bytes20.json"}
  val modules = List.last (#2 (strip_comb (lhs (concl ordinary))))
  val () = if aconv modules expected then () else raise Fail "ordinary/source address_bytes20 AST mismatch"
  val () = audit ordinary
  val _ = save_thm (if deploy then "address_bytes20_ordinary_deploy" else "address_bytes20_ordinary_runtime",ordinary)
in () end) [false,true];
