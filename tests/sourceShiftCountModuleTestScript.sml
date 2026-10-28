Theory sourceShiftCountModuleTest
Ancestors
  sourceShiftCountTest sourceModuleElaborate sourceModuleDefs sourceSyntax
  vyperTypeContract vyperAST finite_map
Libs
  sourceModuleFrontendLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["sourceShiftCountFixtures"];

val address = ``0w : address``;
val trust = ``<| smt_ids := [(["main"],NONE)]; smt_nominals := [];
  smt_type_defs := FEMPTY; smt_slots := [] |> : source_module_trust``;
val layouts = ``[(^address,([]:storage_layout,[]:storage_layout))]``;
val bound_expected = ``[(NONE,[
  VariableDecl Private (Constant (Literal (BaseT (UintT 256)) (IntL 3)))
    "N" (BaseT (UintT 256)) NONE;
  FunctionDecl External Pure F F "power"
    [("x",BaseT (UintT 256));("values",ArrayT (BaseT (UintT 256)) (Fixed 3))] []
    (BaseT (UintT 256)) [Return (SOME (Builtin (BaseT (UintT 256)) (Bop Exp)
      [Name (BaseT (UintT 256)) "x";Literal (BaseT (UintT 256)) (IntL 3)]))]])]
  : (num option # toplevel list) list``;
val shift_expected = ``[(NONE,[
  VariableDecl Private (Constant (Literal (BaseT (UintT 256)) (IntL 2)))
    "N" (BaseT (UintT 256)) NONE;
  VariableDecl Private (Constant (Literal (BaseT (IntT 256)) (IntL (-4))))
    "M" (BaseT (IntT 256)) NONE;
  FunctionDecl External Pure F F "left"
    [("x",BaseT (IntT 256));("n",BaseT (UintT 8));
     ("values",ArrayT (BaseT (UintT 256)) (Fixed 2))] [] (BaseT (IntT 256))
    [Return (SOME (Builtin (BaseT (IntT 256)) (Bop ShL)
      [Name (BaseT (IntT 256)) "x";Name (BaseT (UintT 8)) "n"]))];
  FunctionDecl External Pure F F "right"
    [("x",BaseT (IntT 256));("n",BaseT (UintT 256))] [] (BaseT (IntT 256))
    [Return (SOME (Builtin (BaseT (IntT 256)) (Bop ShR)
      [Name (BaseT (IntT 256)) "x";Name (BaseT (UintT 256)) "n"]))];
  FunctionDecl External Pure F F "count_expression"
    [("x",BaseT (IntT 256));("n",BaseT (UintT 8))] [] (BaseT (IntT 256))
    [Return (SOME (Builtin (BaseT (IntT 256)) (Bop ShR)
      [Name (BaseT (IntT 256)) "x";Builtin (BaseT (UintT 8)) (Bop Add)
        [Literal (BaseT (UintT 8)) (IntL 1);Name (BaseT (UintT 8)) "n"]]))]])]
  : (num option # toplevel list) list``;
fun audit th = let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
  if null (hyp th) andalso null axioms andalso
     List.all (fn s => s = "DISK_THM") oracles then ()
  else raise Fail "source shift module theorem has assumptions/axioms/oracles" end;
fun poison (JSON.OBJECT fields) = JSON.OBJECT
    (List.map (fn key => (key,JSON.STRING "poisoned metadata"))
       ["folded_value","type","is_constant","is_immutable"] @
     List.map (fn (key,value) => (key,poison value))
       (List.filter (fn (key,_) => not (List.exists (fn k => k = key)
         ["folded_value","type","is_constant","is_immutable"])) fields))
  | poison (JSON.ARRAY xs) = JSON.ARRAY (List.map poison xs)
  | poison value = value;
fun check (name,expected) = let
  val json = JSONDecode.decodeFile JSONDecode.raw
    ("sourceShiftCountFixtures/" ^ name ^ ".json")
  val program = JSONDecode.decode sourceSyntaxLib.annotated_ast json
  val () = if aconv program (JSONDecode.decode sourceSyntaxLib.annotated_ast (poison json)) then ()
    else raise Fail ("shift source decoder consumed metadata: " ^ name)
  val checked = sourceModuleFrontendLib.check_simple
    {fuel=``80:num``,trust=trust,keys=``[["main"]]``,program=program}
    {layouts=layouts,address=address}
  val elab = #elaboration checked
  val () = if aconv (#modules elab) expected then ()
    else raise Fail ("source shift module AST mismatch: " ^ name ^ "\n" ^ term_to_string (#modules elab))
  val () = app audit [#equation elab,#original elab,#checking checked,#composition checked]
  val _ = save_thm (name ^ "_phase",#equation elab)
  val _ = save_thm (name ^ "_check",#checking checked)
  val _ = save_thm (name ^ "_composition",#composition checked)
in () end;
val () = app check [("constant_bound",bound_expected),("constant_shifts",shift_expected)];
