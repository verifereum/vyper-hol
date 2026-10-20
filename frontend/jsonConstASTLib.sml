structure jsonConstASTLib :> jsonConstASTLib = struct

open HolKernel boolLib JSONDecode

fun check decoder predicate message next =
  andThen decoder (fn x => if predicate x then next else fail message)

fun node kind = check (field "ast_type" string) (fn s => s = kind)
  ("constant frontend: expected " ^ kind)

fun construct thy name args =
  list_mk_comb (prim_mk_const {Thy = thy, Name = name}, args)
fun raw name args = construct "jsonConstAST" name args
fun expr name args = construct "jsonAST" name args
val no_type = expr "JT_None" []

(* Integer parsing only constructs a HOL literal; all evaluation happens in HOL. *)
val integer = JSONDecode.map
  (fn i => intSyntax.term_of_int (Arbint.fromLargeInt i)) intInf

val binop = andThen (field "ast_type" string) (fn op_name =>
  case List.find (fn (name,_) => name = op_name)
    [("Add", "Add"), ("Sub", "Sub"), ("Mult", "Mult"),
     ("FloorDiv", "FloorDiv"), ("Mod", "Mod"), ("Pow", "Pow"),
     ("BitAnd", "BitAnd"), ("BitOr", "BitOr"), ("BitXor", "BitXor"),
     ("LShift", "LShift"), ("RShift", "RShift")] of
    SOME (_, name) => succeed (expr ("JBop_" ^ name) [])
  | NONE => fail ("constant frontend: unsupported operator " ^ op_name))

(* Never read folded_value or inferred type, even on an original Name. *)
fun expression () : term decoder = choose [
  node "Int" (JSONDecode.map (fn i => expr "JE_Int" [i, no_type])
    (field "value" integer)),
  node "Name" (JSONDecode.map (fn name => expr "JE_Name"
    [stringSyntax.fromMLstring name, optionSyntax.mk_none stringSyntax.string_ty,
     expr "JMissingSource" [], no_type]) (field "id" string)),
  node "BinOp" (JSONDecode.map (fn (left,op_tm,right) =>
    expr "JE_BinOp" [left,op_tm,right,no_type])
    (tuple3 (field "left" (delay expression), field "op" binop,
             field "right" (delay expression))))]

fun integer_annotation name = let
  val signed = String.isPrefix "int" name
  val prefix = if signed then 3 else 4
  val digits = if signed orelse String.isPrefix "uint" name
               then String.extract (name, prefix, NONE) else ""
in
  if digits = "" orelse not (List.all Char.isDigit (String.explode digits))
  then fail ("constant frontend: unsupported type " ^ name)
  else case Int.fromString digits of
    NONE => fail ("constant frontend: invalid integer width " ^ name)
  | SOME bits => succeed (raw "CA_Integer"
      [numSyntax.term_of_int bits, boolSyntax.mk_bool signed])
end

fun annotation () : term decoder = choose [
  node "Name" (andThen (field "id" string) integer_annotation),
  node "Subscript" (JSONDecode.map (fn (element,bound) =>
      raw "CA_Array" [element,bound])
    (tuple2 (field "value" (delay annotation),
             field "slice" (delay expression))))]

val argument = JSONDecode.map (fn (name,ann) =>
  pairSyntax.mk_pair (stringSyntax.fromMLstring name,ann))
  (tuple2 (field "arg" string, field "annotation" (delay annotation)))

val single_return = andThen
  (array (node "Return" (field "value" (delay expression))))
  (fn [e] => succeed e
    | _ => fail "constant frontend: expected a single return statement")

val declaration : term decoder = choose [
  node "VariableDecl"
    (check (field "is_constant" bool) I
      "constant frontend: only constant variables are supported"
    (check (field "is_public" bool) not
      "constant frontend: public constant getters are unsupported"
    (JSONDecode.map (fn (name,ann,value) =>
    raw "CD_Constant" [stringSyntax.fromMLstring name,ann,value])
    (tuple3 (field "target" (node "Name" (field "id" string)),
             field "annotation" (delay annotation),
             field "value" (delay expression)))))),
  node "FunctionDef"
    (check (field "decorator_list" (array (node "Name" (field "id" string))))
      (fn names => names = ["external", "pure"] orelse
                   names = ["pure", "external"])
      "constant frontend: expected @external @pure"
    (check (field "args" (field "defaults" (array (delay expression)))) List.null
      "constant frontend: default arguments are unsupported"
    (JSONDecode.map (fn (name,args,ret,body) => raw "CD_Function"
      [stringSyntax.fromMLstring name,
       listSyntax.mk_list (args, pairSyntax.mk_prod (stringSyntax.string_ty,
         mk_thy_type {Thy="jsonConstAST", Tyop="const_annotation", Args=[]})),
       ret,body])
      (tuple4 (field "name" string, field "args" (field "args" (array argument)),
               field "returns" (delay annotation), field "body" single_return))))) ]

val annotated_ast =
  check (field "imports" (array JSONDecode.raw)) List.null
    "constant frontend: imports are unsupported"
    (field "ast" (node "Module"
      (check (field "settings" (fieldD "nonreentrancy_by_default" bool false)) not
        "constant frontend: default nonreentrancy is unsupported"
      (JSONDecode.map (fn decls => listSyntax.mk_list (decls,
        mk_thy_type {Thy="jsonConstAST", Tyop="const_declaration", Args=[]}))
        (field "body" (array declaration))))))

end
