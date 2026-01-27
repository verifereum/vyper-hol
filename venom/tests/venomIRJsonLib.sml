structure venomIRJsonLib = struct

open HolKernel boolLib bossLib
     listSyntax stringSyntax optionSyntax pairSyntax
     wordsLib wordsSyntax
     vfmTypesSyntax byteStringCacheLib
open JSONDecode

(* Types *)
val operand_ty = mk_thy_type{Thy="venomState",Tyop="operand",Args=[]}
val opcode_ty = mk_thy_type{Thy="venomInst",Tyop="opcode",Args=[]}
val instruction_ty = mk_thy_type{Thy="venomInst",Tyop="instruction",Args=[]}
val basic_block_ty = mk_thy_type{Thy="venomInst",Tyop="basic_block",Args=[]}
val function_ty = mk_thy_type{Thy="venomInst",Tyop="ir_function",Args=[]}
val opt_hint_ty = mk_thy_type{Thy="algebraicOptTransform",Tyop="opt_hint",Args=[]}

(* Constructors *)
val Lit_tm = prim_mk_const{Thy="venomState",Name="Lit"}
val Var_tm = prim_mk_const{Thy="venomState",Name="Var"}
val Label_tm = prim_mk_const{Thy="venomState",Name="Label"}

fun opcode_const s = prim_mk_const{Thy="venomInst",Name=s}

(* JSON helpers *)
val numOfLargeInt =
  intSyntax.dest_injected o
  intSyntax.term_of_int o
  Arbint.fromLargeInt

val numtm = JSONDecode.map numOfLargeInt intInf
val stringtm = JSONDecode.map fromMLstring string
val booltm = JSONDecode.map mk_bool bool

fun decode_operand_obj obj =
  case obj of
      [("lit", v)] =>
        mk_comb(Lit_tm, bytes32_from_hex (decode string v))
    | [("var", v)] =>
        mk_comb(Var_tm, decode stringtm v)
    | [("label", v)] =>
        mk_comb(Label_tm, decode stringtm v)
    | _ => raise Fail "operand"

val operand : term decoder = JSONDecode.map decode_operand_obj rawObject

val operands : term decoder =
  JSONDecode.map (fn ls => mk_list(ls, operand_ty)) (array operand)

val outputs : term decoder =
  JSONDecode.map (fn ls => mk_list(ls, string_ty)) (array stringtm)

val opcode : term decoder =
  JSONDecode.map opcode_const string

fun mk_hint (p,t,c) =
  TypeBase.mk_record (opt_hint_ty, [
    ("prefer_iszero", p),
    ("is_truthy", t),
    ("cmp_flip", c)
  ])

val hint : term decoder =
  JSONDecode.map mk_hint
    (tuple3 (field "prefer_iszero" booltm,
             field "is_truthy" booltm,
             field "cmp_flip" booltm))

fun mk_instruction (id, opc, ops, outs) =
  TypeBase.mk_record (instruction_ty, [
    ("inst_id", id),
    ("inst_opcode", opc),
    ("inst_operands", ops),
    ("inst_outputs", outs)
  ])

val instruction : term decoder =
  JSONDecode.map (fn (id,opc,ops,outs) => mk_instruction (id,opc,ops,outs))
    (tuple4 (field "id" numtm,
             field "opcode" opcode,
             field "operands" operands,
             field "outputs" outputs))

val instruction_with_hint : (term * term) decoder =
  JSONDecode.map (fn ((id,opc,ops,outs),h) =>
    (mk_instruction (id,opc,ops,outs), mk_pair (id, h)))
    (tuple2 (tuple4 (field "id" numtm,
                     field "opcode" opcode,
                     field "operands" operands,
                     field "outputs" outputs),
             field "hints" hint))

val instructions : term decoder =
  JSONDecode.map (fn ls => mk_list(ls, instruction_ty)) (array instruction)

val instructions_with_hints : (term list * term list) decoder =
  JSONDecode.map (fn ls =>
    (List.map #1 ls, List.map #2 ls)) (array instruction_with_hint)

fun mk_basic_block (lbl, insts) =
  TypeBase.mk_record (basic_block_ty, [
    ("bb_label", lbl),
    ("bb_instructions", insts)
  ])

val basic_block : term decoder =
  JSONDecode.map mk_basic_block
    (tuple2 (field "label" stringtm,
             field "instructions" instructions))

val basic_block_with_hints : (term * term list) decoder =
  JSONDecode.map (fn (lbl, (insts, hints)) =>
    (mk_basic_block (lbl, mk_list(insts, instruction_ty)), hints))
    (tuple2 (field "label" stringtm,
             field "instructions" instructions_with_hints))

val blocks : term decoder =
  JSONDecode.map (fn ls => mk_list(ls, basic_block_ty)) (array basic_block)

val blocks_with_hints : (term list * term list) decoder =
  JSONDecode.map (fn ls =>
    (List.map #1 ls, List.concat (List.map #2 ls))) (array basic_block_with_hints)

fun mk_function (name, bbs) =
  TypeBase.mk_record (function_ty, [
    ("fn_name", name),
    ("fn_blocks", bbs)
  ])

val function : term decoder =
  JSONDecode.map mk_function
    (tuple2 (field "name" stringtm,
             field "blocks" blocks))

val function_with_hints : (term * term list) decoder =
  JSONDecode.map (fn (name, (bbs, hints)) =>
    (mk_function (name, mk_list(bbs, basic_block_ty)), hints))
    (tuple2 (field "name" stringtm,
             field "blocks" blocks_with_hints))

val iszero_subst_entry : term decoder =
  JSONDecode.map (fn (v,opr) => mk_pair (v, opr))
    (tuple2 (field "var" stringtm,
             field "operand" operand))

val iszero_subst : term decoder =
  JSONDecode.map (fn ls => mk_list(ls, pairSyntax.mk_prod (string_ty, operand_ty)))
    (array iszero_subst_entry)

val function_pair : (string * term * term * term list * term) decoder =
  JSONDecode.map (fn (nm,(b,hints),a,subst) => (nm,b,a,hints,subst))
    (tuple4 (field "name" string,
             field "before" function_with_hints,
             field "after" function,
             field "iszero_subst" iszero_subst))

val function_pairs : (string * term * term * term list * term) list decoder =
  field "functions" (array function_pair)

fun decode_export_file path =
  decodeFile function_pairs path

end
