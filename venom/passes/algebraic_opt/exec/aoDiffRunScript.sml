(*
 * Differential-test runner for the algebraic-optimization pass.
 *
 * For every JSON file produced by diff/ao_diff.py (in diff/out/), this script
 * imports the "before" Venom function, runs `ao_transform_function` via EVAL,
 * and checks the result against the imported "after" function modulo internal
 * instruction ids (strip_inst_ids).  A mismatch means the HOL pass and the
 * Python pass disagree on this input — i.e. a bug — and fails the build loudly.
 *
 * This is a build-time test: it defines no theory content of interest.
 *)

Theory aoDiffRun
Ancestors
  aoExec venomInst venomState
Libs
  wordsLib

open JSONDecode

(* holbuild statically scans for `holbuild_extra_deps ["lit", ...]` (literal
 * strings only) and copies each listed file into the build's staging dir at
 * the same relative path, so the corpus JSON is readable at run time.  Keep
 * this list in sync with the files under diff/out/.  The function itself is a
 * no-op marker. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["diff/out/peephole_basic.json", "diff/out/cmp_flip.json"]

(* ---- opcode string (Python, lowercase) -> HOL opcode constructor ---- *)
fun hol_opcode_name s =
  case s of
    "div" => "Div"
  | "mod" => "Mod"
  | "exp" => "Exp"
  | _ => String.implode (List.map Char.toUpper (String.explode s))

fun opcode_tm s =
  prim_mk_const{Thy = "venomInst", Name = hol_opcode_name s}
  handle _ => raise Fail ("ao_diff: unmodeled opcode " ^ s)

(* ---- operand terms ---- *)
fun mk_var_tm s = “Var ^(stringSyntax.fromMLstring s)”
fun mk_label_tm s = “Label ^(stringSyntax.fromMLstring s)”
fun mk_lit_tm s =
  let
    val n = Arbnum.fromString s
            handle _ => raise Fail ("ao_diff: bad literal " ^ s)
  in
    “Lit (n2w ^(numSyntax.mk_numeral n))”
  end

val operand_ty = “:operand”
val instruction_ty = “:instruction”
val basic_block_ty = “:basic_block”

val operand_dec : term decoder =
  choose [
    JSONDecode.map mk_var_tm (field "var" string),
    JSONDecode.map mk_lit_tm (field "lit" string),
    JSONDecode.map mk_label_tm (field "label" string)
  ]

(* raw instruction: (opcode_tm, operand-list term, output-list term) *)
val inst_raw_dec : (term * term * term) decoder =
  tuple3 (
    field "opcode" (JSONDecode.map opcode_tm string),
    field "operands"
      (JSONDecode.map (fn ops => listSyntax.mk_list (ops, operand_ty))
                      (array operand_dec)),
    field "outputs"
      (JSONDecode.map (fn ss => listSyntax.mk_list (ss, stringSyntax.string_ty))
                      (array (JSONDecode.map stringSyntax.fromMLstring string))))

val bb_raw_dec : (string * (term * term * term) list) decoder =
  tuple2 (field "label" string, field "instructions" (array inst_raw_dec))

val fn_raw_dec : (string * (string * (term * term * term) list) list) decoder =
  tuple2 (field "name" string, field "blocks" (array bb_raw_dec))

fun build_inst id (opc, ops_tm, outs_tm) =
  let val idtm = numSyntax.mk_numeral (Arbnum.fromInt id) in
    “<| inst_id := ^idtm; inst_opcode := ^opc;
        inst_operands := ^ops_tm; inst_outputs := ^outs_tm |> : instruction”
  end

(* assign sequential, distinct inst ids across the whole function *)
fun build_fn (name, blocks) =
  let
    val ctr = ref 0
    fun next () = let val v = !ctr in ctr := v + 1; v end
    fun build_bb (label, raws) =
      let val insts = List.map (fn r => build_inst (next ()) r) raws in
        “<| bb_label := ^(stringSyntax.fromMLstring label);
            bb_instructions := ^(listSyntax.mk_list (insts, instruction_ty)) |>
           : basic_block”
      end
    val bbs = List.map build_bb blocks
  in
    “<| fn_name := ^(stringSyntax.fromMLstring name);
        fn_blocks := ^(listSyntax.mk_list (bbs, basic_block_ty)) |> : ir_function”
  end

(* a record is {name, before, after}; build (name, before_tm, after_tm) *)
val record_dec : (string * term * term) decoder =
  map3 (fn (nm, b, a) => (nm, build_fn b, build_fn a))
       (field "name" string, field "before" fn_raw_dec, field "after" fn_raw_dec)

(* a file holds either one record or a JSON array of records *)
val file_dec : (string * term * term) list decoder =
  orElse (array record_dec, JSONDecode.map (fn r => [r]) record_dec)

(* ---- run + compare ---- *)
fun normalize tm = rhs (concl (EVAL tm))

fun check_one (name, before_tm, after_tm) =
  let
    val got = normalize “strip_inst_ids (ao_transform_function ^before_tm)”
    val exp = normalize “strip_inst_ids ^after_tm”
  in
    if aconv got exp then (print ("  PASS  " ^ name ^ "\n"); true)
    else (
      print ("  FAIL  " ^ name ^ "\n");
      print ("    HOL produced : " ^ Parse.term_to_string got ^ "\n");
      print ("    Python after : " ^ Parse.term_to_string exp ^ "\n");
      false)
  end

fun first_existing_dir [] = NONE
  | first_existing_dir (d :: ds) =
      if (OS.FileSys.isDir d handle _ => false) then SOME d else first_existing_dir ds

fun json_files dir =
  let
    val ds = OS.FileSys.openDir dir
    fun loop acc =
      case OS.FileSys.readDir ds of
        NONE => acc
      | SOME f =>
          loop (if String.isSuffix ".json" f
                then OS.Path.concat (dir, f) :: acc else acc)
    val fs = loop []
  in
    OS.FileSys.closeDir ds; List.rev fs
  end

val () =
  let
    val dir =
      case first_existing_dir
             ["diff/out", "venom/passes/algebraic_opt/exec/diff/out"] of
        SOME d => d
      | NONE => raise Fail "ao_diff: no diff/out corpus directory found"
    val files = json_files dir
    val results =
      List.concat (List.map (fn path =>
        let val recs = decodeFile file_dec path in
          print ("== " ^ path ^ " ==\n"); List.map check_one recs
        end) files)
    val nfail = List.length (List.filter not results)
  in
    print ("\nao differential: " ^ Int.toString (List.length results)
           ^ " checked, " ^ Int.toString nfail ^ " failed\n");
    if nfail = 0 then ()
    else raise Fail ("ao differential: " ^ Int.toString nfail ^ " mismatch(es)")
  end
