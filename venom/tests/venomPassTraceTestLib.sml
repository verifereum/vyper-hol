structure venomPassTraceTestLib = struct

open HolKernel boolLib bossLib
     listSyntax pairSyntax stringSyntax
     venomIRJsonLib

type pass_spec =
  {name: string,
   uses_hints: bool,
   transform_tm: term,
   subst_tm: term option}

val operand_ty = mk_thy_type{Thy="venomState",Tyop="operand",Args=[]}
val hint_ty = mk_thy_type{Thy="algebraicOptTransform",Tyop="opt_hint",Args=[]}
val hint_pair_ty = pairSyntax.mk_prod(numSyntax.num, hint_ty)
val subst_pair_ty = pairSyntax.mk_prod(string_ty, operand_ty)

fun pass_theory name =
  case name of
    "algebraic_optimization" => "algebraicOptTransform"
  | _ => raise Fail ("unknown pass: " ^ name)

fun mk_pass_spec name =
  case name of
    "algebraic_optimization" =>
      let
        val thy = pass_theory name
        val transform_tm = prim_mk_const{Thy=thy,Name="transform_function_hints"}
        val subst_tm = SOME (prim_mk_const{Thy=thy,Name="subst_function_op"})
      in
        {name=name, uses_hints=true, transform_tm=transform_tm, subst_tm=subst_tm}
      end
  | _ => raise Fail ("unknown pass: " ^ name)

fun apply_transform (spec: pass_spec) hints_tm before_fn =
  if #uses_hints spec then
    list_mk_comb(#transform_tm spec, [hints_tm, before_fn])
  else
    mk_comb(#transform_tm spec, before_fn)

fun apply_subst (spec: pass_spec) subst_tm transformed =
  case #subst_tm spec of
    NONE => transformed
  | SOME fn_tm => list_mk_comb(fn_tm, [subst_tm, transformed])

fun check_one (spec: pass_spec) (name, before_fn, after_fn, hints, subst_tm) =
  let
    val hints_tm = mk_list(hints, hint_pair_ty)
    val transformed = apply_transform spec hints_tm before_fn
    val applied = apply_subst spec subst_tm transformed
    val eq_tm = mk_eq(applied, after_fn)
    val eq_thm = EVAL eq_tm
  in
    if aconv (rhs (concl eq_thm)) boolSyntax.T then ()
    else print ("[mismatch] " ^ name ^ "\n")
  end

fun check_export (spec: pass_spec) path =
  let
    val pairs = decode_export_file path
  in
    List.app (check_one spec) pairs
  end

fun list_json_files dir =
  let
    val d = OS.FileSys.openDir dir
    fun loop acc =
      case OS.FileSys.readDir d of
        NONE => acc
      | SOME entry =>
          let
            val path = OS.Path.concat(dir, entry)
            val acc' =
              if OS.FileSys.isDir path then loop (list_json_files path @ acc)
              else if String.isSuffix ".json" entry then path :: acc
              else acc
          in
            loop acc'
          end
    val files = loop []
    val () = OS.FileSys.closeDir d
  in
    files
  end

fun list_subdirs dir =
  let
    val d = OS.FileSys.openDir dir
    fun loop acc =
      case OS.FileSys.readDir d of
        NONE => acc
      | SOME entry =>
          let
            val path = OS.Path.concat(dir, entry)
            val acc' =
              if OS.FileSys.isDir path then path :: acc
              else acc
          in
            loop acc'
          end
    val dirs = loop []
    val () = OS.FileSys.closeDir d
  in
    dirs
  end

fun check_export_dir (spec: pass_spec) dir =
  let
    val files = list_json_files dir
  in
    List.app (check_export spec) files
  end

fun check_export_root dir =
  let
    fun run_dir path =
      let
        val pass_name = OS.Path.file path
      in
        case (SOME (mk_pass_spec pass_name) handle Fail _ => NONE) of
          NONE => print ("[skip] unknown pass: " ^ pass_name ^ "\n")
        | SOME spec => check_export_dir spec path
      end
  in
    List.app run_dir (list_subdirs dir)
  end

end
