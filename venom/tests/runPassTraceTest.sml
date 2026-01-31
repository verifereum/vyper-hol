val cwd = OS.FileSys.getDir ();

fun isdir p = (OS.FileSys.isDir p) handle OS.SysErr _ => false;

val root =
  case OS.Process.getEnv "VYPER_HOL_ROOT" of
    SOME d => d
  | NONE =>
      let
        val parent = OS.Path.dir cwd
        val grand = OS.Path.dir parent
      in
        if isdir (OS.Path.concat (cwd, "venom")) then cwd
        else if isdir (OS.Path.concat (parent, "venom")) then parent
        else if isdir (OS.Path.concat (grand, "venom")) then grand
        else cwd
      end;

val verifereum_root =
  case OS.Process.getEnv "VERIFEREUM_ROOT" of
    SOME d => d
  | NONE => OS.Path.concat (OS.Path.dir root, "verifereum");

fun pjoin a b = OS.Path.concat (a, b);

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

val pass_root = pjoin root "venom/passes";
val pass_dirs = if isdir pass_root then list_subdirs pass_root else [];

val _ = loadPath :=
  [pjoin root ".hol/objs",
   pjoin verifereum_root "util/.hol/objs",
   pjoin verifereum_root "spec/.hol/objs",
   pjoin root "venom/.hol/objs",
   pjoin root "venom/tests/.hol/objs",
   pjoin root "venom",
   pass_root] @ pass_dirs @ !loadPath;

val _ = load "vfmTypesTheory";
val _ = load "vfmStateTheory";

val _ = load "venomStateTheory";
val _ = load "venomInstTheory";
val _ = load "algebraicOptTransformTheory";

val _ = load "stringSyntax";
val _ = load "wordsLib";
val _ = load "wordsSyntax";
val _ = load "vfmTypesSyntax";
val _ = load "byteStringCacheLib";
val _ = load "intSyntax";

use (pjoin root "venom/tests/venomIRJsonLib.sml");
use (pjoin root "venom/tests/venomPassTraceTestLib.sml");

open venomPassTraceTestLib;

val pass_filter = OS.Process.getEnv "VENOM_PASS";

fun ensure_pass_loaded name =
  let
    val thy = pass_theory name
  in
    if thy = "algebraicOptTransform" then ()
    else load (thy ^ "Theory")
  end;

fun run_export_root dir =
  let
    fun run_dir path =
      let
        val pass_name = OS.Path.file path
      in
        case (SOME (pass_theory pass_name) handle Fail _ => NONE) of
          NONE => print ("[skip] unknown pass: " ^ pass_name ^ "\n")
        | SOME _ =>
            let
              val _ = ensure_pass_loaded pass_name
              val spec = mk_pass_spec pass_name
            in
              check_export_dir spec path
            end
      end
  in
    List.app run_dir (list_subdirs dir)
  end;

val export_root = pjoin root "venom/tests/venom-ir-export";
val export_dir =
  case OS.Process.getEnv "VENOM_TRACE_EXPORT" of
    SOME d => d
  | NONE => export_root;

val _ =
  if OS.FileSys.isDir export_dir then
    case pass_filter of
      SOME p =>
        let
          val pass_dir = pjoin export_dir p
          val _ = ensure_pass_loaded p
          val spec = mk_pass_spec p
        in
          check_export_dir spec pass_dir
        end
    | NONE => run_export_root export_dir
  else
    print ("[skip] missing export dir: " ^ export_dir ^ "\n");

val _ = OS.Process.exit OS.Process.success;
