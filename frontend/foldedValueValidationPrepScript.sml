Theory foldedValueValidationPrep
Ancestors vyperCheckContractFrontendLibTest vyperCheckContractLibTest

(* Local preparation only: these source files are NOT independent oracle data.
   Include the complete inventory in the build key, and fail on missing files,
   duplicate names or an accidental source/manifest divergence. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../lowering/defs/bytecode/folded-value-sources",
   "../lowering/defs/bytecode/folded-value-witnesses.txt",
   "../lowering/defs/bytecode/folded-value-parity-fixtures.txt"]
val prep_root = "../lowering/defs/bytecode/";
val prep_manifest = TextIO.openIn (prep_root ^ "folded-value-witnesses.txt");
fun prep_lines stream =
  case TextIO.inputLine stream of
    NONE => []
  | SOME line => String.tokens Char.isSpace line @ prep_lines stream;
val prep_names = prep_lines prep_manifest;
val () = TextIO.closeIn prep_manifest;
val () = if length prep_names = 37 andalso
    length (Lib.mk_set prep_names) = 37 then ()
  else raise Fail "fold validation manifest must enumerate 37 distinct witnesses";
val prep_parity_stream = TextIO.openIn (prep_root ^ "folded-value-parity-fixtures.txt");
val prep_parity = prep_lines prep_parity_stream;
val () = TextIO.closeIn prep_parity_stream;
val () = if length prep_parity = 7 andalso Lib.set_eq prep_parity
    ["fold_add", "pow_folded_exp", "fold_cmp", "enc_mid_const",
     "fold_powmod", "fold_addmod", "fold_abs"] andalso
    List.all (fn name => Lib.mem name prep_names) prep_parity then ()
  else raise Fail "required seven parity fixture sources are not prepared";
val prep_dir = OS.FileSys.openDir (prep_root ^ "folded-value-sources");
fun prep_entries dir =
  case OS.FileSys.readDir dir of NONE => [] | SOME s => s :: prep_entries dir;
val prep_files = prep_entries prep_dir;
val () = OS.FileSys.closeDir prep_dir;
val () = if Lib.set_eq prep_files (map (fn s => s ^ ".vy") prep_names) then ()
  else raise Fail "fold validation source inventory differs from manifest";
val () = app (fn name => let
    val stream = TextIO.openIn (prep_root ^ "folded-value-sources/" ^ name ^ ".vy")
    val content = TextIO.inputAll stream
    val () = TextIO.closeIn stream
  in if String.isSubstring "@external" content then ()
     else raise Fail ("missing external witness entry point: " ^ name) end) prep_names;

(* Audit every inherited test theorem, including the folded translation and
   malformed ABI/MethodId rejection probes. A cache hit is not a tag audit. *)
val () = app (fn theory => app (fn (name, th) =>
    if null (List.filter (fn oracle => oracle <> "DISK_THM")
      (#1 (Tag.dest_tag (Thm.tag th)))) then ()
    else raise Fail ("validation test depends on oracle: " ^ theory ^ "." ^ name))
    (DB.thms theory))
  ["vyperCheckContractFrontendLibTest", "vyperCheckContractLibTest"];
