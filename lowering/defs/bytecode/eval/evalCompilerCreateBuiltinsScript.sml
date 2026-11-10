(* Every retained creation fixture has an exact Python parity theorem.
   Reuse the compiler certificates already needed by creation execution tests. *)
Theory evalCompilerCreateBuiltins
Ancestors
  evalCompilerCreateBuiltins1 evalCompilerCreateBuiltins2
  createProxyCompileTest createCopyCompileTest createBlueprintCompileTest
Libs
  evalCompilerBytecodeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../create-builtins"]

Theorem cp01_proxy_matches_python_oracle:
  ^(lhs (concl create_proxy_compiled)) =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes_from
      "../create-builtins/oracle/cp01_proxy.hex")
Proof
  CONV_TAC (LAND_CONV (K create_proxy_compiled)) >> EVAL_TAC
QED

Theorem cc01_copy_matches_python_oracle:
  ^(lhs (concl create_copy_compiled)) =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes_from
      "../create-builtins/oracle/cc01_copy.hex")
Proof
  CONV_TAC (LAND_CONV (K create_copy_compiled)) >> EVAL_TAC
QED

Theorem cb01_blueprint_matches_python_oracle:
  ^(lhs (concl create_blueprint_compiled)) =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes_from
      "../create-builtins/oracle/cb01_blueprint.hex")
Proof
  CONV_TAC (LAND_CONV (K create_blueprint_compiled)) >> EVAL_TAC
QED

val suffix = "_matches_python_oracle"
val checked_names = List.concat (map DB.theorems
  ["evalCompilerCreateBuiltins1", "evalCompilerCreateBuiltins2", "evalCompilerCreateBuiltins"])
  |> map #1
  |> List.filter (String.isSuffix suffix)
  |> map (fn name => String.substring (name, 0, size name - size suffix))
val listed_names = evalCompilerBytecodeLib.read_all "../create-builtins/parity-fixtures.txt"
  |> String.tokens (fn c => c = #"\n" orelse c = #"\r")
  |> map evalCompilerBytecodeLib.strip_comment
  |> List.filter (fn name => name <> "")
val ordered = Lib.sort (fn a => fn b => String.compare (a, b) = LESS)
val () = if ordered checked_names = ordered listed_names then ()
  else raise Fail ("create-builtins parity manifest differs from checked fixtures: listed=" ^
    String.concatWith "," (ordered listed_names) ^ "; checked=" ^
    String.concatWith "," (ordered checked_names))

