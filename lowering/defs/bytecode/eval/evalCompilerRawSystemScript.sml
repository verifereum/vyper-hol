(* Every retained raw-system fixture has an exact Python parity theorem. *)
Theory evalCompilerRawSystem
Ancestors
  evalCompilerRawSystem1 evalCompilerRawSystem2
Libs
  evalCompilerBytecodeLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../raw-system/parity-fixtures.txt"]

val suffix = "_matches_python_oracle"
val checked_names = List.concat (map DB.theorems
  ["evalCompilerRawSystem1", "evalCompilerRawSystem2"])
  |> map #1
  |> List.filter (String.isSuffix suffix)
  |> map (fn name => String.substring (name, 0, size name - size suffix))
val listed_names = evalCompilerBytecodeLib.read_all "../raw-system/parity-fixtures.txt"
  |> String.tokens (fn c => c = #"\n" orelse c = #"\r")
  |> map evalCompilerBytecodeLib.strip_comment
  |> List.filter (fn name => name <> "")
val ordered = Lib.sort (fn a => fn b => String.compare (a, b) = LESS)
val () = if ordered checked_names = ordered listed_names then ()
  else raise Fail ("raw-system parity manifest differs from checked fixtures: listed=" ^
    String.concatWith "," (ordered listed_names) ^ "; checked=" ^
    String.concatWith "," (ordered checked_names))

