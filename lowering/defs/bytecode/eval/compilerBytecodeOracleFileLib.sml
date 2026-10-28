(* TOP-LEVEL: read_hex_bytes -- use the shared parser on a declared file path. *)
structure compilerBytecodeOracleFileLib = struct
  fun read_hex_bytes path = let
    val () = if OS.FileSys.access (path,[OS.FileSys.A_READ]) then ()
      else raise Fail ("missing declared bytecode oracle " ^ path ^
        " from " ^ OS.FileSys.getDir ())
    val entries = List.mapPartial evalCompilerBytecodeLib.fixture_line
      (String.tokens (fn c => c = #"\n" orelse c = #"\r")
        (evalCompilerBytecodeLib.read_all path))
    val deploy = evalCompilerBytecodeLib.bytecode_fixture_value path entries "deploy"
    val runtime = evalCompilerBytecodeLib.bytecode_fixture_value path entries "runtime"
  in pairSyntax.mk_pair
    (evalCompilerBytecodeLib.hex_bytes_tm deploy,
     evalCompilerBytecodeLib.hex_bytes_tm runtime)
  end
end
