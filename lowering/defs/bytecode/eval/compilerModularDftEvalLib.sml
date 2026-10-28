(* Prepare the real DFT block analyses separately for the modular fixture. *)
structure compilerModularDftEvalLib = struct
  open HolKernel boolLib
  val prepared = ref ([] : term list)
  val active = ref (NONE : term option)
  val stage = ref 0

  fun configure () =
    app (fn (name,arity) => evalCompilerBytecodeLib.ensure_certificate_head
      (prim_mk_const {Thy="dftDefs",Name=name}) arity)
      [("build_eda",1),("build_offspring_map",2),("entry_instructions",3),
       ("schedule_from_entries",5)]

  fun warm_call root goal =
    case !compilerDftEvalLib.pending of
      current::_ => if same_const (fst(strip_comb current)) compilerDftEvalLib.block_head
          andalso not(List.exists (aconv current) (!prepared)) then let
        val () = if Option.isSome(!active) andalso aconv (valOf(!active)) current then ()
          else (active := SOME current; stage := 0)
        val [order,bb] = snd(strip_comb current)
        val instructions = ``(^bb).bb_instructions``
        val eda = ``build_eda ^instructions``
        val offspring = ``build_offspring_map ^instructions ^order``
        val entries = ``entry_instructions ^instructions ^order ^eda``
        val calls = [eda,offspring,entries,
          ``schedule_from_entries ^instructions ^order ^eda ^offspring ^entries``]
        val result = evalCompilerBytecodeLib.prepare_closed_call (List.nth(calls,!stage)) goal
        val () = stage := !stage + 1
        val () = if !stage = length calls then prepared := current :: !prepared else ()
      in result end
      else compilerDftEvalLib.warm_call root goal
    | [] => compilerDftEvalLib.warm_call root goal
end
