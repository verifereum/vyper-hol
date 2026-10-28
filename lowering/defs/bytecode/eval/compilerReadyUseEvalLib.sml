(* Index unchanged variable-use equations and reuse the prepared function value. *)
structure compilerReadyUseEvalLib = struct
  open HolKernel boolLib
  fun use_head () =
    prim_mk_const {Thy="codegenReadyObservations",Name="var_single_use"}
  fun compare_calls (left,right) = let
    val la = snd (strip_comb left)
    val ra = snd (strip_comb right)
  in case Term.compare (List.nth (la,1),List.nth (ra,1)) of
      EQUAL => Term.compare (hd la,hd ra)
    | order => order
  end
  val equations = ref (Redblackmap.mkDict compare_calls : (term,thm) Redblackmap.dict)

  fun configure () =
    (evalCompilerBytecodeLib.ensure_certificate_head (use_head ()) 2;
     compilerSsaEvalLib.install_indexed_head equations (use_head (),2))

  fun warm_uses func context goal =
    case !compilerReadyEvalLib.uses_pending of
      SOME (saved,value,variables) =>
        if not (aconv saved func) then
          (compilerReadyEvalLib.uses_pending := NONE; Tactical.ALL_TAC goal)
        else (case variables of
          [] => compilerReadyCfgEvalLib.warm_context context goal
        | variable::rest => let
            val call = boolSyntax.list_mk_icomb (use_head (),[value,variable])
            val certificate = evalCompilerBytecodeLib.timed_evaluation (use_head ())
              "indexed variable check" (fn () => computeLib.EVAL_CONV call)
            val () = evalCompilerBytecodeLib.register_compile_eval certificate
            val () = equations := Redblackmap.insert
              (!equations,lhs (concl certificate),certificate)
            val () = evalCompilerBytecodeLib.pending_stage_values :=
              (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
            val () = compilerReadyEvalLib.uses_pending := SOME(saved,value,rest)
          in Tactical.ALL_TAC goal end)
    | NONE => let
        val (variables,_) = listSyntax.dest_list (rhs (concl
          (computeLib.EVAL_CONV ``fn_used_vars ^func``)))
        val requests = HOLset.listItems
          (HOLset.addList (HOLset.empty Term.compare,variables))
        val () = compilerReadyEvalLib.uses_pending := SOME(func,func,requests)
      in Tactical.ALL_TAC goal end

  fun warm_context context goal =
    if not (Option.isSome (!compilerReadyContextEvalLib.active)) orelse
        not (aconv (valOf (!compilerReadyContextEvalLib.active)) context) then
      compilerReadyCfgEvalLib.warm_context context goal
    else case !compilerReadyContextEvalLib.pending of
        SOME (func::_,8) => warm_uses func context goal
      | _ => compilerReadyCfgEvalLib.warm_context context goal
end

