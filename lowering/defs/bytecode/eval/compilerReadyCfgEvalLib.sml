(* Checked graph-analysis bindings for readiness of large function records. *)
structure compilerReadyCfgEvalLib = struct
  open HolKernel boolLib
  fun cfg_head () = prim_mk_const {Thy="cfgDefs",Name="cfg_analyze"}
  val work = ref (Redblackmap.mkDict Term.compare : (term,thm) Redblackmap.dict)
  val completed = ref (Redblackmap.mkDict Term.compare : (term,thm) Redblackmap.dict)
  fun dom_head () = prim_mk_const {Thy="dominatorDefs",Name="dom_analyze"}
  fun configure () = app compilerPassEvalLib.install_indexed_head
    [(cfg_head (),1),(dom_head (),2)]

  fun warm_call current goal = case Redblackmap.peek (!work,current) of
      NONE => let
        val {Thy,Name,...} = dest_thy_const (fst (strip_comb current))
        val unfolded = Conv.REWR_CONV (DB.fetch Thy (Name ^ "_def")) current
        val () = work := Redblackmap.insert (!work,current,unfolded)
      in Tactical.ALL_TAC goal end
    | SOME prefix => let
        val body = rhs (concl prefix)
        val (operator,arguments) = strip_comb body
      in if same_const operator ``LET`` then let
          val argument = List.nth (arguments,1)
          val evaluated = evalCompilerBytecodeLib.timed_evaluation
            (fst (strip_comb current)) "graph binding" (fn () => computeLib.EVAL_CONV argument)
          val projected = Conv.RAND_CONV (fn _ => evaluated) body
          val unfolded = Conv.REWR_CONV boolTheory.LET_THM (rhs (concl projected))
          val reduced = Conv.FIRST_CONV [BETA_CONV,pairLib.PAIRED_BETA_CONV]
            (rhs (concl unfolded))
          val result = TRANS prefix (TRANS projected (TRANS unfolded reduced))
          val () = work := Redblackmap.insert (!work,current,result)
        in Tactical.ALL_TAC goal end
        else let
          val certificate = TRANS prefix (computeLib.EVAL_CONV body)
          val () = evalCompilerBytecodeLib.register_compile_eval certificate
          val () = compilerPassEvalLib.equations := Redblackmap.insert
            (!compilerPassEvalLib.equations,current,certificate)
          val () = completed := Redblackmap.insert (!completed,current,certificate)
          val () = evalCompilerBytecodeLib.pending_stage_values :=
            (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
        in Tactical.ALL_TAC goal end
      end

  fun warm_context context goal = let
    val () = if Option.isSome (!compilerReadyContextEvalLib.active) andalso
        aconv (valOf (!compilerReadyContextEvalLib.active)) context then ()
      else let
        val functions = fst (listSyntax.dest_list (rhs (concl
          (computeLib.EVAL_CONV ``(^context).ctx_functions``))))
      in compilerReadyContextEvalLib.active := SOME context;
         compilerReadyContextEvalLib.pending := SOME (functions,0);
         compilerReadyContextEvalLib.ssa_work := NONE;
         compilerReadyContextEvalLib.ssa_finished := false;
         compilerReadyContextEvalLib.block_requests := NONE end
  in case !compilerReadyContextEvalLib.pending of
      SOME (func::_,phase) =>
        if phase > 1 then compilerReadyContextEvalLib.warm_context context goal
        else let
          val cfg_call = boolSyntax.list_mk_icomb (cfg_head (),[func])
          val call = if phase = 0 then cfg_call else let
            val cfg = rhs (concl (Redblackmap.find (!completed,cfg_call)))
          in boolSyntax.list_mk_icomb (dom_head (),[cfg,func]) end
        in if Option.isSome (Redblackmap.peek (!completed,call)) then
            compilerReadyContextEvalLib.warm_context context goal
          else warm_call call goal end
    | _ => compilerReadyContextEvalLib.warm_context context goal
  end
end

