(* TOP-LEVEL: warm_step. Compose checked SUE instruction/block suffixes
   without normalizing the already computed payloads again. *)
structure compilerSingleUseTraversalEvalLib = struct
  open HolKernel boolLib
  fun head name = prim_mk_const {Thy="singleUseExpansionDefs",Name=name}
  val insts_head = head "sue_expand_insts_supply"
  val blocks_head = head "sue_expand_blocks_supply"

  fun result current = let
    val operator = fst (strip_comb current)
    val insts = same_const operator insts_head
    val name = if insts then "sue_expand_insts_supply" else "sue_expand_blocks_supply"
    val items = List.nth (snd (strip_comb current),2)
  in if listSyntax.is_nil items then
      Conv.REWR_CONV (hd (CONJUNCTS (SPEC_ALL
        (DB.fetch "singleUseExpansionDefs" (name ^ "_def"))))) current
    else let
      val composed = if insts then compilerSingleUseEvalLib.insts_step current
        else compilerSingleUseEvalLib.blocks_step current
    in if not insts then composed else let
        val joined = Conv.RATOR_CONV (Conv.RAND_CONV listLib.APPEND_CONV)
          (rhs (concl composed))
      in TRANS composed joined end
    end
  end

  fun warm_step next goal =
    (case !compilerPassEvalLib.pending of
      current::_ => if List.exists (same_const (fst (strip_comb current)))
          [insts_head,blocks_head] then let
        val certificate = evalCompilerBytecodeLib.timed_evaluation
          (fst (strip_comb current)) "checked SUE suffix composition"
          (fn () => result current)
        val () = if aconv (lhs (concl certificate)) current then ()
          else raise Fail "SUE suffix composition changed its original call"
        val () = evalCompilerBytecodeLib.register_compile_eval certificate
        val () = compilerPassEvalLib.equations := Redblackmap.insert
          (!compilerPassEvalLib.equations,current,certificate)
        val () = evalCompilerBytecodeLib.pending_stage_values :=
          (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
        val () = compilerPassEvalLib.pending := tl (!compilerPassEvalLib.pending)
      in Tactical.ALL_TAC goal end
      else next goal
    | [] => next goal)
    handle evalCompilerBytecodeLib.PlannerBoundary child =>
      (compilerPassEvalLib.pending := child :: !compilerPassEvalLib.pending;
       Tactical.ALL_TAC goal)
end
