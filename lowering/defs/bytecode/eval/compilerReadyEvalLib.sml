(* Checked block observations for the original dominance predicate. *)
structure compilerReadyEvalLib = struct
  open HolKernel boolLib codegenReadyObservationsTheory
  type work = term * term * term * term * term list
  val pending = ref (NONE : work option)
  val block_head = prim_mk_const
    {Thy="codegenReadyObservations",Name="block_def_uses_exec"}
  val use_head = prim_mk_const {Thy="codegenReadyObservations",Name="var_single_use"}
  val uses_pending = ref (NONE : (term * term * term list) option)

  fun warm_blocks source goal = let
    fun value tm = rhs(concl(computeLib.EVAL_CONV tm))
    fun initialize () = let
      val func = value source
      val cfg = value ``cfg_analyze ^func``
      val dom = value ``dom_analyze ^cfg ^func``
      val (blocks,_) = listSyntax.dest_list(value ``(^func).fn_blocks``)
    in (source,cfg,dom,func,blocks) end
    val (saved,cfg,dom,func,blocks) = case !pending of
      SOME (old,c,d,f,bs) => if aconv old source then (old,c,d,f,bs) else initialize ()
    | NONE => initialize ()
  in case blocks of [] => Tactical.ALL_TAC goal
  | bb::rest => let
      val (_,certificate) = evalCompilerBytecodeLib.evaluate_call
        (list_mk_comb(block_head,[cfg,dom,func,bb]))
      val () = evalCompilerBytecodeLib.register_compile_eval certificate
      val () = evalCompilerBytecodeLib.pending_stage_values :=
        (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
      val () = pending := SOME(saved,cfg,dom,func,rest)
    in Tactical.ALL_TAC goal end
  end

  fun warm_uses source goal = let
    fun initialize () = let
      val func = rhs(concl(computeLib.EVAL_CONV source))
      val (vars,_) = listSyntax.dest_list
        (rhs(concl(computeLib.EVAL_CONV ``fn_used_vars ^func``)))
      (* Only preparation requests are deduplicated. The original EVERY still
         checks the complete fn_used_vars list, including duplicates. *)
      val requests = HOLset.listItems (HOLset.addList(HOLset.empty Term.compare,vars))
    in (source,func,requests) end
    val (saved,func,vars) = case !uses_pending of
      SOME (old,f,vs) => if aconv old source then (old,f,vs) else initialize ()
    | NONE => initialize ()
  in case vars of [] => Tactical.ALL_TAC goal
  | v::rest => let
      val (_,certificate) = evalCompilerBytecodeLib.evaluate_call
        (list_mk_comb(use_head,[func,v]))
      val () = evalCompilerBytecodeLib.register_compile_eval certificate
      val () = evalCompilerBytecodeLib.pending_stage_values :=
        (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
      val () = uses_pending := SOME(saved,func,rest)
    in Tactical.ALL_TAC goal end
  end
end
