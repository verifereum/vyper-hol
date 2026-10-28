(* TOP-LEVEL: configure. Helper: certify the original operand test with its DFG opaque. *)
structure compilerSingleUseNeedsEvalLib = struct
  open HolKernel boolLib
  val needs_head = prim_mk_const
    {Thy="singleUseExpansionDefs",Name="sue_needs_assign"}
  val uses_head = prim_mk_const {Thy="dfgDefs",Name="dfg_get_uses"}

  val debug_count = ref 0

  fun replace_uses term =
    if is_const (fst (strip_comb term)) andalso
        same_const (fst (strip_comb term)) uses_head andalso
        length (snd (strip_comb term)) = 2 then
      compilerPassEvalLib.checked_call term
    else if is_comb term then
      MK_COMB (replace_uses (rator term),replace_uses (rand term))
    else if is_abs term then let val (variable,body) = dest_abs term
      in ABS variable (replace_uses body) end
    else REFL term

  fun needs_result current = let
    val [dfg,inst,index] = snd (strip_comb current)
    val opaque = genvar (type_of dfg)
    val call = boolSyntax.list_mk_icomb (needs_head,[opaque,inst,index])
    val unfolded = Conv.REWR_CONV
      (DB.fetch "singleUseExpansionDefs" "sue_needs_assign_def") call
    val selected = evalCompilerBytecodeLib.timed_evaluation needs_head
      "operand branch without DFG expansion"
      (fn () => simpLib.SIMP_CONV (bossLib.srw_ss ())
        [boolTheory.LET_THM] (rhs (concl unfolded)))
    val () = if evalCompilerBytecodeLib.profile_evaluation andalso !debug_count < 3 then
      let val body = term_to_string (rhs (concl selected))
      in debug_count := !debug_count + 1;
         print ("SUE_NEEDS_SYMBOLIC_BODY " ^
           String.substring (body,0,Int.min (size body,1200)) ^ "\n") end
      else ()
    val concrete = evalCompilerBytecodeLib.timed_evaluation needs_head
      "operand instantiation" (fn () => INST [opaque |-> dfg] (TRANS unfolded selected))
    val looked = evalCompilerBytecodeLib.timed_evaluation needs_head
      "cached use substitution" (fn () => replace_uses (rhs (concl concrete)))
    val evaluated = evalCompilerBytecodeLib.timed_evaluation needs_head
      "small operand test" (fn () => computeLib.EVAL_CONV (rhs (concl looked)))
    val result = TRANS concrete (TRANS looked evaluated)
    val () = if aconv (lhs (concl result)) current then ()
      else raise Fail "single-use operand proof changed its original call"
  in result end

  fun configure () = compilerPassEvalLib.extend_phases []
    [(needs_head,needs_result)] []
end
