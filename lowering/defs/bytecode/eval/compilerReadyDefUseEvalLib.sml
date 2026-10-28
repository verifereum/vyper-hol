(* Reuse prepared CFG/dominator/function values for original use queries.
   Each request is still certified by the original kernel evaluator. *)
structure compilerReadyDefUseEvalLib = struct
  open HolKernel boolLib

  fun heads () =
    [(prim_mk_const {Thy="codegenReadyCompute",Name="def_available_at_exec"},6),
     (prim_mk_const {Thy="codegenReadyCompute",Name="phi_edge_uses_wf_exec"},5)]

  fun compare_calls (left,right) = let
    val (lh,la) = strip_comb left
    val (rh,ra) = strip_comb right
  in case Term.compare (lh,rh) of
      EQUAL => (case Term.compare (List.last la,List.last ra) of
        EQUAL => (case Term.compare (List.nth (la,3),List.nth (ra,3)) of
          EQUAL => Term.compare (left,right)
        | order => order)
      | order => order)
    | order => order
  end
  val equations = ref (Redblackmap.mkDict compare_calls : (term,thm) Redblackmap.dict)

  fun configure () =
    (app (fn (head,arity) =>
       evalCompilerBytecodeLib.ensure_certificate_head head arity) (heads ());
     app (compilerSsaEvalLib.install_indexed_head equations) (heads ()))

  fun prepare_request call rest goal = let
    val head = fst (strip_comb call)
    val certificate = evalCompilerBytecodeLib.timed_evaluation head
      "prepared definition-use query" (fn () => computeLib.EVAL_CONV call)
    val () = evalCompilerBytecodeLib.register_compile_eval certificate
    val () = equations := Redblackmap.insert
      (!equations,lhs (concl certificate),certificate)
    val () = evalCompilerBytecodeLib.pending_stage_values :=
      (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
    val () = compilerReadyContextEvalLib.block_requests := SOME rest
  in Tactical.ALL_TAC goal end

  fun warm_context context goal =
    if Option.isSome (!compilerReadyContextEvalLib.active) andalso
        aconv (valOf (!compilerReadyContextEvalLib.active)) context then
      (case (!compilerReadyContextEvalLib.pending,
             !compilerReadyContextEvalLib.block_requests) of
          (SOME (_::_,2),SOME (call::rest)) => prepare_request call rest goal
        | _ => compilerReadyDomEvalLib.warm_context context goal)
    else compilerReadyDomEvalLib.warm_context context goal
end
