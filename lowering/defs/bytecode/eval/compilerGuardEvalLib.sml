(* Checked CV preparation of closed supply guards. The enclosing schedule
   still checks the original predicate and all other pass conditions. *)
structure compilerGuardEvalLib = struct
  open HolKernel boolLib

  fun prepare_subset call goal = let
    val source_head = fst(strip_comb call)
    val normalized = rhs(concl(evalCompilerBytecodeLib.timed_evaluation
      source_head "guard inputs" (fn () => evalCompilerBytecodeLib.normalize_call call)))
    val head = fst(strip_comb normalized)
    val () = if same_const head
        (prim_mk_const {Thy="venomFnScheduleRunner",Name="list_subset"}) andalso
        null(free_vars normalized) andalso null(type_vars_in_term normalized)
      then () else raise Fail "expected a closed list_subset guard"
    val certificate = evalCompilerBytecodeLib.timed_evaluation
      head "guard CV" (fn () => cv_transLib.cv_eval normalized)
    val () = if aconv (lhs(concl certificate)) normalized then ()
      else raise Fail "wrong supply guard certificate"
    val () = evalCompilerBytecodeLib.timed_evaluation head "guard register"
      (fn () => evalCompilerBytecodeLib.register_compile_eval certificate)
    val () = evalCompilerBytecodeLib.pending_stage_values :=
      (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
  in Tactical.ALL_TAC goal end

  (* Each invocation proves one small slice of the SAME predicate. Assembly
     uses the universal append law, including its actual Boolean results. *)
  type subset_work = term * term * term * term list * thm list
  val subset_pending = ref (NONE : subset_work option)

  fun subset_chunks xs ty =
    if null xs then [listSyntax.mk_list([],ty)] else let
      val n = Int.min(16,length xs)
      val prefix = listSyntax.mk_list(List.take(xs,n),ty)
      val rest = List.drop(xs,n)
    in prefix :: (if null rest then [] else subset_chunks rest ty) end

  fun join_subset prefix suffix = let
    val (_,pa) = strip_comb(lhs(concl prefix))
    val (_,sa) = strip_comb(lhs(concl suffix))
    val law = ISPECL [hd pa,hd sa,List.nth(pa,1)]
      (DB.fetch "venomSupplyEval" "list_subset_append")
    val expanded = Conv.CONV_RULE
      (Conv.LAND_CONV (Conv.RATOR_CONV (Conv.RAND_CONV computeLib.EVAL_CONV))) law
    val reduced = Conv.COMB2_CONV
      (Conv.RAND_CONV (fn _ => prefix),fn _ => suffix) (rhs(concl expanded))
  in TRANS expanded (TRANS reduced (computeLib.EVAL_CONV(rhs(concl reduced)))) end

  fun warm_subset call goal = let
    fun initialize () = let
      val normalized = rhs(concl(evalCompilerBytecodeLib.normalize_call call))
      val (head,args) = strip_comb normalized
      val () = if same_const head
          (prim_mk_const {Thy="venomFnScheduleRunner",Name="list_subset"}) andalso
          null(free_vars normalized) andalso null(type_vars_in_term normalized)
        then () else raise Fail "expected a closed list_subset guard"
      val (xs,ty) = listSyntax.dest_list(hd args)
    in (call,head,List.nth(args,1),subset_chunks xs ty,[]) end
    val state = case !subset_pending of
      SOME (saved,h,ys,todo,done) =>
        if aconv saved call then (saved,h,ys,todo,done) else initialize ()
    | NONE => initialize ()
    val (saved,head,ys,todo,done) = state
    fun remember certificate =
      (evalCompilerBytecodeLib.register_compile_eval certificate;
       evalCompilerBytecodeLib.pending_stage_values :=
         (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values)
  in case todo of
    [] => Tactical.ALL_TAC goal
  | chunk::rest => let
      val certificate = computeLib.EVAL_CONV (list_mk_comb(head,[chunk,ys]))
      val proofs = certificate::done
      val () = remember certificate
      val () = if null rest then
        remember (List.foldl (fn (pre,suf) => join_subset pre suf)
          (hd proofs) (tl proofs)) else ()
      val () = subset_pending := SOME(saved,head,ys,rest,proofs)
    in Tactical.ALL_TAC goal end
  end
end
