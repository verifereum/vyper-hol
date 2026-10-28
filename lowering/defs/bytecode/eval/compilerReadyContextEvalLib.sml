(* Prepare actual context readiness, including incremental SSA uniqueness. *)
structure compilerReadyContextEvalLib = struct
  open HolKernel boolLib
  type ssa_state = term * thm * thm * term * thm list * thm option
  val ssa_work = ref (NONE : ssa_state option)
  val ssa_finished = ref false
  fun prepare_ssa func goal = let
    fun remember state = ssa_work := SOME state
    val () = case !ssa_work of NONE => let
        val unfolded = Conv.REWR_CONV (DB.fetch "venomWf" "ssa_form_def")
          ``ssa_form ^func``
        val outputs = evalCompilerBytecodeLib.timed_evaluation ``ssa_form`` "output names"
          (fn () => Conv.RAND_CONV computeLib.EVAL_CONV (rhs (concl unfolded)))
        val current = rhs (concl outputs)
        val () = print ("READY_SSA_OUTPUTS " ^ Int.toString
          (length (fst (listSyntax.dest_list (rand current)))) ^ "\n")
      in ssa_finished := false;
         remember (func,unfolded,outputs,current,[],NONE) end
    | SOME (saved,unfolded,outputs,current,prefixes,tail) =>
        if not (aconv saved func) then raise Fail "wrong SSA preparation function"
        else case tail of NONE => let
            val step = Conv.FIRST_CONV (map Conv.REWR_CONV
              (CONJUNCTS (SPEC_ALL listTheory.ALL_DISTINCT))) current
          in if listSyntax.is_nil (rand current) then
              remember (saved,unfolded,outputs,current,prefixes,SOME step)
            else let
              val test = Conv.RATOR_CONV (Conv.RAND_CONV computeLib.EVAL_CONV)
                (rhs (concl step))
              val prefix = TRANS step test
            in remember (saved,unfolded,outputs,rand (rhs (concl prefix)),
                 prefix::prefixes,NONE) end
          end
        | SOME suffix => (case prefixes of [] => let
            val certificate = TRANS unfolded (TRANS outputs suffix)
            val () = evalCompilerBytecodeLib.register_compile_eval certificate
            val () = evalCompilerBytecodeLib.pending_stage_values :=
              (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
          in ssa_work := NONE; ssa_finished := true end
          | prefix::rest => let
            val reduced = Conv.RAND_CONV (fn term =>
              if aconv term (lhs (concl suffix)) then suffix
              else raise Fail "wrong ALL_DISTINCT tail") (rhs (concl prefix))
            val result = TRANS prefix (TRANS reduced
              (computeLib.EVAL_CONV (rhs (concl reduced))))
          in remember (saved,unfolded,outputs,current,rest,SOME result) end)
  in Tactical.ALL_TAC goal end
  
  
  val block_requests = ref (NONE : term list option)
  fun warm_blocks source goal = let
    fun value tm = rhs (concl (computeLib.EVAL_CONV tm))
    fun initialize () = let
      val func = value source
      val cfg = value ``cfg_analyze ^func``
      val dom = value ``dom_analyze ^cfg ^func``
      val blocks = fst (listSyntax.dest_list (value ``(^func).fn_blocks``))
    in (source,cfg,dom,func,blocks) end
    val state as (_,cfg,dom,func,blocks) = case !compilerReadyEvalLib.pending of
        SOME (old,c,d,f,bs) => if aconv old source then (old,c,d,f,bs)
          else initialize ()
      | NONE => initialize ()
    val () = compilerReadyEvalLib.pending := SOME state
  in case !block_requests of
      SOME (call::rest) => let
        val result = evalCompilerBytecodeLib.prepare_closed_call call goal
      in block_requests := SOME rest; result end
    | SOME [] => let
        val result = compilerReadyEvalLib.warm_blocks source goal
      in block_requests := NONE; result end
    | NONE => (case blocks of [] => Tactical.ALL_TAC goal
      | bb::_ => let
          val insts = fst (listSyntax.dest_list (value ``(^bb).bb_instructions``))
          fun requests inst =
            if aconv (value ``(^inst).inst_opcode``) ``PHI`` then
              [``phi_edge_uses_wf_exec ^cfg ^dom ^func ^bb ^inst``]
            else let
              val operands = fst (listSyntax.dest_list
                (value ``(^inst).inst_operands``))
              fun request operand = case strip_comb operand of
                  (head,[v]) => if same_const head ``Var`` then
                    [``def_available_at_exec ^cfg ^dom ^func ^bb (SOME ^inst) ^v``]
                    else []
                | _ => []
            in List.concat (map request operands) end
        in block_requests := SOME (List.concat (map requests insts));
           Tactical.ALL_TAC goal end)
  end

  val active = ref (NONE : term option)
  val pending = ref (NONE : (term list * int) option)
  fun complete context = Option.isSome (!active) andalso
    aconv (valOf (!active)) context andalso
    (case !pending of SOME ([],_) => true | _ => false)

  fun require_complete context goal =
    if complete context then Tactical.ALL_TAC goal
    else raise Fail "context readiness preparation incomplete"

  fun warm_context context goal = let
    val () = if Option.isSome (!active) andalso
        aconv (valOf (!active)) context then ()
      else (active := SOME context; pending := NONE;
        ssa_work := NONE; ssa_finished := false; block_requests := NONE)
    val () = evalCompilerBytecodeLib.ensure_certificate_head ``ssa_form`` 1
    val () = evalCompilerBytecodeLib.ensure_certificate_head ``def_available_at_exec`` 6
    val () = evalCompilerBytecodeLib.ensure_certificate_head ``phi_edge_uses_wf_exec`` 5
    val (functions,phase) = case !pending of SOME work => work
      | NONE => (#1 (listSyntax.dest_list (rhs (concl
          (computeLib.EVAL_CONV ``(^context).ctx_functions``)))),0)
  in case functions of [] => (pending := SOME ([],0); Tactical.ALL_TAC goal)
    | func::rest => let
        val next = ref (phase + 1)
        fun prepare call = evalCompilerBytecodeLib.prepare_closed_call call goal
        val result = case phase of
            0 => prepare ``cfg_analyze ^func``
          | 1 => prepare ``dom_analyze (cfg_analyze ^func) ^func``
          | 2 => let val result = warm_blocks func goal
              in (case !compilerReadyEvalLib.pending of
                  SOME (_,_,_,_,[]) => () | _ => next := phase); result end
          | 3 => prepare ``def_dominates_uses ^func``
          | 4 => prepare ``canonical_param_prefix ^func``
          | 5 => prepare ``wf_function ^func``
          | 6 => prepare ``fn_inst_wf ^func``
          | 7 => let val result = prepare_ssa func goal
              in if !ssa_finished then () else next := phase; result end
          | 8 => let val result = compilerReadyEvalLib.warm_uses func goal
              in (case !compilerReadyEvalLib.uses_pending of
                  SOME (_,_,[]) => () | _ => next := phase); result end
          | 9 => prepare ``single_use_form ^func``
          | 10 => prepare ``cfg_is_normalized (cfg_analyze ^func) ^func``
          | 11 => prepare ``codegen_ready_fn ^func``
          | _ => raise Fail "unexpected context readiness phase"
        val () = pending := SOME
          (if phase = 11 then (rest,0) else (functions,!next))
      in result end
  end
end

