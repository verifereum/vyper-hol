(* Exact constructor boundaries for the original DFG builder. *)
structure compilerDfgEvalLib = struct
  open HolKernel boolLib
  val active = ref (NONE : term option)
  val pending = ref ([] : term list)
  val completed = ref ([] : term list)
  datatype attempt = Complete of thm | Pending of term

  fun head name = prim_mk_const {Thy="dfgDefs",Name=name}
  fun phases () = map (fn (name,arity) => (head name,arity))
    [("dfg_build_function",1),("dfg_build_insts",1),("dfg_build_insts_rev",2),
     ("dfg_add_inst",2),("dfg_add_uses",3),("dfg_add_use",3),
     ("dfg_add_defs",3),("dfg_get_uses",2)]

  fun configure () = let
    val entries = phases ()
    val () = app (fn (head,arity) =>
      evalCompilerBytecodeLib.ensure_certificate_head head arity) entries
  in app compilerPassEvalLib.install_indexed_head entries end

  fun unfold current = let
    val {Name,...} = dest_thy_const (fst (strip_comb current))
  in Conv.FIRST_CONV (map Conv.REWR_CONV
    (CONJUNCTS (SPEC_ALL (DB.fetch "dfgDefs" (Name ^ "_def"))))) current end

  (* Specialize the small schema once; replacement maps are opaque payloads.
     Repeated SPEC would revisit maps inserted by earlier instantiations. *)
  fun instantiate theorem arguments = let
    val (variables,_) = strip_forall (concl theorem)
    val generic = SPECL variables theorem
  in INST (ListPair.map (fn (variable,value) => variable |-> value)
       (variables,arguments)) generic end

  fun recursive_result current = let
    val unfolded = unfold current
    val body = rhs (concl unfolded)
  in if not (same_const (fst (strip_comb body)) (fst (strip_comb current))) then unfolded
    else let
      val step = compilerSingleUseEvalLib.argument 1
        compilerPassEvalLib.checked_call body
      val tail = compilerPassEvalLib.checked_call (rhs (concl step))
    in TRANS unfolded (TRANS step tail) end
  end

  fun project_record inst body = let
    fun clauses rules = List.concat (map (CONJUNCTS o SPEC_ALL) rules)
    val accessors = clauses
      [DB.fetch "dfgDefs" "dfg_analysis_accessors",
       DB.fetch "dfgDefs" "dfg_analysis_accfupds",
       DB.fetch "venomInst" "instruction_accessors",
       DB.fetch "venomInst" "instruction_accfupds"]
    val updates = clauses [DB.fetch "dfgDefs" "dfg_analysis_fn_updates"]
    val empty = DB.fetch "dfgDefs" "dfg_empty_def"
    fun rule_head theorem = fst (strip_comb (lhs (#2 (strip_forall (concl theorem)))))
    fun headed rules term = is_const (fst (strip_comb term)) andalso
      List.exists (same_const (fst (strip_comb term)) o rule_head) rules
    fun rewrite rules term = Conv.FIRST_CONV (map Conv.REWR_CONV rules) term
      handle HOL_ERR _ => REFL term | Conv.UNCHANGED => REFL term
    fun selector term = let
      val receiver = if headed accessors term then
          Conv.RAND_CONV (rewrite [empty]) term else REFL term
      val value = rhs (concl receiver)
      val selected = SOME (Conv.FIRST_CONV (map Conv.REWR_CONV
          (DB.fetch "combin" "K_THM" :: accessors)) value)
        handle HOL_ERR _ => NONE | Conv.UNCHANGED => NONE
    in case selected of NONE => receiver
      | SOME step => TRANS receiver (TRANS step (selector (rhs (concl step))))
    end
    fun field term = let
      val observed = selector term
      val value = rhs (concl observed)
    in if finite_mapSyntax.is_fupdate value then let
        val base = compilerSingleUseEvalLib.argument 1 selector value
        val key = compilerSingleUseEvalLib.argument 2
          (Conv.RATOR_CONV (Conv.RAND_CONV selector)) (rhs (concl base))
      in TRANS observed (TRANS base key) end
      else observed
    end
    fun literal_fields term = if headed updates term then let
        fun value function = if is_abs function then Conv.ABS_CONV field function
          else Conv.RAND_CONV field function
        val first = compilerSingleUseEvalLib.argument 1 value term
        val rest = Conv.RAND_CONV literal_fields (rhs (concl first))
      in TRANS first rest end
      else if List.exists (same_const (fst (strip_comb term)))
          (TypeBase.constructors_of (type_of term)) then
        List.foldl (fn (index,equation) => TRANS equation
          (compilerSingleUseEvalLib.argument index field (rhs (concl equation))))
          (REFL term) (List.tabulate (length (snd (strip_comb term)),fn i => i + 1))
      else REFL term
    val literal = ISPEC body (DB.fetch "venomDfgEval" "dfg_record_fields")
    val fields = literal_fields (rhs (concl literal))
  in TRANS literal fields
  end

  fun instruction_result current = let
    val [dfg,inst] = snd (strip_comb current)
    val uses_call = ``dfg_add_uses ^dfg (operand_vars (^inst).inst_operands) ^inst``
    val operands = compilerSingleUseEvalLib.argument 2 computeLib.EVAL_CONV uses_call
    val uses = TRANS operands (compilerPassEvalLib.checked_call (rhs (concl operands)))
    val used = rhs (concl uses)
    val defs_call = ``dfg_add_defs ^used (^inst).inst_outputs ^inst``
    val outputs = compilerSingleUseEvalLib.argument 2 computeLib.EVAL_CONV defs_call
    val defs = TRANS outputs (compilerPassEvalLib.checked_call (rhs (concl outputs)))
    val defined = rhs (concl defs)
    val result = evalCompilerBytecodeLib.timed_evaluation (head "dfg_add_inst")
      "DFG instruction composition" (fn () => let
        val law = instantiate (DB.fetch "venomDfgEval" "dfg_add_inst_result")
          [dfg,inst,used,defined]
      in MP law (CONJ uses defs) end)
    val projected = evalCompilerBytecodeLib.timed_evaluation (head "dfg_add_inst")
      "DFG record projection" (fn () => project_record inst (rhs (concl result)))
  in TRANS result projected end

  fun use_result current = let
    val [dfg,v,inst] = snd (strip_comb current)
    val uses = compilerPassEvalLib.checked_call ``dfg_get_uses ^dfg ^v``
    val law = instantiate (DB.fetch "venomDfgEval" "dfg_add_use_result")
      [dfg,v,inst,rhs (concl uses)]
    val result = MP law uses
    val tested = compilerSingleUseEvalLib.argument 1 computeLib.EVAL_CONV
      (rhs (concl result))
    val selected = Conv.FIRST_CONV (map Conv.REWR_CONV
      (CONJUNCTS (SPEC_ALL boolTheory.COND_CLAUSES))) (rhs (concl tested))
    val prefix = TRANS result (TRANS tested selected)
  in TRANS prefix (project_record inst (rhs (concl prefix))) end

  fun definitions_result current = let
    val unfolded = unfold current
    val body = rhs (concl unfolded)
    val inst = List.nth (snd (strip_comb current),2)
  in if not (same_const (fst (strip_comb body)) (fst (strip_comb current))) then unfolded
    else let
      val updated = compilerSingleUseEvalLib.argument 1 (project_record inst) body
      val tail = compilerPassEvalLib.checked_call (rhs (concl updated))
    in TRANS unfolded (TRANS updated tail) end
  end

  fun require_complete call goal =
    if List.exists (aconv call) (!completed) then Tactical.ALL_TAC goal
    else raise Fail ("DFG preparation incomplete: " ^
      Int.toString (length (!pending)) ^ " pending calls")

  fun warm_call call goal =
    if List.exists (aconv call) (!completed) then Tactical.ALL_TAC goal
    else if not (Option.isSome (!active) andalso aconv (valOf (!active)) call) then let
      val inputs = evalCompilerBytecodeLib.timed_evaluation (fst (strip_comb call))
        "DFG inputs" (fn () => evalCompilerBytecodeLib.normalize_call call)
      val () = active := SOME call
      val () = pending := [rhs (concl inputs)]
    in Tactical.ALL_TAC goal end
    else case !pending of [] => raise Fail "missing DFG work"
    | current::_ => let
      val current_head = fst (strip_comb current)
      fun is name = same_const current_head (head name)
      val captures = if is "dfg_build_function" then [head "dfg_build_insts"]
        else if is "dfg_build_insts" then [head "dfg_build_insts_rev"]
        else if is "dfg_add_inst" then [head "dfg_add_uses",head "dfg_add_defs"]
        else if is "dfg_add_use" then [head "dfg_get_uses"] else []
      fun evaluate () = evalCompilerBytecodeLib.timed_evaluation current_head
        "DFG fragment" (fn () =>
          if is "dfg_build_insts_rev" orelse is "dfg_add_uses" then
            recursive_result current
          else if is "dfg_get_uses" then compilerSingleUseEvalLib.uses_step current
          else if is "dfg_add_inst" then instruction_result current
          else if is "dfg_add_use" then use_result current
          else if is "dfg_add_defs" then definitions_result current
          else let
            val unfolded = unfold current
            val result = computeLib.EVAL_CONV (rhs (concl unfolded))
          in TRANS unfolded result end)
      val result = (Complete (Lib.with_flag
        (evalCompilerBytecodeLib.planner_capture_heads,captures) evaluate ())
        handle evalCompilerBytecodeLib.PlannerBoundary child => Pending child)
      val () = case result of Pending child => pending := child :: !pending
      | Complete certificate =>
          (evalCompilerBytecodeLib.register_compile_eval certificate;
           compilerPassEvalLib.equations := Redblackmap.insert
             (!compilerPassEvalLib.equations,lhs (concl certificate),certificate);
           evalCompilerBytecodeLib.pending_stage_values :=
             (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values;
           if length (!pending) = 1 then completed := call :: !completed else ();
           pending := tl (!pending))
    in Tactical.ALL_TAC goal end
end
