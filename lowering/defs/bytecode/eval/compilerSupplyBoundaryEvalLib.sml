(* Certify original supply predicates one conjunct at a time. *)
structure compilerSupplyBoundaryEvalLib = struct
  open HolKernel boolLib
  fun head name = prim_mk_const {Thy="venomFnScheduleRunner",Name=name}
  fun guards () = map head ["ir_supply_extends","ir_supply_covers_fn","ir_supply_covers_unit"]
  fun collections () = map (fn name => prim_mk_const {Thy="irSupply",Name=name})
    ["fn_ir_vars","block_ir_vars","inst_ir_vars"]
  fun configure () = app compilerPassEvalLib.install_indexed_head
    (map (fn operator => (operator,2)) (guards ()) @
     map (fn operator => (operator,1)) (collections ()))
  type state = thm * term list * thm list
  val work = ref (Redblackmap.mkDict Term.compare : (term,state) Redblackmap.dict)

  fun atom_result atom = Lib.with_flag
    (evalCompilerBytecodeLib.planner_capture_heads,collections ()) (fn () =>
    if is_const (fst (strip_comb atom)) andalso
        same_const (fst (strip_comb atom)) (head "list_subset") then let
      val inputs = evalCompilerBytecodeLib.timed_evaluation (head "list_subset")
        "supply inputs" (fn () => evalCompilerBytecodeLib.normalize_call atom)
      val certificate = compilerPassEvalLib.checked_call (rhs (concl inputs))
    in TRANS inputs certificate end
    else compilerSingleUseEvalLib.guard_observation atom) ()

  fun warm_collection current goal = let
    val {Name,...} = dest_thy_const (fst (strip_comb current))
    val unfolded = Conv.REWR_CONV (DB.fetch "irSupply" (Name ^ "_def")) current
    val result = Lib.with_flag
      (evalCompilerBytecodeLib.planner_capture_heads,collections ())
      computeLib.EVAL_CONV (rhs (concl unfolded))
    val certificate = TRANS unfolded result
    val () = evalCompilerBytecodeLib.register_compile_eval certificate
    val () = compilerPassEvalLib.equations := Redblackmap.insert
      (!compilerPassEvalLib.equations,current,certificate)
    val () = evalCompilerBytecodeLib.pending_stage_values :=
      (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
    val () = compilerPassEvalLib.pending := tl (!compilerPassEvalLib.pending)
  in Tactical.ALL_TAC goal end

  fun assemble facts body =
    if boolSyntax.is_conj body then let
      val (left,right) = boolSyntax.dest_conj body
      val projected = MK_COMB
        (AP_TERM (rator (rator body)) (assemble facts left),assemble facts right)
    in TRANS projected (computeLib.EVAL_CONV (rhs (concl projected))) end
    else case List.find (fn theorem => aconv body (lhs (concl theorem))) facts of
        SOME theorem => theorem
      | NONE => raise Fail "missing checked supply conjunct"

  fun warm_guard current goal =
    case Redblackmap.peek (!work,current) of
      NONE => let
        val {Name,...} = dest_thy_const (fst (strip_comb current))
        val supply = hd (snd (strip_comb current))
        val fields = List.concat (map (CONJUNCTS o SPEC_ALL)
          (TypeBase.accessors_of (type_of supply)))
        val accessors = map (fst o strip_comb o lhs o concl) fields
        fun project term = let
          val operator = fst (strip_comb term)
        in if is_comb term andalso is_const operator andalso
            List.exists (same_const operator) accessors
          then Conv.TRY_CONV (Conv.FIRST_CONV (map Conv.REWR_CONV fields)) term
          else if is_const operator andalso #Thy (dest_thy_const operator) = "irSupply"
          then REFL term
          else if is_comb term then Conv.COMB_CONV project term
          else if is_abs term then Conv.ABS_CONV project term else REFL term
        end
        val unfolded = evalCompilerBytecodeLib.timed_evaluation (head Name)
          "supply unfold" (fn () => Conv.REWR_CONV
            (DB.fetch "venomFnScheduleRunner" (Name ^ "_def")) current)
        val body = rhs (concl unfolded)
        val projected = evalCompilerBytecodeLib.timed_evaluation (head Name)
          "supply projection" (fn () => project body)
        val prefix = TRANS unfolded projected
        val () = work := Redblackmap.insert
          (!work,current,(prefix,strip_conj (rhs (concl prefix)),[]))
      in Tactical.ALL_TAC goal end
    | SOME (prefix,atom::rest,facts) => let
        val certificate = evalCompilerBytecodeLib.timed_evaluation
          (fst (strip_comb current)) "supply conjunct" (fn () => atom_result atom)
        val () = work := Redblackmap.insert
          (!work,current,(prefix,rest,certificate::facts))
      in Tactical.ALL_TAC goal end
    | SOME (prefix,[],facts) => let
        val certificate = TRANS prefix (assemble facts (rhs (concl prefix)))
        val () = evalCompilerBytecodeLib.register_compile_eval certificate
        val () = compilerPassEvalLib.equations := Redblackmap.insert
          (!compilerPassEvalLib.equations,current,certificate)
        val () = evalCompilerBytecodeLib.pending_stage_values :=
          (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
        val () = compilerPassEvalLib.pending := tl (!compilerPassEvalLib.pending)
      in Tactical.ALL_TAC goal end

  fun warm_step goal =
    (case !compilerPassEvalLib.pending of
        current::_ => if List.exists (same_const (fst (strip_comb current))) (guards ())
          then warm_guard current goal
          else if List.exists (same_const (fst (strip_comb current))) (collections ())
          then warm_collection current goal else compilerMemoryFrameEvalLib.warm_step goal
      | [] => compilerMemoryFrameEvalLib.warm_step goal)
    handle evalCompilerBytecodeLib.PlannerBoundary child =>
      (compilerPassEvalLib.pending := child :: !compilerPassEvalLib.pending;
       Tactical.ALL_TAC goal)
end

