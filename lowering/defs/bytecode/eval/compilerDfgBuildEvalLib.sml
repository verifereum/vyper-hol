(* Exact bounded preparation of the original recursive DFG construction. *)
structure compilerDfgBuildEvalLib = struct
  open HolKernel boolLib
  fun entries () = map (fn (name,arity) =>
    (prim_mk_const {Thy="dfgDefs",Name=name},arity))
    [("dfg_build_function",1),("dfg_build_insts",1),
     ("dfg_build_insts_rev",2),("dfg_add_inst",2),
     ("dfg_add_uses",3),("dfg_add_use",3),("dfg_add_defs",3)]
  val equations = ref (Redblackmap.mkDict Term.compare : (term,thm) Redblackmap.dict)
  val active = ref (NONE : term option)
  val pending = ref ([] : term list)
  val completed = ref ([] : term list)

  fun configure () = app (fn entry as (head,arity) =>
    (evalCompilerBytecodeLib.ensure_certificate_head head arity;
     compilerSsaEvalLib.install_indexed_head equations entry)) (entries ())

  fun complete call = List.exists (aconv call) (!completed)
  fun require_complete call goal =
    if complete call then Tactical.ALL_TAC goal
    else raise Fail ("DFG preparation incomplete: " ^
      Int.toString (length (!pending)) ^ " pending calls")

  fun checked call = case Redblackmap.peek (!equations,call) of
      SOME certificate => certificate
    | NONE => raise evalCompilerBytecodeLib.PlannerBoundary call

  fun argument position conversion term = let
    fun descend 0 = Conv.RAND_CONV conversion
      | descend n = Conv.RATOR_CONV (descend (n - 1))
  in descend (length (snd (strip_comb term)) - position) term end
  val first_argument = argument 1

  fun record_update term = let
    val state = List.last (snd (strip_comb term))
    val fields = List.concat (map (CONJUNCTS o SPEC_ALL)
      (TypeBase.accessors_of (type_of state)))
    val updates = List.concat (map (CONJUNCTS o SPEC_ALL)
      (TypeBase.updates_of (type_of state)))
    val rules = CONJUNCTS (SPEC_ALL (DB.fetch "dfgDefs" "dfg_analysis_accfupds")) @
      (DB.fetch "combin" "K_THM" :: fields)
    fun project expression =
      case SOME (Conv.FIRST_CONV (map Conv.REWR_CONV rules) expression)
          handle HOL_ERR _ => NONE of
        SOME equation => TRANS equation (project (rhs (concl equation)))
      | NONE => if finite_mapSyntax.is_fupdate expression then
          first_argument project expression else REFL expression
    fun project_fields conversion expression = let
      val (constructor,arguments) = strip_comb expression
    in List.foldl (fn (argument,theorem) => MK_COMB (theorem,conversion argument))
      (REFL constructor) arguments end
    val state_equation =
      if TypeBase.is_constructor (fst (strip_comb state)) then REFL state
      else let
        val eta = SPEC state (DB.fetch "venomDfgRecordCases" "dfg_analysis_eta")
      in TRANS eta (project_fields project (rhs (concl eta))) end
    val normalized = Conv.RAND_CONV (fn _ => state_equation) term
    val unfolded = Conv.FIRST_CONV (map Conv.REWR_CONV updates)
      (rhs (concl normalized))
    fun changed_field field =
      if is_comb field andalso same_const (fst (strip_comb field))
          (prim_mk_const {Thy="combin",Name="K"}) then let
        val reduced = project field
        val value = rhs (concl reduced)
        val key = if finite_mapSyntax.is_fupdate value then
            Conv.RAND_CONV (Conv.RATOR_CONV (Conv.RAND_CONV
              computeLib.EVAL_CONV)) value
          else REFL value
      in TRANS reduced key end else REFL field
    val projected = project_fields changed_field (rhs (concl unfolded))
  in TRANS normalized (TRANS unfolded projected) end

  val bindings = ref (Redblackmap.mkDict Term.compare : (term,thm) Redblackmap.dict)
  fun binding_step current unfolded = let
    val prefix = case Redblackmap.peek (!bindings,current) of
        SOME theorem => theorem | NONE => unfolded
    val body = rhs (concl prefix)
    fun remember theorem =
      (bindings := Redblackmap.insert (!bindings,current,theorem); NONE)
    fun binding_value expression = let
      val operator = fst (strip_comb expression)
    in if same_const operator
        (prim_mk_const {Thy="dfgDefs",Name="dfg_get_uses"}) then
        compilerSingleUseEvalLib.uses_step expression
      else if List.exists (fn (head,_) => same_const operator head) (entries ()) then let
        val {Name,...} = dest_thy_const operator
        val inputs = if Name = "dfg_add_uses" orelse Name = "dfg_add_defs" then
            argument 2 computeLib.EVAL_CONV expression else REFL expression
      in TRANS inputs (checked (rhs (concl inputs))) end
      else computeLib.EVAL_CONV expression
    end
  in if same_const (fst (strip_comb body)) ``LET`` then let
      val value = binding_value (List.nth (snd (strip_comb body),1))
      val evaluated = Conv.RAND_CONV (fn _ => value) body
      val exposed = Conv.REWR_CONV boolTheory.LET_THM (rhs (concl evaluated))
      val reduced = BETA_CONV (rhs (concl exposed))
    in remember (TRANS prefix (TRANS evaluated (TRANS exposed reduced))) end
    else if boolSyntax.is_cond body then let
      val tested = argument 1 computeLib.EVAL_CONV body
      val selected = Conv.FIRST_CONV (map Conv.REWR_CONV
        (CONJUNCTS (SPEC_ALL boolTheory.COND_CLAUSES))) (rhs (concl tested))
    in remember (TRANS prefix (TRANS tested selected)) end
    else let
      val operator = fst (strip_comb body)
      val final = if is_const operator andalso
          String.isSuffix "_fupd" (#Name (dest_thy_const operator)) then
          record_update body else REFL body
    in SOME (TRANS prefix final) end
  end

  fun recursive_result name current unfolded =
    if listSyntax.is_nil (List.nth (snd (strip_comb current),1)) then unfolded
    else let
      val body = rhs (concl unfolded)
      val step = first_argument
        (if name = "dfg_add_defs" then record_update else checked) body
      val tail = checked (rhs (concl step))
    in TRANS unfolded (TRANS step tail) end

  fun warm_call call goal =
    if complete call then Tactical.ALL_TAC goal
    else if not (Option.isSome (!active)) orelse
        not (aconv (valOf (!active)) call) then let
      val inputs = evalCompilerBytecodeLib.normalize_call call
      val () = active := SOME call
      val () = pending := [rhs (concl inputs)]
    in Tactical.ALL_TAC goal end
    else (case !pending of
      [] => (completed := call :: !completed; Tactical.ALL_TAC goal)
    | current::rest => let
        val operator = fst (strip_comb current)
        val {Name,...} = dest_thy_const operator
        val definition = DB.fetch "dfgDefs" (Name ^ "_def")
        val unfolded = Conv.FIRST_CONV
          (map Conv.REWR_CONV (CONJUNCTS (SPEC_ALL definition))) current
        val prepared = evalCompilerBytecodeLib.timed_evaluation operator
          "DFG construction step" (fn () =>
            if Name = "dfg_add_inst" orelse Name = "dfg_add_use" then
              binding_step current unfolded
            else SOME (if List.exists (fn name => name = Name)
                ["dfg_build_insts_rev","dfg_add_uses","dfg_add_defs"] then
              recursive_result Name current unfolded
            else TRANS unfolded (Lib.with_flag
              (evalCompilerBytecodeLib.planner_capture_heads,map #1 (entries ()))
              computeLib.EVAL_CONV (rhs (concl unfolded)))))
      in case prepared of NONE => Tactical.ALL_TAC goal
      | SOME certificate => let
        val () = evalCompilerBytecodeLib.register_compile_eval certificate
        val () = equations := Redblackmap.insert (!equations,current,certificate)
        val () = evalCompilerBytecodeLib.pending_stage_values :=
          (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
        val () = pending := rest
      in Tactical.ALL_TAC goal end end)
    handle evalCompilerBytecodeLib.PlannerBoundary child =>
      (pending := child :: !pending; Tactical.ALL_TAC goal)
end

