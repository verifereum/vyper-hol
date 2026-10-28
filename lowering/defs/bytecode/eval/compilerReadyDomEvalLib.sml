(* Prepare the original dominator dataflow calculation in checked worklist steps. *)
structure compilerReadyDomEvalLib = struct
  open HolKernel boolLib
  val equations = compilerDftWorklistEvalLib.equations
  val active = ref (NONE : term option)
  val pending = ref ([] : term list)
  val completed = ref ([] : term list)
  val prefixes = ref (Redblackmap.mkDict Term.compare : (term,thm) Redblackmap.dict)

  fun entries () =
    [(prim_mk_const {Thy="dominatorDefs",Name="dom_fixpoint"},1),
     (prim_mk_const {Thy="dominatorDefs",Name="compute_idom"},4),
     (prim_mk_const {Thy="dominatorDefs",Name="compute_idom_for"},4),
     (prim_mk_const {Thy="dominatorDefs",Name="compute_dominated"},2),
     (prim_mk_const {Thy="dominatorDefs",Name="compute_df"},4),
     (prim_mk_const {Thy="dominatorDefs",Name="walk_to_idom"},5),
     (prim_mk_const {Thy="dfAnalyzeDefs",Name="df_analyze"},8),
     (prim_mk_const {Thy="dfAnalyzeDefs",Name="df_process_block"},11),
     (prim_mk_const {Thy="dfAnalyzeDefs",Name="df_populate_inst"},11),
     (prim_mk_const {Thy="dfAnalyzeDefs",Name="df_joined_val"},9),
     (prim_mk_const {Thy="dfAnalyzeDefs",Name="df_fold_block"},5),
     (prim_mk_const {Thy="dfAnalyzeDefs",Name="df_fold_forward"},6),
     (prim_mk_const {Thy="worklistDefs",Name="wl_iterate"},5),
     (prim_mk_const {Thy="worklistDefs",Name="wl_step"},4),
     (prim_mk_const {Thy="While",Name="WHILE"},3),
     (prim_mk_const {Thy="list",Name="FOLDL"},3),
     (prim_mk_const {Thy="finite_map",Name="FUNION"},2)]
  fun configure () = app (fn entry as (head,arity) =>
    (evalCompilerBytecodeLib.ensure_certificate_head head arity;
     compilerSsaEvalLib.install_indexed_head equations entry)) (entries ())
  fun complete call = List.exists (aconv call) (!completed)
  val checked = compilerDftWorklistEvalLib.checked_call
  val argument = compilerDftWorklistEvalLib.argument
  fun evaluate expression = Lib.with_flag
    (evalCompilerBytecodeLib.planner_capture_heads,map #1 (entries ()))
    computeLib.EVAL_CONV expression

  val fold_steps = ref (Redblackmap.mkDict Term.compare : (term,thm) Redblackmap.dict)

  fun record_result term = let
    val state = List.last (snd (strip_comb term))
    val fields = List.concat (map (CONJUNCTS o SPEC_ALL)
      (TypeBase.accessors_of (type_of state)))
    val updates = List.concat (map (CONJUNCTS o SPEC_ALL)
      (TypeBase.updates_of (type_of state)))
    val rules = CONJUNCTS (SPEC_ALL (DB.fetch "dfAnalyzeDefs" "df_state_accfupds")) @
      (DB.fetch "combin" "K_THM" :: fields)
    val union = prim_mk_const {Thy="finite_map",Name="FUNION"}
    fun project expression =
      case SOME (Conv.FIRST_CONV (map Conv.REWR_CONV rules) expression)
          handle HOL_ERR _ => NONE of
        SOME equation => TRANS equation (project (rhs (concl equation)))
      | NONE => if finite_mapSyntax.is_fupdate expression then
          argument 1 project expression
        else if same_const (fst (strip_comb expression)) union then let
          val left = argument 1 project expression
          val right = argument 2 project (rhs (concl left))
        in TRANS left right end
        else REFL expression
    fun project_fields conversion expression = let
      val (constructor,values) = strip_comb expression
    in List.foldl (fn (value,theorem) => MK_COMB (theorem,conversion value))
      (REFL constructor) values end
    val state_equation =
      if TypeBase.is_constructor (fst (strip_comb state)) then REFL state
      else let
        val eta = ISPEC state (DB.fetch "venomDfStateCases" "df_state_eta")
      in TRANS eta (project_fields project (rhs (concl eta))) end
    val normalized = Conv.RAND_CONV (fn _ => state_equation) term
    val unfolded = Conv.FIRST_CONV (map Conv.REWR_CONV updates)
      (rhs (concl normalized))
    fun field value =
      if is_comb value andalso same_const (fst (strip_comb value))
          (prim_mk_const {Thy="combin",Name="K"}) then let
        val projected = project value
        val result = rhs (concl projected)
      in if same_const (fst (strip_comb result)) union then
          TRANS projected (checked result) else projected end
      else REFL value
  in TRANS normalized (TRANS unfolded (project_fields field (rhs (concl unfolded)))) end

  fun union_result current = let
    val unfolded = Conv.FIRST_CONV (map (fn name =>
      Conv.REWR_CONV (DB.fetch "finite_map" name))
      ["FUNION_FEMPTY_1","FUNION_FEMPTY_2","FUNION_FUPDATE_1"]) current
    val body = rhs (concl unfolded)
  in if finite_mapSyntax.is_fupdate body andalso
      same_const (fst (strip_comb (hd (snd (strip_comb body)))))
        (prim_mk_const {Thy="finite_map",Name="FUNION"}) then
      TRANS unfolded (argument 1 checked body)
    else unfolded
  end

  fun work_result current = let
    val [changed,process,deps,pair] = snd (strip_comb current)
    val (work,state) = pairSyntax.dest_pair pair
    val (label,rest) = listSyntax.dest_cons work
    val processed = checked (list_mk_comb (process,[label,state]))
    val next = rhs (concl processed)
    val change = computeLib.EVAL_CONV (list_mk_comb (changed,[label,state,next]))
    val law = ISPECL [changed,process,deps,label,rest,state,next,rhs (concl change)]
      (DB.fetch "venomWorklistEval" "wl_step_cons_result")
    val result = MATCH_MP law (CONJ processed change)
    val labels = Conv.RATOR_CONV (Conv.RAND_CONV computeLib.EVAL_CONV)
      (rhs (concl result))
  in TRANS result labels end

  fun run_prefix current initial = let
    val prefix = case Redblackmap.peek (!prefixes,current) of
        SOME theorem => theorem | NONE => initial
    val body = rhs (concl prefix)
    fun remember equation =
      (prefixes := Redblackmap.insert (!prefixes,current,equation); NONE)
    val (head,args) = strip_comb body
    fun describe expression = let val (operator,values) = strip_comb expression
      in (if is_const operator then #Name (dest_thy_const operator) else "lambda") ^
        "/" ^ Int.toString (length values) end
    fun timed phase run = evalCompilerBytecodeLib.timed_evaluation
      (if is_const (fst (strip_comb current)) then fst (strip_comb current)
       else prim_mk_const {Thy="list",Name="FOLDL"}) phase run
  in if is_comb body andalso is_abs (rator body) then
      remember (TRANS prefix (BETA_CONV body))
    else if is_comb body andalso is_comb (rator body) andalso
        is_abs (rator (rator body)) then
      remember (TRANS prefix (Conv.RATOR_CONV BETA_CONV body))
    else if same_const head (prim_mk_const {Thy="pair",Name="UNCURRY"}) andalso
        length args = 2 then
      if pairSyntax.is_pair (List.nth (args,1)) then
        remember (TRANS prefix (Conv.REWR_CONV
          (DB.fetch "pair" "UNCURRY_DEF") body))
      else remember (TRANS prefix (argument 2 evaluate body))
    else if same_const head ``LET`` then let
      val expression = List.nth (args,1)
      val value = timed ("dominator binding " ^ describe expression)
        (fn () => evaluate expression)
      val projected = Conv.RAND_CONV (fn _ => value) body
      val exposed = Conv.REWR_CONV boolTheory.LET_THM (rhs (concl projected))
      val reduced = Conv.FIRST_CONV [BETA_CONV,pairLib.PAIRED_BETA_CONV]
        (rhs (concl exposed))
    in remember (TRANS prefix (TRANS projected (TRANS exposed reduced))) end
    else if boolSyntax.is_cond body then let
      val condition = argument 1 evaluate body
      val selected = Conv.FIRST_CONV (map Conv.REWR_CONV
        (CONJUNCTS (SPEC_ALL boolTheory.COND_CLAUSES))) (rhs (concl condition))
    in remember (TRANS prefix (TRANS condition selected)) end
    else case List.find (fn (operator,arity) =>
        same_const head operator andalso length args = arity) (entries ()) of
      SOME _ => SOME (TRANS prefix (checked body))
    | NONE => SOME (TRANS prefix (timed ("dominator residual " ^ describe body)
        (fn () => if is_const head andalso
            String.isPrefix "recordtype.df_state." (#Name (dest_thy_const head)) andalso
            String.isSuffix "_fupd" (#Name (dest_thy_const head)) then
            record_result body else evaluate body)))
  end

  fun binding_step current = let
    val {Thy,Name,...} = dest_thy_const (fst (strip_comb current))
    val exposed = if Name = "walk_to_idom" andalso
        numSyntax.int_of_term (List.nth (snd (strip_comb current),4)) <> 0 then
        argument 5 numLib.num_CONV current else REFL current
    val unfolded = Conv.FIRST_CONV (map Conv.REWR_CONV (CONJUNCTS
      (SPEC_ALL (DB.fetch Thy (Name ^ "_def"))))) (rhs (concl exposed))
  in run_prefix current (TRANS exposed unfolded) end

  fun fold_result current = let
    fun timed phase run = evalCompilerBytecodeLib.timed_evaluation
      (prim_mk_const {Thy="list",Name="FOLDL"}) phase run
    val unfolded = timed "dominator fold constructor" (fn () => Conv.FIRST_CONV
      (map Conv.REWR_CONV (CONJUNCTS (SPEC_ALL listTheory.FOLDL))) current)
    val body = rhs (concl unfolded)
  in if not (same_const (fst (strip_comb body))
      (prim_mk_const {Thy="list",Name="FOLDL"})) then SOME unfolded
    else let
      val call = List.nth (snd (strip_comb body),1)
      val known = timed "dominator fold step cache"
        (fn () => Redblackmap.peek (!fold_steps,call))
      val prepared = case known of
          SOME theorem => SOME theorem
        | NONE => timed "dominator fold application"
            (fn () => run_prefix call (REFL call))
    in case prepared of NONE => NONE
    | SOME step => let
        val () = fold_steps := Redblackmap.insert (!fold_steps,call,step)
        val projected = timed "dominator fold congruence"
          (fn () => argument 2 (fn _ => step) body)
        val tail = timed "dominator fold tail"
          (fn () => checked (rhs (concl projected)))
      in SOME (TRANS unfolded (TRANS projected tail)) end
    end
  end

  fun warm_call call goal =
    if complete call then Tactical.ALL_TAC goal
    else if not (Option.isSome (!active)) orelse
        not (aconv (valOf (!active)) call) then
      (active := SOME call;
       pending := [rhs (concl (evalCompilerBytecodeLib.normalize_call call))];
       Tactical.ALL_TAC goal)
    else (case !pending of
        [] => (completed := call :: !completed; Tactical.ALL_TAC goal)
      | current::rest => let
          val head = fst (strip_comb current)
          val {Name,...} = dest_thy_const head
          val prepared = evalCompilerBytecodeLib.timed_evaluation head
            "dominator dataflow step" (fn () =>
              if Name = "WHILE" then SOME (compilerDftWorklistEvalLib.while_result current)
              else if Name = "wl_iterate" then
                SOME (compilerDftWorklistEvalLib.iterate_result current)
              else if Name = "FOLDL" then fold_result current
              else if Name = "FUNION" then SOME (union_result current)
              else if Name = "wl_step" then SOME (work_result current)
              else binding_step current)
        in case prepared of NONE => Tactical.ALL_TAC goal
        | SOME certificate =>
          (evalCompilerBytecodeLib.register_compile_eval certificate;
           equations := Redblackmap.insert (!equations,current,certificate);
           evalCompilerBytecodeLib.pending_stage_values :=
             (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values;
           pending := rest; Tactical.ALL_TAC goal)
        end)
    handle evalCompilerBytecodeLib.PlannerBoundary child =>
      (pending := child :: !pending; Tactical.ALL_TAC goal)

  fun warm_context context goal =
    if Option.isSome (!compilerReadyContextEvalLib.active) andalso
        aconv (valOf (!compilerReadyContextEvalLib.active)) context then
      (case !compilerReadyContextEvalLib.pending of
          SOME (func::_,1) => let
            val call = boolSyntax.list_mk_icomb
              (prim_mk_const {Thy="dominatorDefs",Name="dom_fixpoint"},[func])
            fun remaining () = let
              val cfg_call = boolSyntax.list_mk_icomb
                (prim_mk_const {Thy="cfgDefs",Name="cfg_analyze"},[func])
              val cfg = rhs (concl (Redblackmap.find
                (!compilerReadyCfgEvalLib.completed,cfg_call)))
              val dom_call = boolSyntax.list_mk_icomb
                (prim_mk_const {Thy="dominatorDefs",Name="dom_analyze"},[cfg,func])
              val candidate = case Redblackmap.peek (!compilerReadyCfgEvalLib.work,dom_call) of
                  NONE => NONE
                | SOME prefix => let val (head,args) = strip_comb (rhs (concl prefix))
                  in if same_const head ``LET`` then SOME (List.nth (args,1)) else NONE end
            in case candidate of
                SOME query =>
                  if List.exists (fn (head,arity) =>
                      same_const (fst (strip_comb query)) head andalso
                      length (snd (strip_comb query)) = arity) (entries ()) andalso
                      not (complete query) then warm_call query goal
                  else compilerReadyUseEvalLib.warm_context context goal
              | NONE => compilerReadyUseEvalLib.warm_context context goal
            end
          in if complete call then remaining () else warm_call call goal end
        | _ => compilerReadyUseEvalLib.warm_context context goal)
    else compilerReadyUseEvalLib.warm_context context goal
end

