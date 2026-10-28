(* TOP-LEVEL: warm_call. Certify successor lookup with instruction payloads
   opaque, then compose the original checked block analysis and map update. *)
structure compilerDftSuccessorEvalLib = struct
  open HolKernel boolLib
  val successor_head = prim_mk_const
    {Thy="stackOrderInternalDefs",Name="so_analyze_succ"}
  val lookup_head = prim_mk_const {Thy="venomInst",Name="lookup_block"}
  val analyze_head = prim_mk_const
    {Thy="stackOrderInternalDefs",Name="so_analyze_block"}
  val dfs_loop_head = prim_mk_const {Thy="dftDefs",Name="dfs_run_fuel"}
  fun call head args = boolSyntax.list_mk_icomb (head,args)
  fun field value name = Parse.Term [QUOTE "(",ANTIQUOTE value,QUOTE (")." ^ name)]

  fun projection value name = let
    val typ = type_of value
    val {Thy,Tyop,...} = dest_thy_type typ
    val rules = List.concat (map (CONJUNCTS o SPEC_ALL)
      (TypeBase.accessors_of typ)) @
      [DB.fetch Thy (Tyop ^ "_accfupds"),DB.fetch "combin" "K_THM"]
  in Rewrite.PURE_REWRITE_CONV rules (field value name) end

  fun lookup_result func label = let
    val blocks = projection func "fn_blocks"
    val (values,ty) = listSyntax.dest_list (rhs (concl blocks))
    val symbolic = map (genvar o type_of) values
    val labels = map (fn block => projection block "bb_label") values
    val premises = ListPair.map (fn (block,equation) =>
      mk_eq (field block "bb_label",rhs (concl equation))) (symbolic,labels)
    val schema = simpLib.SIMP_CONV (bossLib.srw_ss ())
      (DB.fetch "venomInst" "lookup_block_def" ::
       DB.fetch "list" "FIND_thm" :: map ASSUME premises)
      (call lookup_head [label,listSyntax.mk_list (symbolic,ty)])
    val guarded = List.foldr (fn (p,th) => DISCH p th) schema premises
    val concrete = INST (ListPair.map (fn (v,x) => v |-> x) (symbolic,values)) guarded
    val result = List.foldl (fn (fact,th) => MP th fact) concrete labels
    val inputs = Conv.RAND_CONV (fn _ => blocks)
      (call lookup_head [label,field func "fn_blocks"])
  in TRANS inputs result end

  fun successor_result current = let
    val [cfg,live,func,from_to,label] = snd (strip_comb current)
    val lookup = lookup_result func label
    val symbolic = map (genvar o type_of) [cfg,live,func,from_to]
    val [cfg_var,live_var,func_var,map_var] = symbolic
    val source = call successor_head (symbolic @ [label])
    val lookup_term = call lookup_head [label,field func_var "fn_blocks"]
    fun finish premises facts replacements extra = let
      val schema = simpLib.SIMP_CONV (bossLib.srw_ss ())
        (DB.fetch "stackOrderInternalDefs" "so_analyze_succ_def" ::
         boolTheory.LET_THM :: pairTheory.pair_case_thm :: map ASSUME premises) source
      val guarded = List.foldr (fn (p,th) => DISCH p th) schema premises
      val concrete = INST (replacements @ extra) guarded
    in List.foldl (fn (fact,th) => MP th fact) concrete facts end
    val replacements = ListPair.map (fn (v,x) => v |-> x)
      (symbolic,[cfg,live,func,from_to])
  in if optionSyntax.is_none (rhs (concl lookup)) then
      finish [mk_eq (lookup_term,rhs (concl lookup))] [lookup] replacements []
    else let
      val block = optionSyntax.dest_some (rhs (concl lookup))
      val instructions = projection block "bb_instructions"
      val block_var = genvar (type_of block)
      val insts_var = genvar (type_of (rhs (concl instructions)))
      val analyzed = compilerDftBoundaryEvalLib.checked
        (call analyze_head [cfg,live,from_to,label,rhs (concl instructions)])
      val (needed,other) = pairSyntax.dest_pair (rhs (concl analyzed))
      val needed_var = genvar (type_of needed)
      val other_var = genvar (type_of other)
      val premises = [mk_eq (lookup_term,optionSyntax.mk_some block_var),
        mk_eq (field block_var "bb_instructions",insts_var),
        mk_eq (call analyze_head [cfg_var,live_var,map_var,label,insts_var],
          pairSyntax.mk_pair (needed_var,other_var))]
      val composed = finish premises [lookup,instructions,analyzed] replacements
        [block_var |-> block,insts_var |-> rhs (concl instructions),
         needed_var |-> needed,other_var |-> other]
      val updated = compilerDftBoundaryEvalLib.checked (rhs (concl composed))
    in TRANS composed updated end
  end

  fun dfs_loop_result current = let
    val [step,fuel,state] = snd (strip_comb current)
    val step_var = genvar (type_of step)
    val state_var = genvar (type_of state)
    val symbolic = call dfs_loop_head [step_var,fuel,state_var]
    val unfolded = compilerDftWorklistEvalLib.unfold_dfs symbolic
    val replacements = [step_var |-> step,state_var |-> state]
  in if not (boolSyntax.is_cond (rhs (concl unfolded))) then INST replacements unfolded
    else let
      val stack = projection state "ds_stack"
      val items = rhs (concl stack)
      val empty = listSyntax.mk_nil (listSyntax.dest_list_type (type_of items))
      val shape = if listSyntax.is_nil items then
          computeLib.EVAL_CONV (mk_eq (items,empty))
        else let
          val (item,rest) = listSyntax.dest_cons items
          val item_var = genvar (type_of item)
          val rest_var = genvar (type_of rest)
          val small = computeLib.EVAL_CONV
            (mk_eq (listSyntax.mk_cons (item_var,rest_var),empty))
        in INST [item_var |-> item,rest_var |-> rest] small end
      val observed = MK_COMB
        (AP_TERM (rator (rator (mk_eq (field state "ds_stack",empty)))) stack,
         REFL empty)
      val test = TRANS observed shape
      val premise = mk_eq
        (mk_eq (field state_var "ds_stack",empty),rhs (concl test))
      val selected = simpLib.SIMP_CONV (bossLib.srw_ss ())
        [ASSUME premise] (rhs (concl unfolded))
      val prefix = MP (INST replacements
        (DISCH premise (TRANS unfolded selected))) test
      val body = rhs (concl prefix)
    in if not (same_const (fst (strip_comb body)) dfs_loop_head) then prefix
      else let
        val argument = compilerDftWorklistEvalLib.argument
        val next_fuel = argument 2 computeLib.EVAL_CONV body
        val stepped = argument 3 compilerDftBoundaryEvalLib.checked
          (rhs (concl next_fuel))
        val tail = compilerDftBoundaryEvalLib.checked (rhs (concl stepped))
      in TRANS prefix (TRANS next_fuel (TRANS stepped tail)) end
    end
  end

  fun warm_call root goal =
    (case !compilerDftWorklistEvalLib.pending of
      current::_ => if Option.isSome (!compilerDftWorklistEvalLib.active) andalso
          aconv (valOf (!compilerDftWorklistEvalLib.active)) root andalso
          List.exists (same_const (fst (strip_comb current)))
            [successor_head,dfs_loop_head] then let
        val head = fst (strip_comb current)
        val certificate = evalCompilerBytecodeLib.timed_evaluation head
          "checked successor/DFS composition"
          (fn () => if same_const head successor_head then successor_result current
            else dfs_loop_result current)
        val () = if aconv (lhs (concl certificate)) current then ()
          else raise Fail "successor composition changed its original call"
        val () = evalCompilerBytecodeLib.register_compile_eval certificate
        val () = compilerDftWorklistEvalLib.equations := Redblackmap.insert
          (!compilerDftWorklistEvalLib.equations,current,certificate)
        val () = evalCompilerBytecodeLib.pending_stage_values :=
          (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
        val () = compilerDftWorklistEvalLib.pending := tl (!compilerDftWorklistEvalLib.pending)
      in Tactical.ALL_TAC goal end
      else compilerDftSortEvalLib.warm_call root goal
    | [] => compilerDftSortEvalLib.warm_call root goal)
    handle evalCompilerBytecodeLib.PlannerBoundary child =>
      (compilerDftWorklistEvalLib.pending := child :: !compilerDftWorklistEvalLib.pending;
       Tactical.ALL_TAC goal)
end
