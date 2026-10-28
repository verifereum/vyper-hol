(* Observe only metadata fields required by the original effect contract.
   Symbolic unfolding precedes instantiation with instruction-bearing records. *)
structure compilerPassEffectsEvalLib = struct
  open HolKernel boolLib
  fun head name = prim_mk_const {Thy="venomPassDispatcher",Name=name}

  fun definitions () =
    DB.fetch "venomPassSchedule" "fn_pass_tag_def" ::
    map (DB.fetch "venomPassDispatcher")
      ["fn_pass_effects_hold_def","fn_metadata_effect_holds_def",
       "fn_static_layout_effect_holds_def","fn_abi_effect_holds_def",
       "fn_pass_metadata_effect_def","fn_pass_static_layout_effect_def",
       "fn_pass_abi_effect_def"] @
    map (DB.fetch "venomInst")
      ["fn_identity_metadata_eq_def","fn_static_input_eq_def",
       "fn_static_layout_eq_def","fn_fmp_convention_eq_def"]

  fun record_rules typ = let
    val {Thy,Tyop,...} = dest_thy_type typ
    val fields = List.concat (map (CONJUNCTS o SPEC_ALL)
      (TypeBase.accessors_of typ))
    val updates = CONJUNCTS (SPEC_ALL (DB.fetch Thy (Tyop ^ "_accfupds")))
  in (map (fst o strip_comb o lhs o concl) fields,fields @ updates) end

  fun observe types body = let
    val information = map record_rules types
    val getters = List.concat (map #1 information)
    val rules = map Conv.REWR_CONV
      (DB.fetch "combin" "K_THM" :: List.concat (map #2 information))
    val k = prim_mk_const {Thy="combin",Name="K"}
    fun project term = let
      val operator = fst (strip_comb term)
    in if is_const operator andalso
        (same_const operator k orelse
         List.exists (same_const operator) getters) then
      ((let val step = Conv.FIRST_CONV rules term
        in if aconv term (rhs (concl step)) then step
           else TRANS step (project (rhs (concl step))) end)
       handle HOL_ERR _ => REFL term)
    else if List.exists (fn typ => type_of term = typ) types then REFL term
    else if is_comb term then Conv.COMB_CONV project term
    else if is_abs term then Conv.ABS_CONV project term else REFL term
    end
  in project body end

  fun effects_step current = let
    val [tag,func_before,out] = snd (strip_comb current)
    val before_var = mk_var ("effects_before",type_of func_before)
    val out_var = mk_var ("effects_out",type_of out)
    val abstract = list_mk_comb (head "fn_pass_effects_hold",
      [tag,before_var,out_var])
    val schema = simpLib.SIMP_CONV (bossLib.srw_ss ()) (definitions ()) abstract
    val instantiated = INST [before_var |-> func_before,out_var |-> out] schema
    val projected = observe [type_of func_before,type_of out]
      (rhs (concl instantiated))
  in TRANS instantiated projected end

  fun checked current =
    case Redblackmap.peek (!compilerPassEvalLib.equations,current) of
      SOME theorem => theorem
    | NONE => (case List.find (fn theorem => aconv current (lhs (concl theorem)))
          (!evalCompilerBytecodeLib.compiler_certificates) of
        SOME theorem => theorem
      | NONE => raise evalCompilerBytecodeLib.PlannerBoundary current)

  fun sue_function_step current = let
    val [supply,func] = snd (strip_comb current)
    val dfg_eq = checked (mk_comb
      (prim_mk_const {Thy="dfgDefs",Name="dfg_build_function"},func))
    val blocks = Parse.Term [QUOTE "(",ANTIQUOTE func,QUOTE ").fn_blocks"]
    val projected = observe [type_of func] blocks
    val call = list_mk_comb (prim_mk_const
      {Thy="singleUseExpansionDefs",Name="sue_expand_blocks_supply"},
      [rhs (concl dfg_eq),supply,rhs (concl projected)])
    val blocks_eq = TRANS
      (compilerSingleUseEvalLib.argument 3 (fn _ => projected)
        (list_mk_comb (fst (strip_comb call),
          [rhs (concl dfg_eq),supply,blocks]))) (checked call)
  in MATCH_MP (DB.fetch "venomFnScheduleCases"
       "sue_expand_function_supply_result") (CONJ dfg_eq blocks_eq) end

  (* Compose a cons from checked children before exposing its continuation.
     The original six guards are projected and certified independently. *)
  fun fold_step current = let
    val [runner,rpolicy,passes,unit,supply,func,labels] = snd (strip_comb current)
    val (pass,_) = listSyntax.dest_cons passes
    val unit_head = prim_mk_const
      {Thy="venomFnScheduleRunner",Name="unit_with_current_fn"}
    val observed_eq = checked
      (list_mk_comb (unit_head,[unit,func]))
    val observed = optionSyntax.dest_some (rhs (concl observed_eq))
    val output_eq = checked
      (list_mk_comb (runner,[rpolicy,pass,observed,supply,func]))
    val out = optionSyntax.dest_some (rhs (concl output_eq))
    val constructor = PART_MATCH (lhs o snd o dest_imp)
      (MATCH_MP (DB.fetch "venomFnScheduleCases"
        "run_configured_fn_pass_fold_cons_result") (CONJ observed_eq output_eq))
      current
    val types = map type_of [unit,supply,func,out]
    val guard = fst (dest_imp (concl constructor))
    val projected = observe types guard
    fun certify atom =
      if is_const (fst (strip_comb atom)) andalso
          List.exists (same_const (fst (strip_comb atom)))
            (head "fn_pass_effects_hold" :: head "introduces_no_invoke_edges" ::
             compilerSupplyBoundaryEvalLib.guards ()) then
        checked atom
      else computeLib.EVAL_CONV atom
    val facts = LIST_CONJ (map (EQT_ELIM o certify)
      (strip_conj (rhs (concl projected))))
    val result = MP constructor (EQ_MP (SYM projected) facts)
    val tail = observe types (rhs (concl result))
  in TRANS result tail end

  fun sue_pass_step current = let
    val constructor = PART_MATCH (lhs o snd o dest_imp)
      (DB.fetch "venomFnScheduleCases" "execute_configured_fn_pass_sue_result")
      current
    val child = lhs (fst (dest_imp (concl constructor)))
  in MATCH_MP constructor (checked child) end

  fun configure () = let
    val scan = prim_mk_const {Thy="fcgDefs",Name="fcg_scan_function"}
    val fold = evalCompilerBytecodeLib.scheduled_fold_head
    val unit_head = prim_mk_const
      {Thy="venomFnScheduleRunner",Name="unit_with_current_fn"}
    val entries = [(fold,7),(unit_head,2),(head "fn_pass_effects_hold",3),
      (head "introduces_no_invoke_edges",2),(scan,1)] @
      map (fn name => (head name,3))
      ["fn_metadata_effect_holds","fn_static_layout_effect_holds",
       "fn_abi_effect_holds"]
    val () = compilerPassEvalLib.extend_phases entries
      [(fold,Conv.FIRST_CONV [fold_step,Conv.REWR_CONV
          (hd (CONJUNCTS (SPEC_ALL (DB.fetch "venomFnScheduleRunner"
            "run_configured_fn_pass_fold_def"))))]),
       (prim_mk_const {Thy="singleUseExpansionDefs",Name="sue_expand_function_supply"},
          sue_function_step),
       (evalCompilerBytecodeLib.scheduled_pass_head,
          Conv.FIRST_CONV [sue_pass_step,REFL]),
       (head "fn_pass_effects_hold",effects_step),
       (head "introduces_no_invoke_edges",Conv.REWR_CONV
         (DB.fetch "venomPassDispatcher" "introduces_no_invoke_edges_def")),
       (scan,Conv.REWR_CONV (DB.fetch "fcgDefs" "fcg_scan_function_def"))] []
  in app compilerPassEvalLib.install_indexed_head entries end
end
