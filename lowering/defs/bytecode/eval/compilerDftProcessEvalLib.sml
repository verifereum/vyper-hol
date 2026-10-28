(* TOP-LEVEL: warm_call. Compose the original missing/converged/rescheduled
   block cases from checked children, with instruction-bearing values opaque. *)
structure compilerDftProcessEvalLib = struct
  open HolKernel boolLib
  fun head theory name = prim_mk_const {Thy=theory,Name=name}
  val process_head = head "dftDefs" "dft_process_one"
  val lookup_head = head "venomInst" "lookup_block"
  val analyze_head = head "stackOrderInternalDefs" "so_analyze_block"
  val record_head = head "stackOrderInternalDefs" "so_record_from_to"
  val order_head = compilerDftWorklistEvalLib.order_head
  val block_head = head "dftDefs" "dft_block"
  val map_head = head "list" "MAP"
  val reverse_head = head "list" "REVERSE"
  val lookup_map_head = head "finite_map" "FLOOKUP"
  val preds_head = head "cfgDefs" "cfg_preds_of"
  val call = compilerDftSuccessorEvalLib.call
  val field = compilerDftSuccessorEvalLib.field
  val projection = compilerDftSuccessorEvalLib.projection
  val checked = compilerDftBoundaryEvalLib.checked

  fun with_blocks func blocks = Parse.Term
    [QUOTE "(",ANTIQUOTE func,QUOTE ") with fn_blocks := (",ANTIQUOTE blocks,QUOTE ")"]

  fun replace_query blocks label replacement = let
    val block = genvar (listSyntax.dest_list_type (type_of blocks))
    val body = boolSyntax.mk_cond
      (mk_eq (field block "bb_label",label),replacement,block)
  in call map_head [mk_abs (block,body),blocks] end

  fun replacement_result blocks label replacement = let
    val (values,ty) = listSyntax.dest_list blocks
    val variables = map (genvar o type_of) values
    val replacement_var = genvar (type_of replacement)
    val labels = map (fn block => projection block "bb_label") values
    val premises = ListPair.map (fn (block,equation) =>
      mk_eq (field block "bb_label",rhs (concl equation))) (variables,labels)
    val schema = simpLib.SIMP_CONV (bossLib.srw_ss ())
      (listTheory.MAP :: map ASSUME premises)
      (replace_query (listSyntax.mk_list (variables,ty)) label replacement_var)
    val () = if listSyntax.is_list (rhs (concl schema)) then ()
      else raise Fail "DFT block replacement remained symbolic"
    val guarded = List.foldr (fn (p,th) => DISCH p th) schema premises
    val concrete = INST ((replacement_var |-> replacement) ::
      ListPair.map (fn (v,x) => v |-> x) (variables,values)) guarded
  in List.foldl (fn (fact,th) => MP th fact) concrete labels end

  fun process_result current = let
    val [cfg,live,func,state,label] = snd (strip_comb current)
    val bindings = ref []
    val premises = ref ([] : term list)
    val facts = ref ([] : thm list)
    fun opaque actual = let val variable = genvar (type_of actual)
      in bindings := (variable |-> actual) :: !bindings; variable end
    fun add left right theorem =
      (premises := mk_eq (left,right) :: !premises; facts := theorem :: !facts)
    val cv = opaque cfg
    val lv = opaque live
    val fv = opaque func
    val sv = opaque state
    fun finish () = let
      val conditions = rev (!premises)
      val schema = simpLib.SIMP_CONV (bossLib.srw_ss ())
        (DB.fetch "dftDefs" "dft_process_one_def" :: boolTheory.LET_THM ::
         pairTheory.pair_case_thm :: map ASSUME conditions)
        (call process_head [cv,lv,fv,sv,label])
      val guarded = List.foldr (fn (p,th) => DISCH p th) schema conditions
    in List.foldl (fn (fact,th) => MP th fact)
      (INST (!bindings) guarded) (rev (!facts)) end
    val blocks_eq = projection state "dls_blocks"
    val blocks = rhs (concl blocks_eq)
    val bv = opaque blocks
    val () = add (field sv "dls_blocks") bv blocks_eq
    val cur_fn = with_blocks func blocks
    val found_raw = compilerDftSuccessorEvalLib.lookup_result cur_fn label
    val found_inputs = Conv.RAND_CONV
      (fn _ => projection cur_fn "fn_blocks") (lhs (concl found_raw))
    val found = TRANS (SYM found_inputs) found_raw
  in if optionSyntax.is_none (rhs (concl found)) then
      (add (call lookup_head [label,bv]) (rhs (concl found)) found; finish ())
    else let
      val block = optionSyntax.dest_some (rhs (concl found))
      val bbv = opaque block
      val () = add (call lookup_head [label,bv]) (optionSyntax.mk_some bbv) found
      val instructions_eq = projection block "bb_instructions"
      val instructions = rhs (concl instructions_eq)
      val iv = opaque instructions
      val () = add (field bbv "bb_instructions") iv instructions_eq
      val from_to_eq = projection state "dls_from_to"
      val from_to = rhs (concl from_to_eq)
      val mv = opaque from_to
      val () = add (field sv "dls_from_to") mv from_to_eq
      val analyzed = checked (call analyze_head [cfg,live,from_to,label,instructions])
      val (needed,other) = pairSyntax.dest_pair (rhs (concl analyzed))
      val nv = opaque needed
      val ov = opaque other
      val () = add (call analyze_head [cv,lv,mv,label,iv])
        (pairSyntax.mk_pair (nv,ov)) analyzed
      val recorded = checked (call record_head [cfg,from_to,label,needed])
      val map1 = rhs (concl recorded)
      val m1v = opaque map1
      val () = add (call record_head [cv,mv,label,nv]) m1v recorded
      val ordered = checked (call order_head [cfg,live,cur_fn,map1,label])
      val (order,map2) = pairSyntax.dest_pair (rhs (concl ordered))
      val ordv = opaque order
      val m2v = opaque map2
      val () = add (call order_head [cv,lv,with_blocks fv bv,m1v,label])
        (pairSyntax.mk_pair (ordv,m2v)) ordered
      val last_eq = projection state "dls_last_order"
      val last = rhs (concl last_eq)
      val lastv = opaque last
      val () = add (field sv "dls_last_order") lastv last_eq
      val previous_eq = computeLib.EVAL_CONV (call lookup_map_head [last,label])
      val converged = if optionSyntax.is_none (rhs (concl previous_eq)) then
          (add (call lookup_map_head [lastv,label])
            (rhs (concl previous_eq)) previous_eq; false)
        else let
          val previous = optionSyntax.dest_some (rhs (concl previous_eq))
          val prevv = opaque previous
          val () = add (call lookup_map_head [lastv,label])
            (optionSyntax.mk_some prevv) previous_eq
          val comparison = if aconv previous order then EQT_INTRO (REFL previous)
            else computeLib.EVAL_CONV (mk_eq (previous,order))
          val () = add (mk_eq (prevv,ordv)) (rhs (concl comparison)) comparison
        in aconv (rhs (concl comparison)) T end
    in if converged then finish () else let
        val reversed = computeLib.EVAL_CONV (call reverse_head [order])
        val rev_order = rhs (concl reversed)
        val rv = opaque rev_order
        val () = add (call reverse_head [ordv]) rv reversed
        val scheduled = checked (call block_head [rev_order,block])
        val replacement = rhs (concl scheduled)
        val newbbv = opaque replacement
        val () = add (call block_head [rv,bbv]) newbbv scheduled
        val replaced = replacement_result blocks label replacement
        val newbv = opaque (rhs (concl replaced))
        val () = add (replace_query bv label newbbv) newbv replaced
        val preds = computeLib.EVAL_CONV (call preds_head [cfg,label])
        val pv = opaque (rhs (concl preds))
        val () = add (call preds_head [cv,label]) pv preds
      in finish () end
    end
  end

  fun warm_call root goal =
    (case !compilerDftWorklistEvalLib.pending of
      current::_ => if Option.isSome (!compilerDftWorklistEvalLib.active) andalso
          aconv (valOf (!compilerDftWorklistEvalLib.active)) root andalso
          same_const (fst (strip_comb current)) process_head then let
        val certificate = evalCompilerBytecodeLib.timed_evaluation process_head
          "checked block worklist composition" (fn () => process_result current)
        val () = if aconv (lhs (concl certificate)) current then ()
          else raise Fail "DFT block worklist changed its original call"
        val () = evalCompilerBytecodeLib.register_compile_eval certificate
        val () = compilerDftWorklistEvalLib.equations := Redblackmap.insert
          (!compilerDftWorklistEvalLib.equations,current,certificate)
        val () = evalCompilerBytecodeLib.pending_stage_values :=
          (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
        val () = compilerDftWorklistEvalLib.pending := tl (!compilerDftWorklistEvalLib.pending)
      in Tactical.ALL_TAC goal end
      else compilerDftSuccessorEvalLib.warm_call root goal
    | [] => compilerDftSuccessorEvalLib.warm_call root goal)
    handle evalCompilerBytecodeLib.PlannerBoundary child =>
      (compilerDftWorklistEvalLib.pending := child :: !compilerDftWorklistEvalLib.pending;
       Tactical.ALL_TAC goal)
end
