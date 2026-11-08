(* Normalize the completed SUE function before DFT. Follow typed record
   field lenses, then flatten each block independently; no DFT fuel changes. *)
structure evalCompilerBaseDftLib = struct
open HolKernel Parse boolLib bossLib
open evalCompilerBaseLib

fun base_dft_argument i n convert =
  if i = n - 1 then RAND_CONV convert
  else RATOR_CONV (base_dft_argument i (n - 1) convert)

(* Record literals are field-update chains over ARB. Their constant setters
   can be normalized directly without evaluating discarded older fields. *)
fun base_dft_field_view ty name record = let
  val fields = TypeBase.fields_of ty
  val (_, {accessor,fupd,...}) = valOf (List.find (fn (n,_) => n = name) fields)
  val instantiations = match_type (fst (dom_rng (type_of accessor))) ty
  val accessor = inst instantiations accessor
  val fupd = inst instantiations fupd
  fun constant_setter setter = let
    val (head,args) = strip_comb setter
  in if is_const head andalso #Thy (dest_thy_const head) = "combin" andalso
        #Name (dest_thy_const head) = "K" andalso length args = 1 then
       (hd args,fn convert => RAND_CONV convert setter)
     else if is_abs setter then let
       val (v,body) = dest_abs setter
     in if free_in v body then raise Fail "DFT record setter is not constant"
        else (body,fn convert => ABS_CONV convert setter) end
     else raise Fail ("DFT record setter head=" ^ term_to_string head ^
       " arguments=" ^ Int.toString (length args))
  end
  fun view tm = let val (head,args) = strip_comb tm in
    if aconv head fupd andalso length args = 2 then let
      val (value,inside) = constant_setter (hd args)
    in (value,fn convert => RATOR_CONV
      (RAND_CONV (fn _ => inside convert)) tm) end
    else if length args = 2 andalso List.exists
        (fn (_, {fupd,...}) => aconv head (inst instantiations fupd)) fields then let
      val (value,inside) = view (List.nth(args,1))
    in (value,fn convert => RAND_CONV (fn _ => inside convert) tm) end
    else if List.exists (aconv head o inst instantiations)
        (TypeBase.constructors_of ty) then let
      val field_ty = snd (dom_rng (type_of accessor))
      val matches = List.filter (fn (_,arg) => type_of arg = field_ty)
        (ListPair.zip (List.tabulate(length args,fn i => i),args))
      val (index,value) = case matches of [entry] => entry
        | _ => raise Fail "DFT constructor field is not uniquely typed"
    in (value,fn convert => base_dft_argument index (length args) convert tm) end
    else raise Fail ("DFT record has no field " ^ name ^ "; head=" ^
      (if is_const head then #Name (dest_thy_const head)
       else if is_abs head then "<lambda>" else "<variable>"))
  end
in view record end

(* Normalize only the current fields before the next DFT iteration. *)
fun base_dft_loop_field name g =
  if entry_has_call ["dft_loop_run_fuel"] (lhs (snd g)) then
    base_eval_stage (RAND_CONV (LAND_CONV (fn state => let
      val (_,inside) = base_dft_field_view (type_of state) name state
    in inside (computeLib.WEAK_CBV_CONV base_dft_cs) end)))
      "dft_loop_run_fuel" g
  else ALL_TAC g

fun base_dft_input_convert convert = base_eval_stage (RAND_CONV convert) "dft_fn"
val base_dft_project = base_dft_input_convert
  (computeLib.WEAK_CBV_CONV base_dom_cs)
val base_dft_blocks_project = base_dft_input_convert (fn func => let
  val (_,inside) = base_dft_field_view ``:ir_function`` "fn_blocks" func
in inside (computeLib.WEAK_CBV_CONV base_dom_cs) end)
fun base_dft_normalize_block i = let
  val () = if i >= 0 andalso i < 32 then ()
    else raise Fail "DFT block normalization index is outside 0..31"
  fun element 0 convert = RATOR_CONV (RAND_CONV convert)
    | element n convert = RAND_CONV (element (n - 1) convert)
  fun normalize func = let
    val (value,inside) = base_dft_field_view ``:ir_function`` "fn_blocks" func
    val blocks = fst (listSyntax.dest_list value)
    val () = if length blocks <= 32 then ()
      else raise Fail "DFT input needs more explicit block normalization slots"
  in if i >= length blocks then REFL func
     else inside (element i computeLib.EVAL_CONV)
  end
in normalize end
fun base_dft_input_block i =
  base_dft_input_convert (base_dft_normalize_block i)
fun base_dft_normalize_field i = let
  val fields = TypeBase.fields_of ``:ir_function``
  val () = if i >= 0 andalso i < length fields then ()
    else raise Fail "DFT function field index is out of range"
  val (name,_) = List.nth(fields,i)
in fn func => let
     val (_,inside) = base_dft_field_view ``:ir_function`` name func
   in inside computeLib.EVAL_CONV end
end
fun base_dft_input_field i =
  base_dft_input_convert (base_dft_normalize_field i)
(* Derive normalization coverage from the record, not a stale field count. *)
fun base_dft_all_fields normalize =
  EVERY (List.tabulate
    (length (TypeBase.fields_of ``:ir_function``), normalize))
val base_dft_input_fields = base_dft_all_fields base_dft_input_field
fun base_dft_check_function func = let
  val (value,_) = base_dft_field_view ``:ir_function`` "fn_blocks" func
  val blocks = fst (listSyntax.dest_list value)
  val () = if length blocks <= 32 then ()
    else raise Fail "DFT input block normalization is incomplete"
  fun checked_block block = let
    val (instructions,_) =
      base_dft_field_view ``:basic_block`` "bb_instructions" block
    val _ = listSyntax.dest_list instructions
  in if entry_has_call ["APPEND"] instructions then
      raise Fail "DFT input retains instruction concatenations" else () end
in List.app checked_block blocks end
fun base_dft_input_finish g = let
  val query = find_term (flow_call "dft_fn") (lhs (snd g))
  val () = base_dft_check_function (rand query)
in ALL_TAC g end

(* The completed traversal still has a tuple-case continuation and block
   concatenations. Normalize its actual function before the supply checks. *)
val base_dft_result_project = CONV_TAC
  (LAND_CONV (computeLib.WEAK_CBV_CONV base_dom_cs))
val base_dft_result_blocks_project = CONV_TAC (LAND_CONV (fn func => let
  val (_,inside) = base_dft_field_view ``:ir_function`` "fn_blocks" func
in inside (computeLib.WEAK_CBV_CONV base_dom_cs) end))
fun base_dft_result_block i = CONV_TAC
  (LAND_CONV (base_dft_normalize_block i))
fun base_dft_result_field i = CONV_TAC
  (LAND_CONV (base_dft_normalize_field i))
val base_dft_result_fields = base_dft_all_fields base_dft_result_field
fun base_dft_result_finish g =
  (base_dft_check_function (lhs (snd g)); ALL_TAC g)

(* Compact one current worklist field without walking discarded record updates. *)
val base_dft_flow_cs = entry_plan_readonly_cs
  [``:'a df_state``, ``:ir_function``, ``:cfg_analysis``]
(* Preserve the old instruction map while computing one block's updates. *)
val base_dft_lazy_maps_cs = computeLib.copy base_dft_flow_cs
  |> (fn cs => computeLib.set_skip cs finite_mapSyntax.fupdate_tm (SOME 0))
(* A skipped update pair is opaque to compute's pattern matcher. Use the
   public raw-term lookup equations, then recompile their guard callers. *)
val base_dft_guard_cs = computeLib.copy base_dft_lazy_maps_cs
  |> (fn cs => computeLib.scrub_const cs finite_mapSyntax.flookup_tm)
  |> computeLib.add_conv (finite_mapSyntax.flookup_tm, 2,
       FIRST_CONV [REWR_CONV finite_mapTheory.FLOOKUP_UPDATE,
                   REWR_CONV finite_mapTheory.FLOOKUP_EMPTY])
  |> computeLib.add_thms [dfAnalyzeDefsTheory.df_at_def,
       dfAnalyzeDefsTheory.df_at_funion_compute,
       dfAnalyzeDefsTheory.df_boundary_def, livenessDefsTheory.liveness_changed_def]
fun base_dft_push_union tm =
  if finite_mapSyntax.is_fempty (fst (finite_mapSyntax.dest_funion tm)) then
    REWR_CONV finite_mapTheory.FUNION_FEMPTY_1 tm
  else (REWR_CONV finite_mapTheory.FUNION_FUPDATE_1 THENC
    RATOR_CONV (RAND_CONV base_dft_push_union)) tm
fun base_dft_check_map tm = let
  val (base,updates) = finite_mapSyntax.strip_fupdate tm
in if finite_mapSyntax.is_fempty base andalso List.all
     (fn update => can listSyntax.dest_list
       (snd (pairSyntax.dest_pair update))) updates then ()
   else raise Fail "instruction map retains deferred values"
end
fun base_dft_block_map tm = let
  val th = computeLib.CBV_CONV base_dft_flow_cs tm
  val () = base_dft_check_map (rhs (concl th))
in th end
fun base_dft_merge_inst tm =
  if finite_mapSyntax.is_funion tm then
    (RATOR_CONV (RAND_CONV base_dft_block_map) THENC
     RAND_CONV (computeLib.WEAK_CBV_CONV base_dft_lazy_maps_cs) THENC
     base_dft_push_union) tm
  else if finite_mapSyntax.is_fempty tm orelse finite_mapSyntax.is_fupdate tm then
    (base_dft_check_map tm; REFL tm)
  else raise Fail "instruction map is neither literal nor a block-map union"
fun base_dft_flow_project g =
  if entry_has_call ["wl_iterate"] (lhs (snd g)) then
    base_eval_stage (RAND_CONV
      (computeLib.WEAK_CBV_CONV base_dft_flow_cs)) "wl_iterate" g
  else ALL_TAC g
fun base_dft_flow_field name convert g =
  if entry_has_call ["wl_iterate"] (lhs (snd g)) then
    base_eval_stage (RAND_CONV (fn state => let
      val (_,inside) = base_dft_field_view (type_of state) name state
    in inside convert end)) "wl_iterate" g
  else ALL_TAC g
(* Keep exception keys canonical and time bounded batches of kernel updates. *)
val base_dft_map_equation = ref
  (NONE : (term * (term * term) list * thm) option)
fun base_dft_map_begin name = base_dft_flow_field name (fn tm => let
  val (base,updates) = finite_mapSyntax.strip_fupdate tm
  val entries = List.map pairSyntax.dest_pair updates
  fun distinct [] = true
    | distinct ((key,_) :: rest) =
        not (List.exists (fn (next,_) => aconv key next) rest) andalso distinct rest
  val empty = inst [alpha |-> fst (finite_mapSyntax.dest_fmap_ty (type_of base))]
    pred_setSyntax.empty_tm
  val initial = if distinct entries then NONE
    else SOME (tm,entries,ISPECL [empty,base] finite_mapTheory.fmap_EQ_UPTO___EQ)
in base_dft_map_equation := initial; REFL tm end)
fun base_dft_map_tick g =
  case !base_dft_map_equation of NONE => ALL_TAC g
  | SOME (target,entries,initial) => let
      fun advance 0 rest th = (rest,th)
        | advance _ [] th = ([],th)
        | advance n ((key,value) :: rest) th = let
            val body = concl th
            val exceptions = rand body
            val right = rand (rator body)
            val left = rand (rator (rator body))
            val shadowed = List.exists (fn (next,_) => aconv key next) rest
            val missing = List.exists (aconv key) (pred_setSyntax.strip_set exceptions)
            val rule = if shadowed then finite_mapTheory.fmap_EQ_UPTO___FUPDATE_SING
              else if missing then finite_mapTheory.fmap_EQ_UPTO___FUPDATE_BOTH
              else finite_mapTheory.fmap_EQ_UPTO___FUPDATE_BOTH___NO_DELETE
            val next = MP (ISPECL [left,right,exceptions,key,value] rule) th
            val normalized = if missing andalso not shadowed then
              CONV_RULE (RAND_CONV (pred_setLib.DELETE_CONV computeLib.EVAL_CONV)) next
              else next
          in advance (n - 1) rest normalized end
      val (remaining,next) = advance 32 entries initial
    in base_dft_map_equation := SOME (target,remaining,next); ALL_TAC g end
fun base_dft_map_finish name g =
  case !base_dft_map_equation of NONE => ALL_TAC g
  | SOME (target,remaining,th) => let
      val () = if List.null remaining then ()
        else raise Fail "map normalization needs more finite update boundaries"
      val () = if pred_setSyntax.is_empty (rand (concl th)) then ()
        else raise Fail "map normalization retains exception keys"
      val result = CONV_RULE (REWR_CONV finite_mapTheory.fmap_EQ_UPTO___EMPTY) th
      val lifted = base_dft_flow_field name (fn tm =>
        if aconv tm target then result else raise Fail "map normalization target changed") g
    in base_dft_map_equation := NONE; lifted end
val base_dft_flow_compact = base_dft_flow_field "ds_boundary"
  (computeLib.WEAK_CBV_CONV base_dft_flow_cs THENC
   Conv.QCONV entry_compact_maps)

(* Rewrite one demanded worklist call; deferred compiler data is not searched
   again while lifting the resulting equality into the fragment. *)
fun base_dft_flow_part name convert = TRY (base_eval_stage convert name)
(* Compute the final block state before its two projections duplicate it. *)
val base_dft_stack_order = base_dft_flow_part "so_analyze_block"
  (REWR_CONV stackOrderInternalDefsTheory.so_analyze_block_def THENC
   REWR_CONV boolTheory.LET_THM THENC TRY_CONV BETA_CONV THENC
   RAND_CONV (computeLib.CBV_CONV base_dft_flow_cs) THENC
   REWR_CONV boolTheory.LET_THM THENC TRY_CONV BETA_CONV THENC
   computeLib.WEAK_CBV_CONV base_dft_flow_cs)
val base_dft_flow_begin = base_dft_flow_part "wl_iterate"
  evalCompilerFlowStepLib.flow_begin
val base_dft_flow_step_open = base_dft_flow_part "wl_step"
  (RAND_CONV (LAND_CONV computeLib.EVAL_CONV) THENC FIRST_CONV
    [REWR_CONV worklistStepComputeTheory.wl_step_cons,
     REWR_CONV worklistStepComputeTheory.wl_step_nil])
(* Evaluate the successor join before the block fold duplicates its value. *)
val base_dft_flow_live_out = base_dft_flow_part "WHILE"
  (RAND_CONV (RAND_CONV (TRY_CONV
    (base_first_conv (flow_call "liveness_block")
      (REWR_CONV livenessDefsTheory.liveness_block_def THENC
       RAND_CONV (fn tm => let
         val th = computeLib.CBV_CONV base_dft_flow_cs tm
         val () = if can listSyntax.dest_list (rhs (concl th)) then ()
           else raise Fail "incomplete liveness successor join"
       in th end) THENC
       REWR_CONV boolTheory.LET_THM THENC TRY_CONV BETA_CONV)))))
val base_dft_flow_transfer = base_dft_flow_part "WHILE"
  (RAND_CONV (RAND_CONV
    (computeLib.WEAK_CBV_CONV base_dft_flow_cs)))
(* Liveness also attaches a new instruction map, normalized separately. *)
val base_dft_flow_live_transfer = base_dft_flow_part "WHILE"
  (RAND_CONV (RAND_CONV (Lib.with_flag
    (computeLib.stoppers, SOME (fn t =>
      is_const t andalso same_const t finite_mapSyntax.funion_tm))
    (computeLib.WEAK_CBV_CONV base_dft_lazy_maps_cs))))
val base_dft_flow_merge_inst = base_dft_flow_part "WHILE"
  (RAND_CONV (RAND_CONV (fn state => let
    val (_,inside) = base_dft_field_view (type_of state) "ds_inst" state
  in inside base_dft_merge_inst end)))
val base_dft_flow_bind = base_dft_flow_part "WHILE"
  (RAND_CONV (REWR_CONV boolTheory.LET_THM THENC TRY_CONV BETA_CONV))
val base_dft_flow_changed = base_dft_flow_part "WHILE"
  (RAND_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV
    (base_boolean_conv (computeLib.WEAK_CBV_CONV base_dft_guard_cs)
      "worklist changed")))))
val base_dft_flow_select = base_dft_flow_part "WHILE"
  (RAND_CONV (FIRST_CONV (List.map REWR_CONV
    (Drule.BODY_CONJUNCTS boolTheory.COND_CLAUSES))))
val base_dft_flow_resume = base_dft_flow_part "WHILE"
  (RAND_CONV (LAND_CONV (computeLib.WEAK_CBV_CONV base_dft_lazy_maps_cs)) THENC
   REWR_CONV (GSYM worklistDefsTheory.wl_iterate_def))
end
