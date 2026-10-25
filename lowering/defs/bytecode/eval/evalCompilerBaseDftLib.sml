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
  val () = if length fields = 7 andalso i >= 0 andalso i < length fields then ()
    else raise Fail "DFT function field index is out of range"
  val (name,_) = List.nth(fields,i)
in fn func => let
     val (_,inside) = base_dft_field_view ``:ir_function`` name func
   in inside computeLib.EVAL_CONV end
end
fun base_dft_input_field i =
  base_dft_input_convert (base_dft_normalize_field i)
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
fun base_dft_result_finish g =
  (base_dft_check_function (lhs (snd g)); ALL_TAC g)

(* Worklist iteration changes only ds_boundary. Compact that current field,
   without walking older record updates or the unchanged instruction map. *)
val base_dft_flow_cs = entry_plan_readonly_cs
  [``:'a df_state``, ``:ir_function``, ``:cfg_analysis``]
fun base_dft_flow_project g =
  if entry_has_call ["wl_iterate"] (lhs (snd g)) then
    base_eval_stage (RAND_CONV
      (computeLib.WEAK_CBV_CONV base_dft_flow_cs)) "wl_iterate" g
  else ALL_TAC g
fun base_dft_flow_compact g =
  if entry_has_call ["wl_iterate"] (lhs (snd g)) then
    base_eval_stage (RAND_CONV (fn state => let
      val (_,inside) = base_dft_field_view
        (type_of state) "ds_boundary" state
    in inside (computeLib.WEAK_CBV_CONV base_dft_flow_cs THENC
      Conv.QCONV entry_compact_maps) end)) "wl_iterate" g
  else ALL_TAC g

(* Rewrite one demanded worklist call; deferred compiler data is not searched
   again while lifting the resulting equality into the fragment. *)
fun base_dft_flow_part name convert = TRY (base_eval_stage convert name)
val base_dft_flow_begin = base_dft_flow_part "wl_iterate"
  evalCompilerFlowStepLib.flow_begin
val base_dft_flow_step_open = base_dft_flow_part "wl_step"
  (RAND_CONV (LAND_CONV computeLib.EVAL_CONV) THENC FIRST_CONV
    [REWR_CONV worklistStepComputeTheory.wl_step_cons,
     REWR_CONV worklistStepComputeTheory.wl_step_nil])
val base_dft_flow_transfer = base_dft_flow_part "WHILE"
  (RAND_CONV (RAND_CONV
    (computeLib.WEAK_CBV_CONV (computeLib.the_compset()))))
val base_dft_flow_bind = base_dft_flow_part "WHILE"
  (RAND_CONV (REWR_CONV boolTheory.LET_THM THENC TRY_CONV BETA_CONV))
val base_dft_flow_changed = base_dft_flow_part "WHILE"
  (RAND_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV computeLib.EVAL_CONV))))
val base_dft_flow_select = base_dft_flow_part "WHILE"
  (RAND_CONV (FIRST_CONV (List.map REWR_CONV
    (Drule.BODY_CONJUNCTS boolTheory.COND_CLAUSES))))
val base_dft_flow_resume = base_dft_flow_part "WHILE"
  (RAND_CONV (LAND_CONV computeLib.EVAL_CONV) THENC
   REWR_CONV (GSYM worklistDefsTheory.wl_iterate_def))
end
