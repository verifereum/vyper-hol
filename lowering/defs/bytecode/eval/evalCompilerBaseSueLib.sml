(* Checked SUE replay with one shared, explicitly discharged DFG abbreviation. *)
structure evalCompilerBaseSueLib = struct
open HolKernel Parse boolLib bossLib
open evalCompilerBaseLib

val base_sue_dispatch = base_eval_stage
  (REWR_CONV venomPassDispatcherTheory.execute_configured_fn_pass_sue)
  "execute_configured_fn_pass"
val base_sue_input = base_eval_stage (RAND_CONV
  (computeLib.WEAK_CBV_CONV base_dom_cs THENC computeLib.EVAL_CONV))
  "sue_expand_function_supply"
val base_sue_supply_input = base_eval_stage (RATOR_CONV (RAND_CONV
  (computeLib.WEAK_CBV_CONV base_dom_cs THENC computeLib.EVAL_CONV)))
  "sue_expand_function_supply"
val base_sue_open = base_eval_stage
  (REWR_CONV singleUseExpansionDefsTheory.sue_expand_function_supply_def)
  "sue_expand_function_supply"

fun base_sue_abbrev g = let
  val target = find_term (flow_call "sue_expand_blocks_supply") (lhs (snd g))
  val value = hd (snd (strip_comb target))
  val variable = mk_var ("sue_dfg",type_of value)
  val () = if List.exists (aconv variable) (free_varsl (snd g :: fst g)) then
      raise Fail "SUE DFG abbreviation already exists" else ()
  fun remember next = let
    fun matching a =
      #Name (dest_thy_const (rator a)) = "Abbrev" andalso
      aconv (lhs (rand a)) variable
      handle HOL_ERR _ => false
    val assumption = valOf (List.find matching (fst next))
    val th = REWRITE_RULE [markerTheory.Abbrev_def] (ASSUME assumption)
    val () = entry_plan_abbrev_defs := th :: !entry_plan_abbrev_defs
  in ALL_TAC next end
in (markerLib.ABBREV_TAC (mk_eq(variable,value)) >> remember) g end

fun base_sue_tick g =
  if entry_plan_has_call ["sue_expand_blocks_supply", "sue_expand_insts_supply"]
       (lhs (snd g)) then
    CONV_TAC (LAND_CONV (CHANGED_CONV (entry_plan_active
      ["sue_expand_blocks_supply", "sue_expand_insts_supply"]
      entry_sue_block_step))) g
  else ALL_TAC g

(* Read only the queried DFG field, then normalize the small emitted result. *)
val base_sue_cs = entry_plan_readonly_cs [``:dfg_analysis``]
val base_sue_instruction = CONV_TAC (LAND_CONV (TRY_CONV
  (entry_plan_active ["sue_expand_inst_supply"]
    (entry_plan_compute (fn tm => let
      val th = computeLib.WEAK_CBV_CONV base_sue_cs tm
    in TRANS th (Conv.QCONV computeLib.EVAL_CONV (rhs (concl th))) end)))))

fun base_sue_finish g =
  if entry_plan_has_call ["sue_expand_blocks_supply", "sue_expand_insts_supply"]
       (lhs (snd g)) then
    raise Fail "single-use expansion has pending traversal calls"
  else ALL_TAC g
end
