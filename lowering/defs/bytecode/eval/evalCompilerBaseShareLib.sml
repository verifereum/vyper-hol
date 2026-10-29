(* Share immutable IR data while a pure function pass runs.
   The live query is kept closed; the local definition is discharged before
   the pass's unit/supply guards. No compiler equation or fuel is changed. *)
structure evalCompilerBaseShareLib = struct
open HolKernel Parse boolLib bossLib
open evalCompilerBaseLib

val base_shared_names = ref ([] : string list)
val base_sharing_active = ref false
val base_sharing_done = ref false
val base_share_types =
  [``:compilation_unit``, ``:venom_context``, ``:ir_function``,
   ``:ir_supply``, ``:fn_pass_output``]
fun base_unit_nodes tm =
  if is_comb tm then 1 + base_unit_nodes (rator tm) + base_unit_nodes (rand tm)
  else if is_abs tm then 1 + base_unit_nodes (snd (dest_abs tm)) else 1
fun base_share_candidates active tm entries = let
  (* Record values can be update expressions rather than constructor terms.
     Never hide the live query itself inside the abbreviation. *)
  val selected = is_comb tm andalso
    List.exists (fn ty => type_of tm = ty) base_share_types andalso
    List.null (free_vars tm) andalso not (can (find_term (aconv active)) tm)
  fun add [] = [(tm,1,base_unit_nodes tm)]
    | add ((value,count,size)::rest) =
        if aconv tm value then (value,count+1,size)::rest
        else (value,count,size)::add rest
  val next = if selected then add entries else entries
in if selected then next
   else if is_comb tm then base_share_candidates active (rand tm)
     (base_share_candidates active (rator tm) next)
   else if is_abs tm then base_share_candidates active (snd (dest_abs tm)) next
   else next
end
fun base_share_more name g = if !base_sharing_done then ALL_TAC g else let
  val () = if !base_sharing_active then ()
    else raise Fail "pass-context sharing scope is not active"
  fun better (candidate as (_,count,size), best as (_,best_count,best_size)) =
    if (count-1)*size > (best_count-1)*best_size orelse
       ((count-1)*size = (best_count-1)*best_size andalso size > best_size)
    then candidate else best
  fun named tm = let val (h,args) = strip_comb tm in
    is_const h andalso #Name (dest_thy_const h) = name andalso
    List.length args = entry_function_arity (type_of h) end
  val active = find_term (flow_call name) (lhs (snd g))
  val candidates = base_share_candidates active (lhs (snd g)) []
  val best = case candidates of
      [] => NONE
    | first::rest => SOME (List.foldl better first rest)
in case best of
    NONE => (base_sharing_done := true; ALL_TAC g)
  | SOME (value,count,_) => if count <= 1 then
      (base_sharing_done := true; ALL_TAC g)
    else let
  val context_name = "base_pass_context_" ^ Int.toString (List.length (!base_shared_names))
  val variable = mk_var (context_name,type_of value)
  val initial_nodes = base_unit_nodes (snd g)
  val () = if List.exists (aconv variable) (free_varsl (snd g :: fst g)) then
      raise Fail "pass-context abbreviation already exists" else ()
  fun finish next = let
    fun matching a =
      #Name (dest_thy_const (rator a)) = "Abbrev" andalso
      aconv (lhs (rand a)) variable
      handle HOL_ERR _ => false
    val assumption = valOf (List.find matching (fst next))
    val equation = REWRITE_RULE [markerTheory.Abbrev_def] (ASSUME assumption)
    (* A projection in the input can mention the saved value. Expand that
       occurrence only, leaving the deferred compiler continuation shared. *)
    val restore_query = CONV_TAC (LAND_CONV (base_first_conv named
      (Conv.QCONV (ONCE_DEPTH_CONV (fn tm =>
        if aconv tm variable then equation else NO_CONV tm)))))
    fun report result = let
      val () = if can (find_term (aconv active)) (lhs (snd result)) then ()
        else raise Fail "sharing did not restore the original closed query"
      val remaining = base_unit_nodes (snd result)
      val () = base_shared_names := !base_shared_names @ [context_name]
      val () = if remaining < initial_nodes then () else base_sharing_done := true
    in
      (print ("shared " ^ type_to_string (type_of value) ^ " for " ^ name ^
         " goal_nodes=" ^ Int.toString initial_nodes ^
         " -> " ^ Int.toString remaining ^ "\n");
       ALL_TAC result)
    end
  in (restore_query >> report) next end
in (markerLib.ABBREV_TAC (mk_eq(variable,value)) >> finish) g end
end
fun base_share_for name g =
  if !base_sharing_active then raise Fail "previous shared context was not discharged"
  else (base_sharing_active := true; base_sharing_done := false;
        base_share_more name g)
fun base_unshare_one g = case !base_shared_names of
    [] => ALL_TAC g
  | name::rest =>
      (markerLib.UNABBREV_TAC name >>
       (fn next => (base_shared_names := rest; ALL_TAC next))) g
fun base_sharing_finish g =
  if not (List.null (!base_shared_names)) then raise Fail "shared pass data remain"
  else if List.exists (fn v => String.isPrefix "base_pass_context_" (fst (dest_var v)))
    (free_varsl (snd g :: fst g)) then raise Fail "shared pass variable remains"
  else (base_sharing_active := false; base_sharing_done := false; ALL_TAC g)
end
