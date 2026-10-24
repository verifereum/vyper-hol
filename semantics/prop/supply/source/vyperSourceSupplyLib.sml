(* Forward source-supply facts across actual evaluation equations, using the
   independently proved invariant for intermediate states in typing proofs. *)
structure vyperSourceSupplyLib =
struct

open HolKernel Parse boolLib bossLib;

val properties = List.concat (map (CONJUNCTS o SPEC_ALL)
  [vyperEvalSupplyTheory.eval_source_supply_mutual,
   vyperSourcePrimitiveSupplyTheory.source_supply_reads,
   vyperSourcePrimitiveSupplyTheory.source_supply_field_updates,
   vyperSourcePrimitiveSupplyTheory.source_supply_locals,
   vyperSourcePrimitiveSupplyTheory.source_supply_locks,
   vyperSourcePrimitiveSupplyTheory.source_supply_action_write_storage,
   vyperSourcePrimitiveSupplyTheory.source_supply_action_set_storage_backend,
   vyperSourcePrimitiveSupplyTheory.source_supply_action_set_global,
   vyperSourceCompoundSupplyTheory.source_supply_assignment,
   vyperSourceCompoundSupplyTheory.source_supply_handlers,
   vyperSourceCompoundSupplyTheory.source_supply_check_create_blueprint,
   vyperSourceCallSupplyTheory.source_supply_action_raw_call,
   vyperSourceCallSupplyTheory.source_supply_action_send,
   vyperSourceCreateSupplyTheory.source_supply_action_create,
   vyperSourceTransferSupplyTheory.source_supply_action_transfer,
    vyperSourceTransferSupplyTheory.source_supply_action_send_call_value,
   vyperSourceOracleSupplyTheory.source_supply_action_take,
   vyperSourceSupplyDefsTheory.source_supply_action_return,
   vyperSourceSupplyDefsTheory.source_supply_action_raise,
   vyperSourceSupplyDefsTheory.source_supply_action_read]);

val net = vyperSupplyProofLib.fact_net properties
  [vyperSourceSupplyDefsTheory.source_supply_action_bind_simple,
   vyperSourceSupplyDefsTheory.source_supply_action_ignore_bind,
   vyperSourceSupplyDefsTheory.source_supply_action_try,
   vyperSourceSupplyDefsTheory.source_supply_action_finally,
   vyperSourceSupplyDefsTheory.source_supply_action_finally_unless_halt,
   vyperSourceSupplyDefsTheory.source_supply_action_cond];

val supply = ``vyperSourceSupplyDefs$source_supply``;
val action_supply = ``vyperSourceSupplyDefs$source_supply_action``;

fun property action =
  TAC_PROOF (([], mk_icomb (action_supply, action)),
    NTAC 40 (vyperSupplyProofLib.step net) >> NO_TAC);

(* These proofs have no hypotheses, so cache them across tactic invocations. *)
val attempted = ref [];

fun equation th =
  let val (call,outcome) = dest_eq (concl th)
      val (action,pre_state) = dest_comb call
      val (_,post_state) = pairSyntax.dest_pair outcome
  in if type_of pre_state = ``:vyperState$evaluation_state`` andalso
        type_of post_state = type_of pre_state
     then SOME (th,action,pre_state,post_state) else NONE end
  handle HOL_ERR _ => NONE;

fun forward (goal as (asl,_)) =
  let
    val atoms = List.concat (map (CONJUNCTS o ASSUME)
      (List.filter (not o is_forall) asl));
    val equations = List.mapPartial equation atoms;
    val explicit = List.filter (fn th =>
      total (same_const supply o rator) (concl th) = SOME true) atoms;
    val domains = List.filter (fn th =>
      total (same_const ``vyperSourceSupplyFields$machine_supply`` o
        fst o strip_comb) (concl th) = SOME true) atoms;
    val domain_facts = List.concat (map (CONJUNCTS o REWRITE_RULE
      [vyperSourceSupplyFieldsTheory.machine_supply_def]) domains);
    (* Seed actual entry equations from the public machine domain. These
       proofs are context-dependent and must never enter the action cache. *)
    fun entry (_,_,state,_) =
      if null domains then NONE else
      let
        val th = TAC_PROOF ((map concl domain_facts, mk_comb (supply,state)),
          asm_simp_tac (srw_ss())
            [vyperSourceSupplyDefsTheory.source_supply_def,
             vyperInterpreterTheory.initial_state_def] >> NO_TAC);
        val th = List.foldl (fn (fact,th) => PROVE_HYP fact th) th domain_facts;
      in if List.all (fn h => List.exists (aconv h) asl) (hyp th)
         then SOME th else NONE end
      handle HOL_ERR _ => NONE;
    val initial = explicit @ List.mapPartial entry equations;
  in if null initial then ALL_TAC goal else
  let
    fun state_alias th =
      let val eq = REWRITE_RULE [markerTheory.Abbrev_def] th
            handle UNCHANGED => th
          val (state,_) = dest_eq (concl eq)
      in if type_of state = ``:vyperState$evaluation_state``
         then SOME eq else NONE end
      handle HOL_ERR _ => NONE;
    val aliases = List.mapPartial state_alias atoms;
    fun action_property action =
      case List.find (fn (term,_) => aconv term action) (!attempted) of
        SOME (_,SOME th) => th
      | SOME (_,NONE) => raise ERR "forward" "action is not uniformly preserving"
      | NONE =>
          let val result = SOME (property action) handle HOL_ERR _ => NONE
              val () = attempted := (action,result) :: !attempted
          in case result of SOME th => th
             | NONE => raise ERR "forward" "action is not uniformly preserving" end;
    fun exact state facts = tryfind (fn th =>
      if aconv (concl th) (mk_comb (supply,state)) then th
      else raise ERR "forward" "state not known") facts;
    fun known state facts = exact state facts handle HOL_ERR _ =>
      let
        val context = aliases @ facts;
        val th = TAC_PROOF ((map concl context, mk_comb (supply,state)),
          asm_simp_tac bool_ss
            [vyperSourceSupplyFieldsTheory.source_supply_fields] >> NO_TAC);
        val th = List.foldl (fn (fact,th) => PROVE_HYP fact th) th context;
      in if List.all (fn h => List.exists (aconv h) asl) (hyp th)
         then th else raise ERR "forward" "frame proof has extra hypotheses" end;
    fun include_state state facts =
      if can (exact state) facts then facts
      else (known state facts :: facts handle HOL_ERR _ => facts);
    fun advance ((eq,action,pre_state,post_state),facts) =
      let val facts = include_state pre_state facts
          val facts = include_state post_state facts
      in if can (exact post_state) facts then facts else
          (let val pre = exact pre_state facts
               val preserves = action_property action
               val post = MATCH_MP
                 vyperSourceSupplyDefsTheory.source_supply_action_result
                 (LIST_CONJ [preserves,pre,eq])
           in post :: facts end
           handle HOL_ERR _ => facts)
      end;
    fun close facts =
      let val next = List.foldl advance facts equations
      in if length next = length facts then facts else close next end;
    val derived = close initial;
    val bounds = map (CONJUNCT1 o REWRITE_RULE
      [vyperSourceSupplyDefsTheory.source_supply_def]) derived;
    val fresh = List.filter (fn th =>
      not (List.exists (aconv (concl th)) asl)) (bounds @ derived);
    val () = if List.all (fn th =>
      List.all (fn h => List.exists (aconv h) asl) (hyp th)) fresh
      then () else raise ERR "forward" "derived fact has extra hypotheses";
  in MAP_EVERY ASSUME_TAC fresh goal end end;

end
