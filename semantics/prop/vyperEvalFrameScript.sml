(* Evaluator frame theorem.  A transitive relation R on evaluation states
 * that holds across every machine-invisible step (machine_frame) and across
 * each state-changing primitive the evaluator calls relates the start and end
 * states of every evaluator function. *)
Theory vyperEvalFrame
Ancestors
  pair vyperAST vyperMachineFrame vyperCallOutcomeFrame
  vyperCreateFrame vyperStatePreservation vyperInterpreter vyperState
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";

Theorem state_rel_frame_machine:
  (!s t. machine_frame s t ==> R s t) /\ state_rel_frame machine_frame f ==>
  state_rel_frame R f
Proof
  simp[state_rel_frame_def]
QED

val R_tm = mk_var ("R", type_of ``machine_frame``);

(* Each leaf is indexed under its conclusion with machine_frame generalised to
   R, and applied through state_rel_frame_machine. *)
val eval_frame_net =
  let
    val rules = [state_rel_frame_bind_guarded, state_rel_frame_try,
      state_rel_frame_finally, state_rel_frame_finally_unless_halt]
    val leaves = [machine_frame_primitives, machine_frame_read_result,
      machine_frame_read_results, machine_frame_reads, machine_frame_select_result,
      machine_frame_extend_place, machine_frame_get_place, machine_frame_read_place,
      machine_frame_place_type_value, machine_frame_new_variable,
      machine_frame_next_gas_reading, machine_frame_precompile_call_success,
      machine_frame_handlers, machine_frame_push_function,
      machine_frame_pop_function, machine_frame_unchanged_reads,
      machine_frame_array_iterator_results]
    val structural = List.foldl (fn (th,net) => Net.insert
      (snd (dest_imp (concl th)), MATCH_MP_TAC th >> rpt conj_tac) net)
      Net.empty (map SPEC_ALL rules)
    fun leaf (th,net) =
      Net.insert (subst [``machine_frame`` |-> R_tm] (concl th),
        MATCH_MP_TAC state_rel_frame_machine >> conj_tac >-
          first_assum ACCEPT_TAC >> MATCH_ACCEPT_TAC th) net
  in List.foldl leaf structural
      (List.concat (map (CONJUNCTS o SPEC_ALL) leaves)) end;

(* Rewrite only the exposed head: case and let redexes, beta, UNCURRY. *)
val eval_frame_head_conv =
  let
    val case_rules = List.concat (List.map
      (map SPEC_ALL o CONJUNCTS o SPEC_ALL)
      (LET_THM :: COND_CLAUSES ::
       List.mapPartial (total TypeBasePure.case_def_of) (TypeBase.elts ())))
    val cases = List.foldl (fn (th,net) =>
      Net.insert (lhs (concl th), REWR_CONV th) net) Net.empty case_rules
    fun root tm = FIRST_CONV (Net.match tm cases) tm
    fun head tm = (BETA_CONV ORELSEC root ORELSEC
      REWR_CONV UNCURRY ORELSEC RATOR_CONV head) tm
  in head end;

fun EVAL_FRAME_CASE_TAC (g as (old,_)) =
  let fun simplify (asl,w) =
    let val fresh = List.filter (fn a => not (is_forall a) andalso
      not (List.exists (aconv a) old)) asl
    in simp_tac bool_ss (map ASSUME fresh) (asl,w) end
  in (BasicProvers.PURE_TOP_CASE_TAC >> simplify) g end;

(* Close the goal with an induction hypothesis, discharging its guards from
   the bind results in the assumptions. *)
fun EVAL_FRAME_IH_TAC (asl,w) =
  let
    fun terminal tm =
      if is_forall tm then terminal (snd (dest_forall tm))
      else if is_imp tm then terminal (snd (dest_imp tm)) else tm
    val candidates = List.mapPartial
      (total (fn a => PART_MATCH terminal (ASSUME a) w)) asl
    val normalise = SIMP_RULE bool_ss
      [oneTheory.one, ignore_bind_def, FST, SND, pair_case_thm, UNCURRY,
       lock_if_nr_def, unlock_if_nr_def]
    val facts = List.concat (map (CONJUNCTS o normalise o ASSUME)
      (List.filter (not o is_forall) asl))
    fun discharge raw =
      let val th = normalise raw in
        if is_imp (snd (strip_forall (concl th))) then
          discharge (tryfind (MATCH_MP th) facts handle HOL_ERR _ =>
            let val guard = fst (dest_imp (snd (strip_forall (concl th)))) in
              MATCH_MP th (REFL (lhs guard)) handle HOL_ERR _ =>
                MATCH_MP th (REFL (rhs guard)) end)
        else th
      end
    fun close candidate = ACCEPT_TAC (discharge
      (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] (normalise candidate)))
  in FIRST (map close candidates) (asl,w) end;

val EVAL_FRAME_STEP = FIRST [
  first_assum MATCH_ACCEPT_TAC,
  (fn g as (_,w) => FIRST (Net.match w eval_frame_net) g),
  CONV_TAC (RAND_CONV (REWR_CONV switch_BoolV_def)),
  CONV_TAC (HO_REWR_CONV FORALL_PROD),
  CONV_TAC (RAND_CONV (CHANGED_CONV eval_frame_head_conv)),
  gen_tac, strip_tac, conj_tac,
  CONV_TAC (RAND_CONV (REWR_CONV ignore_bind_def)),
  CONV_TAC (RAND_CONV ETA_CONV),
  CHANGED_TAC (fn (asl,w) => simp_tac bool_ss
    (pair_case_thm :: UNCURRY :: List.map ASSUME (List.filter is_eq asl)) (asl,w)),
  EVAL_FRAME_CASE_TAC, EVAL_FRAME_IH_TAC,
  (* Hypotheses guarded by a CreateTarget kind, and IntCall's tuple
     projections, need normalising before they apply. *)
  RULE_ASSUM_TAC (REWRITE_RULE [create_kind_11, create_kind_distinct,
    GSYM create_kind_distinct, COND_CLAUSES]) >>
  simp_tac bool_ss [FST, SND] >>
  FIRST [first_assum ACCEPT_TAC, EVAL_FRAME_IH_TAC]];

(* Unfold one evaluator equation and walk its body. *)
val EVAL_FRAME_CASE =
  rpt strip_tac >>
  simp_tac bool_ss [Once evaluate_def, lock_if_nr_def, unlock_if_nr_def] >>
  rpt EVAL_FRAME_STEP;

Theorem eval_state_rel_frame:
  (!s t u. R s t /\ R t u ==> R s u) /\
  (!s t. machine_frame s t ==> R s t) /\
  (!cx p v. state_rel_frame R (write_place cx p v)) /\
  (!cx p v. state_rel_frame R (append_place cx p v)) /\
  (!cx p. state_rel_frame R (pop_place cx p)) /\
  (!ev. state_rel_frame R (push_log ev)) /\
  (!a b n. state_rel_frame R (transfer_value a b n)) /\
  (!cx g vs. state_rel_frame R (eval_send cx g vs)) /\
  (!cx st sk sig opts vs. state_rel_frame R (eval_ext_call cx st sk sig opts vs)) /\
  (!cx fl a d m g. state_rel_frame R (eval_raw_call cx fl a d m g)) /\
  (!cx k h r ts vs cs. state_rel_frame R (eval_create cx k h r ts vs cs)) /\
  (!a n v. state_rel_frame R (acquire_nonreentrant_lock a n v)) /\
  (!a n. state_rel_frame R (release_nonreentrant_lock a n)) /\
  (!f. state_rel_frame R (update_accounts f)) /\
  (!f. state_rel_frame R (update_pending_deletions f)) ==>
  (!cx s. state_rel_frame R (eval_stmt cx s)) /\
  (!cx ss. state_rel_frame R (eval_stmts cx ss)) /\
  (!cx it. state_rel_frame R (eval_iterator cx it)) /\
  (!cx tyv nm body vs. state_rel_frame R (eval_for cx tyv nm body vs)) /\
  (!cx e. state_rel_frame R (eval_expr cx e)) /\
  (!cx es. state_rel_frame R (eval_exprs cx es)) /\
  (!cx t. state_rel_frame R (eval_base_place cx t)) /\
  (!cx t. state_rel_frame R (eval_target_place cx t)) /\
  (!cx g v. state_rel_frame R (assign_tuple_targets cx g v)) /\
  (!cx gs vs. state_rel_frame R (assign_tuple_target_list cx gs vs)) /\
  (!cx es. state_rel_frame R (eval_expr_results cx es))
Proof
  strip_tac >> ho_match_mp_tac evaluate_ind >> rpt conj_tac
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  (* Builtin In/NotIn: the membership branch's eval_exprs needs the
     disjunct-guarded induction hypothesis; EVAL_FRAME_IH_TAC leaves it open. *)
  >- (EVAL_FRAME_CASE >> metis_tac[])
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >> EVAL_FRAME_CASE
QED
