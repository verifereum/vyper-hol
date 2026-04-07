(*
 * Assert Combiner Pass — Simulation Precondition Proofs (Part 2)
 *
 * Contains ac_sim_precond definition, extractors, and ac_sim_step_ok
 * (the OK-case per-step simulation via Suspend/Resume).
 *)

Theory acSimPrecondProofs
Ancestors
  acChainProofs acBaseProofs assertCombinerDefs passSimulationDefs passSimulationProps
  stateEquiv stateEquivProps execEquivParamProps venomInstProps venomExecProps
  dfgAnalysisProps venomState venomWf venomExecSemantics venomExecProofs
  analysisSimDefs analysisSimProofsBase
Libs
  pred_setTheory arithmeticTheory listTheory rich_listTheory

(* Quotation-free tactic helpers *)
fun find_free_var name (asl, w) =
  let val vs = free_varsl (w::asl)
  in valOf (List.find (fn v => fst (dest_var v) = name) vs) end;

fun exists_var_tac name (g as (asl, w)) =
  Tactic.EXISTS_TAC (find_free_var name g) g;

fun exists_vars_tac names = Tactical.EVERY (map exists_var_tac names);

fun with_var name (f : term -> tactic) (g as (asl, w)) : goal list * validation =
  f (find_free_var name g) g;

fun specl_vars_then names ttac thm (g as (asl, w)) =
  let val tms = map (fn n => find_free_var n g) names
  in ttac (SPECL tms thm) g end;

fun exists_term_tac f names (g as (asl, w)) =
  let val tms = map (fn n => find_free_var n g) names
  in Tactic.EXISTS_TAC (f tms) g end;


(* ===== Bundled precondition for run_insts simulation ===== *)

(* Shared preconditions across ac_run_insts_sim.
   Parameterized by insts (the remaining instruction suffix), cands (merge
   candidates from scan), mp (merged predicates so far), dfg, s (current
   state), V (fresh variable set). *)
Definition ac_sim_precond_def:
  ac_sim_precond cands mp dfg insts s V <=>
    ac_dfg_inv dfg s /\
    EVERY inst_wf insts /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) insts /\
    EVERY (\i. ac_is_safe_between i \/ i.inst_opcode = ASSERT) insts /\
    (!i op. MEM i insts /\ MEM op i.inst_operands ==>
       IS_SOME (eval_operand op s)) /\
    (!i x. MEM i insts /\ MEM (Var x) i.inst_operands ==> x NOTIN V) /\
    (!i x. MEM i insts /\ MEM x i.inst_outputs ==> x NOTIN V) /\
    (!mc. MEM mc cands ==>
       ac_or_var mc.mc_second_id IN V /\ ac_iz_var mc.mc_second_id IN V) /\
    ALL_DISTINCT (MAP (\mc. mc.mc_second_id) cands) /\
    (!mc. MEM mc cands ==>
       IS_SOME (eval_operand mc.mc_second_pred s) /\
       IS_SOME (eval_operand mc.mc_first_pred s)) /\
    (!i mc x. MEM i insts /\ MEM (Var x) i.inst_operands /\ MEM mc cands ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (!i mc x. MEM i insts /\ MEM x i.inst_outputs /\ MEM mc cands ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (!mc mc' x. MEM mc cands /\ MEM mc' cands /\
       (mc.mc_second_pred = Var x \/ mc.mc_first_pred = Var x) ==>
       x <> ac_or_var mc'.mc_second_id /\ x <> ac_iz_var mc'.mc_second_id) /\
    (!i mc. MEM i insts /\
       FIND (\mc'. mc'.mc_second_id = i.inst_id) cands = SOME mc ==>
       i.inst_opcode = ASSERT) /\
    (!i. MEM i insts /\ EXISTS (\mc. mc.mc_first_id = i.inst_id) cands ==>
       i.inst_opcode = ASSERT) /\
    (!mc1 mc2. MEM mc1 cands /\ MEM mc2 cands /\
       mc1.mc_second_id = mc2.mc_first_id ==>
       mc1.mc_second_pred = mc2.mc_first_pred) /\
    ac_cands_ordered cands insts /\
    (!i x mc. MEM i insts /\ MEM x i.inst_outputs /\ MEM mc cands /\
       (mc.mc_second_pred = Var x \/ mc.mc_first_pred = Var x) ==> F) /\
    (!i x id. MEM i insts /\ MEM x i.inst_outputs /\
       ALOOKUP mp id = SOME (Var x) ==> F) /\
    (!id x mc. ALOOKUP mp id = SOME (Var x) /\ MEM mc cands /\
       (?i. MEM i insts /\ i.inst_id = mc.mc_second_id) ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (!id p. ALOOKUP mp id = SOME p ==> IS_SOME (eval_operand p s)) /\
    (!i. MEM i insts ==> ALOOKUP mp i.inst_id = NONE) /\
    (!id pred. ALOOKUP mp id = SOME pred ==> eval_operand pred s = SOME 0w) /\
    (* Processed first_ids: if mc.mc_first_id has been consumed (not in insts)
       and no mp entry overrides it, then mc.mc_first_pred evaluates to 0w. *)
    (!mc. MEM mc cands /\
       (!i. MEM i insts ==> i.inst_id <> mc.mc_first_id) /\
       ALOOKUP mp mc.mc_first_id = NONE ==>
       eval_operand mc.mc_first_pred s = SOME 0w) /\
    (* DFG consistency for ac_dfg_inv preservation *)
    (!i v. MEM i insts /\ MEM v i.inst_outputs /\ dfg_get_def dfg v <> NONE ==>
       dfg_get_def dfg v = SOME i) /\
    (* Self: each instruction's operand vars not among its own outputs *)
    (!i op x. MEM i insts /\ MEM op i.inst_operands /\ op = Var x ==>
       ~MEM x i.inst_outputs) /\
    (* DFG does not reference fresh variables *)
    (!v. v IN V ==> dfg_get_def dfg v = NONE) /\
    (!di x v. dfg_get_def dfg x = SOME di /\
       MEM (Var v) di.inst_operands ==> v NOTIN V) /\
    (* DFG-ISZERO chain connection: merge targets trace to their predicates *)
    (!i mc. MEM i insts /\ MEM mc cands /\ mc.mc_second_id = i.inst_id ==>
       ?v. i.inst_operands = [Var v] /\
           ac_get_iszero_operand dfg {} (Var v) = SOME mc.mc_second_pred) /\
    (!i mc. MEM i insts /\ MEM mc cands /\ mc.mc_first_id = i.inst_id ==>
       ?v. i.inst_operands = [Var v] /\
           ac_get_iszero_operand dfg {} (Var v) = SOME mc.mc_first_pred)
End

(* Operand evaluability preserved through safe_between/ASSERT OK step *)
Theorem safe_assert_step_preserves_eval:
  !fuel ctx h s s' op.
    step_inst fuel ctx h s = OK s' /\
    (ac_is_safe_between h \/ h.inst_opcode = ASSERT) /\
    inst_wf h /\
    (!op'. MEM op' h.inst_operands ==> IS_SOME (eval_operand op' s)) /\
    IS_SOME (eval_operand op s) ==>
    IS_SOME (eval_operand op s')
Proof
  rpt gen_tac >> strip_tac >> (
    TRY (`s' = s` by metis_tac[step_assert_identity] >> gvs[]) >>
    Cases_on `op` >> gvs[eval_operand_def] >>
    TRY (irule safe_between_step_is_some_mono >>
         MAP_EVERY qexists_tac [`ctx`, `fuel`, `h`, `s`] >> simp[] >> NO_TAC) >>
    `s'.vs_labels = s.vs_labels` by
      metis_tac[step_preserves_labels, ac_is_safe_between_def] >>
    gvs[]
  )
QED

(* step_inst on safe_between/ASSERT can only OK or Revert_abort *)
Theorem step_safe_or_assert_ok_or_revert:
  !fuel ctx inst s.
    (ac_is_safe_between inst \/ inst.inst_opcode = ASSERT) /\
    inst_wf inst /\
    (!op. MEM op inst.inst_operands ==> IS_SOME (eval_operand op s)) ==>
    (?s'. step_inst fuel ctx inst s = OK s') \/
    (?sa. step_inst fuel ctx inst s = Abort Revert_abort sa)
Proof
  rpt gen_tac >> strip_tac
  >- (disj1_tac >> metis_tac[safe_between_wf_step_ok])
  >- (
    gvs[inst_wf_def] >>
    `?cond_op. inst.inst_operands = [cond_op]` by
      (Cases_on `inst.inst_operands` >> gvs[] >>
       Cases_on `t` >> gvs[]) >>
    gvs[] >>
    `?v. eval_operand cond_op s = SOME v` by
      (Cases_on `eval_operand cond_op s` >> gvs[]) >>
    Cases_on `v = 0w`
    >- (disj2_tac >> metis_tac[step_assert_abort])
    >- (disj1_tac >> metis_tac[step_assert_ok])
  )
QED

(* run_insts on safe_between/ASSERT only returns OK or Abort Revert_abort *)
Theorem run_insts_safe_assert_only_ok_or_revert:
  !insts fuel ctx s a sa.
    run_insts fuel ctx insts s = Abort a sa /\
    EVERY (\i. ac_is_safe_between i \/ i.inst_opcode = ASSERT) insts /\
    EVERY inst_wf insts /\
    (!i op. MEM i insts /\ MEM op i.inst_operands ==>
       IS_SOME (eval_operand op s)) ==>
    a = Revert_abort
Proof
  Induct >> simp[run_insts_def] >>
  rpt gen_tac >> simp[EVERY_DEF] >> strip_tac >>
  `(?s'. step_inst fuel ctx h s = OK s') \/
   (?sa'. step_inst fuel ctx h s = Abort Revert_abort sa')` by
    (irule step_safe_or_assert_ok_or_revert >> metis_tac[]) >>
  gvs[] >> (
    (* Both safe_between and ASSERT cases: apply IH *)
    first_x_assum
      (qspecl_then [`fuel`, `ctx`, `s'`, `a`, `sa`] mp_tac) >>
    simp[] >> disch_then irule >>
    rpt strip_tac >>
    irule safe_assert_step_preserves_eval >>
    MAP_EVERY qexists_tac [`ctx`, `fuel`, `h`, `s`] >> simp[] >>
    metis_tac[]
  )
QED

(* Core: run_insts on original non-terminators vs FOLDL-transformed.
   Two-state formulation: original runs from s_o, transform runs from s_t,
   with state_equiv V s_o s_t. This allows the transform state to track
   fresh variables (or_v, iz_v) created by the merge while the original
   state doesn't have them.

   OK case: per-instruction induction. Every original step succeeds,
   show each contrib succeeds, transfer preconditions, apply IH. *)

(* ===== Reusable tactic for ac_sim_precond conjuncts =====
   After expanding ac_sim_precond_def, the goal is a big conjunction.
   State-independent conjuncts are solved by metis_tac[ac_cands_ordered_tail].
   State-dependent conjuncts need eval_operand preservation.
   ALOOKUP conjuncts need case split on the new mp entry. *)
val eval_uv_pres_tac =
  irule eval_operand_update_var_neq >> rpt strip_tac >> gvs[] >>
  CCONTR_TAC >> gvs[] >>
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  metis_tac[];

val precond_eval_tac =
  TRY (
    `IS_SOME (eval_operand op s)` by res_tac >>
    `eval_operand op (update_var v val s) = eval_operand op s` by
      eval_uv_pres_tac >>
    gvs[] >> NO_TAC) >>
  TRY (
    `IS_SOME (eval_operand mc.mc_second_pred s)` by res_tac >>
    `eval_operand mc.mc_second_pred (update_var v val s) =
     eval_operand mc.mc_second_pred s` by eval_uv_pres_tac >>
    gvs[] >> NO_TAC) >>
  TRY (
    `IS_SOME (eval_operand mc.mc_first_pred s)` by res_tac >>
    `eval_operand mc.mc_first_pred (update_var v val s) =
     eval_operand mc.mc_first_pred s` by eval_uv_pres_tac >>
    gvs[] >> NO_TAC) >>
  TRY (
    `IS_SOME (eval_operand p s)` by res_tac >>
    `eval_operand p (update_var v val s) = eval_operand p s` by (
      irule eval_operand_update_var_neq >> rpt strip_tac >> gvs[] >>
      CCONTR_TAC >> gvs[] >> metis_tac[]) >>
    gvs[] >> NO_TAC) >>
  TRY (
    `eval_operand pred s = SOME 0w` by res_tac >>
    `eval_operand pred (update_var v val s) = eval_operand pred s` by (
      irule eval_operand_update_var_neq >> rpt strip_tac >> gvs[] >>
      CCONTR_TAC >> gvs[] >> metis_tac[]) >>
    gvs[] >> NO_TAC);

val precond_alookup_ext_tac =
  rpt strip_tac >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  TRY (first_x_assum (drule_then irule) >> metis_tac[] >> NO_TAC) >>
  metis_tac[];

(* Head-drop: ac_sim_precond cands mp dfg (h::insts) s V
              ==> ac_sim_precond cands mp dfg insts s V
   Extra hypothesis: when h was a first_id whose predicate wasn't in mp,
   the caller must establish that predicate evaluates to 0w. *)
Triviality ac_sim_precond_transfer_same[local]:
  !h insts cands mp dfg s_t V.
    ac_sim_precond cands mp dfg (h::insts) s_t V ==>
    (!mc. MEM mc cands /\ mc.mc_first_id = h.inst_id /\
       ALOOKUP mp mc.mc_first_id = NONE ==>
       eval_operand mc.mc_first_pred s_t = SOME 0w) ==>
    ac_sim_precond cands mp dfg insts s_t V
Proof
  rpt strip_tac >>
  qpat_x_assum `ac_sim_precond _ _ _ (h::_) _ _` mp_tac >>
  simp[ac_sim_precond_def, EVERY_DEF] >> strip_tac >>
  rpt conj_tac >> metis_tac[ac_cands_ordered_tail]
QED

(* State update on fresh variable.
   Side conditions: v must not be a variable in any cand pred or mp pred. *)
Triviality ac_sim_precond_update_fresh_var[local]:
  !cands mp dfg insts s v val V.
    ac_sim_precond cands mp dfg insts s V /\
    v IN V /\
    (!mc x. MEM mc cands /\
       (mc.mc_second_pred = Var x \/ mc.mc_first_pred = Var x) ==> x <> v) /\
    (!id x. ALOOKUP mp id = SOME (Var x) ==> x <> v) ==>
    ac_sim_precond cands mp dfg insts (update_var v val s) V
Proof
  rpt strip_tac >>
  qpat_x_assum `ac_sim_precond _ _ _ _ _ _` mp_tac >>
  simp[ac_sim_precond_def] >> strip_tac >>
  rpt conj_tac
  >- (irule ac_dfg_inv_update_fresh >> simp[] >> metis_tac[])
  >> TRY (metis_tac[]) >>
  rpt strip_tac >> precond_eval_tac
QED

(* mp extension without head drop *)
Triviality ac_sim_precond_extend_mp[local]:
  !cands mp id pred dfg insts s V.
    ac_sim_precond cands mp dfg insts s V /\
    (!i. MEM i insts ==> i.inst_id <> id) /\
    eval_operand pred s = SOME 0w /\
    (!i x. MEM i insts /\ MEM x i.inst_outputs /\ pred = Var x ==> F) /\
    (!mc x. MEM mc cands /\ pred = Var x /\
       (?i. MEM i insts /\ i.inst_id = mc.mc_second_id) ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) ==>
    ac_sim_precond cands ((id,pred)::mp) dfg insts s V
Proof
  rpt strip_tac >>
  qpat_x_assum `ac_sim_precond _ _ _ _ _ _` mp_tac >>
  simp[ac_sim_precond_def] >> strip_tac >>
  rpt conj_tac >> TRY (metis_tac[]) >>
  precond_alookup_ext_tac
QED

(* Head-drop + mp extension: compose transfer_same + extend_mp *)
Triviality ac_sim_precond_transfer_ext[local]:
  !h insts cands mp id pred dfg s_t V.
    ac_sim_precond cands mp dfg (h::insts) s_t V ==>
    (!i. MEM i insts ==> i.inst_id <> id) /\
    eval_operand pred s_t = SOME 0w /\
    (!i x. MEM i insts /\ MEM x i.inst_outputs /\ pred = Var x ==> F) /\
    (!mc x. MEM mc cands /\ pred = Var x /\
       (?i. MEM i insts /\ i.inst_id = mc.mc_second_id) ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (!mc. MEM mc cands /\ mc.mc_first_id = h.inst_id /\
       ALOOKUP mp mc.mc_first_id = NONE ==>
       eval_operand mc.mc_first_pred s_t = SOME 0w) ==>
    ac_sim_precond cands ((id,pred)::mp) dfg insts s_t V
Proof
  rpt strip_tac >>
  `ac_sim_precond cands mp dfg insts s_t V` by (
    qpat_x_assum `ac_sim_precond _ _ _ (h::_) _ _`
      (mp_tac o MATCH_MP ac_sim_precond_transfer_same) >>
    disch_then match_mp_tac >> simp[]) >>
  irule ac_sim_precond_extend_mp >> simp[] >>
  qpat_x_assum `ac_sim_precond _ _ _ insts _ _` mp_tac >>
  simp[ac_sim_precond_def] >> metis_tac[]
QED

(* Extract all head-instruction facts from ac_sim_precond.
   Avoids repeated simp[ac_sim_precond_def, EVERY_DEF] in case bodies. *)
Theorem ac_sim_precond_head_facts:
  !h insts cands mp dfg s V.
    ac_sim_precond cands mp dfg (h::insts) s V ==>
    (ac_is_safe_between h \/ h.inst_opcode = ASSERT) /\
    inst_wf h /\
    h.inst_opcode <> INVOKE /\
    ~is_terminator h.inst_opcode /\
    (!op. MEM op h.inst_operands ==> IS_SOME (eval_operand op s)) /\
    (!x. MEM (Var x) h.inst_operands ==> x NOTIN V) /\
    (!x. MEM x h.inst_outputs ==> x NOTIN V) /\
    (!mc. FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc ==>
       h.inst_opcode = ASSERT) /\
    (EXISTS (\mc. mc.mc_first_id = h.inst_id) cands ==> h.inst_opcode = ASSERT) /\
    (!mc x. MEM mc cands /\ MEM (Var x) h.inst_operands ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (!mc x. MEM mc cands /\ MEM x h.inst_outputs ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (!i x. MEM i insts /\ MEM x i.inst_outputs /\
       (ALOOKUP mp h.inst_id = SOME (Var x) \/
        ?mc. FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
             (mc.mc_first_pred = Var x \/ mc.mc_second_pred = Var x)) ==> F) /\
    ALOOKUP mp h.inst_id = NONE /\
    (!i. MEM i insts ==> ALOOKUP mp i.inst_id = NONE)
Proof
  rpt gen_tac >> simp[ac_sim_precond_def, EVERY_DEF] >>
  strip_tac >> rpt conj_tac >>
  metis_tac[FIND_MEM]
QED

(* All instruction outputs are outside V — extracted from ac_sim_precond. *)
Theorem ac_sim_precond_outputs_notin_V:
  !cands mp dfg insts s V.
    ac_sim_precond cands mp dfg insts s V ==>
    (!i x. MEM i insts /\ MEM x i.inst_outputs ==> x NOTIN V)
Proof
  simp[ac_sim_precond_def] >> metis_tac[]
QED

(* Transfer no-redefine condition across state_equiv: if output vars are
   undefined in s1, they are also undefined in s2 (provided outputs are
   outside V and the states agree on non-V variables). *)
Theorem no_redefine_transfer_equiv:
  !insts s1 s2 V.
    (!i x. MEM i insts /\ MEM x i.inst_outputs ==>
       ~IS_SOME (lookup_var x s1)) /\
    (!i x. MEM i insts /\ MEM x i.inst_outputs ==> x NOTIN V) /\
    state_equiv V s1 s2 ==>
    (!i x. MEM i insts /\ MEM x i.inst_outputs ==>
       ~IS_SOME (lookup_var x s2))
Proof
  rpt strip_tac >>
  `~IS_SOME (lookup_var x s1)` by metis_tac[] >>
  `x NOTIN V` by metis_tac[] >>
  `lookup_var x s1 = lookup_var x s2` by
    (fs[state_equiv_def, execution_equiv_def] >> metis_tac[]) >>
  metis_tac[]
QED

(* Output-related facts from head of precond: needed for eval_transfer. *)
Triviality ac_sim_precond_head_output_facts[local]:
  !h insts cands mp dfg s V.
    ac_sim_precond cands mp dfg (h::insts) s V ==>
    (!mc x. MEM mc cands /\
       (mc.mc_first_pred = Var x \/ mc.mc_second_pred = Var x) ==>
       ~MEM x h.inst_outputs) /\
    (!id x. ALOOKUP mp id = SOME (Var x) ==> ~MEM x h.inst_outputs) /\
    (!v. MEM v h.inst_outputs /\ dfg_get_def dfg v <> NONE ==>
       dfg_get_def dfg v = SOME h) /\
    (!op x. MEM op h.inst_operands /\ op = Var x ==>
       ~MEM x h.inst_outputs)
Proof
  rpt gen_tac >> simp[ac_sim_precond_def, EVERY_DEF] >>
  strip_tac >> rpt conj_tac >> metis_tac[]
QED

(* For non-ASSERT head, transfer_same's first_id condition is vacuous. *)
Triviality ac_sim_precond_transfer_non_assert[local]:
  !h insts cands mp dfg s V.
    ac_sim_precond cands mp dfg (h::insts) s V /\
    h.inst_opcode <> ASSERT ==>
    ac_sim_precond cands mp dfg insts s V
Proof
  rpt strip_tac >>
  qpat_assum `ac_sim_precond _ _ _ (h::_) _ _`
    (fn th => mp_tac (MATCH_MP ac_sim_precond_transfer_same th)) >>
  impl_tac >- (
    rpt strip_tac >>
    `EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands` by
      (simp[EXISTS_MEM] >> metis_tac[]) >>
    metis_tac[ac_sim_precond_head_facts]) >>
  simp[]
QED

(* Transfer ac_sim_precond through state change.
   Needs: (1) DFG inv on new state, (2) IS_SOME for instruction operands,
   (3) value-preservation for mp/cand preds. *)
Triviality ac_sim_precond_eval_transfer[local]:
  !insts cands mp dfg s s' V.
    ac_sim_precond cands mp dfg insts s V /\
    ac_dfg_inv dfg s' /\
    (!i op. MEM i insts /\ MEM op i.inst_operands /\
       IS_SOME (eval_operand op s) ==>
       IS_SOME (eval_operand op s')) /\
    (!mc. MEM mc cands ==>
       eval_operand mc.mc_second_pred s' = eval_operand mc.mc_second_pred s /\
       eval_operand mc.mc_first_pred s' = eval_operand mc.mc_first_pred s) /\
    (!id p. ALOOKUP mp id = SOME p ==>
       eval_operand p s' = eval_operand p s)
  ==>
    ac_sim_precond cands mp dfg insts s' V
Proof
  rpt strip_tac >>
  qpat_x_assum `ac_sim_precond _ _ _ _ s _` mp_tac >>
  simp[ac_sim_precond_def] >> strip_tac >>
  rpt conj_tac >> metis_tac[]
QED

(* Extract dfg_inv from ac_sim_precond. *)
Theorem ac_sim_precond_dfg_inv:
  !cands mp dfg insts s V.
    ac_sim_precond cands mp dfg insts s V ==> ac_dfg_inv dfg s
Proof
  simp[ac_sim_precond_def]
QED

(* Extract iszero operand from ac_sim_precond when FIND = SOME mc. *)
Theorem ac_sim_precond_find_iszero:
  !h insts cands mp dfg s V mc.
    ac_sim_precond cands mp dfg (h::insts) s V /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc ==>
    ?v. h.inst_operands = [Var v] /\
        ac_get_iszero_operand dfg {} (Var v) = SOME mc.mc_second_pred
Proof
  rpt strip_tac >>
  imp_res_tac FIND_MEM >> imp_res_tac FIND_P >> gvs[] >>
  qpat_x_assum `ac_sim_precond _ _ _ _ _ _` mp_tac >>
  simp[ac_sim_precond_def, EVERY_DEF]
QED

(* When ASSERT h passes on s_o and h is a first_id for mc,
   mc.mc_first_pred evaluates to 0w on s_t.
   Key bridge for the first_id side condition in transfer_same/ext. *)
Triviality ac_first_id_pred_zero[local]:
  !h insts cands mp dfg fuel ctx s_o s_t V mc.
    step_inst fuel ctx h s_o = OK s_o /\
    h.inst_opcode = ASSERT /\ inst_wf h /\
    state_equiv V s_o s_t /\
    ac_sim_precond cands mp dfg (h::insts) s_t V /\
    MEM mc cands /\ mc.mc_first_id = h.inst_id /\
    ALOOKUP mp mc.mc_first_id = NONE ==>
    eval_operand mc.mc_first_pred s_t = SOME 0w
Proof
  rpt strip_tac >>
  (* From ac_sim_precond: h has iszero chain to mc.mc_first_pred *)
  `?v. h.inst_operands = [Var v] /\
       ac_get_iszero_operand dfg {} (Var v) = SOME mc.mc_first_pred` by (
    qpat_x_assum `ac_sim_precond _ _ _ _ _ _` mp_tac >>
    simp[ac_sim_precond_def, EVERY_DEF] >> metis_tac[]) >>
  (* h's operand is nonzero on s_o (ASSERT pass) then on s_t (equiv) *)
  `?cval. eval_operand (Var v) s_o = SOME cval /\ cval <> 0w` by (
    `step_inst_base h s_o = OK s_o` by fs[step_inst_non_invoke] >>
    pop_assum mp_tac >>
    simp[step_inst_base_def] >>
    Cases_on `eval_operand (Var v) s_o` >> simp[] >>
    rename1 `SOME cv` >>
    Cases_on `cv = 0w` >> simp[]) >>
  `eval_operand (Var v) s_t = SOME cval` by (
    `v NOTIN V` by (
      drule ac_sim_precond_head_facts >> strip_tac >> fs[]) >>
    `eval_operand (Var v) s_o = eval_operand (Var v) s_t` by (
      irule eval_operand_equiv >> qexists_tac `V` >> simp[]) >>
    gvs[]) >>
  (* ac_dfg_inv on s_t + iszero bridge → pred = 0w *)
  `ac_dfg_inv dfg s_t` by (
    qpat_x_assum `ac_sim_precond _ _ _ _ _ _` mp_tac >>
    simp[ac_sim_precond_def]) >>
  irule ac_assert_pass_pred_zero >>
  MAP_EVERY qexists_tac [`dfg`, `v`, `cval`] >> simp[]
QED

(* Common preamble for FIND=SOME cases: ASSERT h passes on s_o with equiv s_t,
   FIND returns SOME mc => second_pred evaluates to 0w on s_t.
   Extracts iszero operand and bridges to pred = 0w. *)
Triviality ac_find_some_second_pred_zero[local]:
  !h insts cands mp dfg fuel ctx s_o s_t V mc.
    step_inst fuel ctx h s_o = OK s_o /\
    h.inst_opcode = ASSERT /\ inst_wf h /\
    h.inst_opcode <> INVOKE /\
    state_equiv V s_o s_t /\
    ac_sim_precond cands mp dfg (h::insts) s_t V /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    step_inst fuel ctx h s_t = OK s_t ==>
    eval_operand mc.mc_second_pred s_t = SOME 0w
Proof
  rpt strip_tac >>
  (* Get iszero operand *)
  `?v. h.inst_operands = [Var v] /\
       ac_get_iszero_operand dfg {} (Var v) = SOME mc.mc_second_pred` by
    metis_tac[ac_sim_precond_find_iszero] >>
  (* h's operand nonzero on s_t via step_inst_base *)
  `step_inst_base h s_t = OK s_t` by metis_tac[step_inst_non_invoke] >>
  `?cval. eval_operand (Var v) s_t = SOME cval /\ cval <> 0w` by (
    qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
    simp[step_inst_base_def] >>
    Cases_on `eval_operand (Var v) s_t` >> simp[] >>
    rename1 `SOME cv` >> Cases_on `cv = 0w` >> simp[]) >>
  (* Bridge: iszero operand + nonzero => pred = 0w *)
  `ac_dfg_inv dfg s_t` by metis_tac[ac_sim_precond_dfg_inv] >>
  irule ac_assert_pass_pred_zero >>
  MAP_EVERY qexists_tac [`dfg`, `v`, `cval`] >> simp[]
QED

(* Extract: ALOOKUP mp entries have fresh or/iz variable names *)
Theorem ac_sim_precond_mp_or_iz_fresh:
  !cands mp dfg insts s V id x mc.
    ac_sim_precond cands mp dfg insts s V /\
    ALOOKUP mp id = SOME (Var x) /\ MEM mc cands /\
    (?i. MEM i insts /\ i.inst_id = mc.mc_second_id) ==>
    x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id
Proof
  simp[ac_sim_precond_def] >> metis_tac[]
QED

(* Extract: ALOOKUP mp entries evaluate *)
Theorem ac_sim_precond_mp_eval:
  !cands mp dfg insts s V id p.
    ac_sim_precond cands mp dfg insts s V /\
    ALOOKUP mp id = SOME p ==>
    IS_SOME (eval_operand p s)
Proof
  simp[ac_sim_precond_def] >> metis_tac[]
QED

(* Extract: effective first pred (afp) is evaluable when FIND matches *)
Theorem ac_sim_precond_afp_eval:
  !h insts cands mp mc dfg s V.
    ac_sim_precond cands mp dfg (h::insts) s V /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc ==>
    IS_SOME (eval_operand
      (case ALOOKUP mp mc.mc_first_id of
         NONE => mc.mc_first_pred | SOME p => p) s)
Proof
  rpt strip_tac >>
  `MEM mc cands` by metis_tac[FIND_MEM] >>
  Cases_on `ALOOKUP mp mc.mc_first_id` >>
  fs[ac_sim_precond_def, optionTheory.IS_SOME_EXISTS] >>
  metis_tac[]
QED

(* FIND=SOME transfer: given head precond + FIND match + eval pred = 0w +
   pred shape + first_id discharge, derive extended tail precond.
   Used by all 4 FIND=SOME Resume blocks. *)
Triviality ac_sim_precond_transfer_find[local]:
  !h insts cands mp mc pred dfg s_t V.
    ac_sim_precond cands mp dfg (h::insts) s_t V /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    eval_operand pred s_t = SOME 0w /\
    (!i x. MEM i insts /\ MEM x i.inst_outputs /\ pred = Var x ==> F) /\
    (!mc' x. MEM mc' cands /\ pred = Var x /\
       (?i. MEM i insts /\ i.inst_id = mc'.mc_second_id) ==>
       x <> ac_or_var mc'.mc_second_id /\ x <> ac_iz_var mc'.mc_second_id) /\
    (!mc'. MEM mc' cands /\ mc'.mc_first_id = h.inst_id /\
       ALOOKUP mp mc'.mc_first_id = NONE ==>
       eval_operand mc'.mc_first_pred s_t = SOME 0w) ==>
    ac_sim_precond cands ((mc.mc_second_id,pred)::mp) dfg insts s_t V
Proof
  rpt gen_tac >> strip_tac >>
  `MEM mc cands` by metis_tac[FIND_MEM] >>
  `mc.mc_second_id = h.inst_id` by
    (imp_res_tac FIND_P >> full_simp_tac std_ss []) >>
  (* Step 1: tail precond via transfer_same *)
  `ac_sim_precond cands mp dfg insts s_t V` by (
    qpat_assum `ac_sim_precond _ _ _ (h::_) _ _`
      (fn th => mp_tac (MATCH_MP ac_sim_precond_transfer_same th)) >>
    disch_then match_mp_tac >> metis_tac[]) >>
  (* Step 2: extend mp — inst_id disjointness from ac_cands_ordered *)
  `!i. MEM i insts ==> i.inst_id <> mc.mc_second_id` by (
    qpat_assum `ac_sim_precond _ _ _ (h::_) _ _` mp_tac >>
    simp_tac (srw_ss()) [ac_sim_precond_def, ac_cands_ordered_def,
      MAP, ALL_DISTINCT, MEM_MAP] >> metis_tac[]) >>
  match_mp_tac ac_sim_precond_extend_mp >>
  simp_tac (srw_ss()) [] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >> metis_tac[]
QED

(* One-step transfer: processing h with ac_apply_merge_step preserves
   simulation and transfers all preconditions to the tail.
   This factors out all 6 cases of ac_apply_merge_step. *)
Theorem ac_sim_step_ok:
  !h insts cands mp dfg fuel ctx s_o s1_o s_t V.
    step_inst fuel ctx h s_o = OK s1_o /\
    state_equiv V s_o s_t /\
    ac_sim_precond cands mp dfg (h::insts) s_t V /\
    (* No-redefine: output vars of remaining insts are undefined in s_o *)
    (!i x. MEM i (h::insts) /\ MEM x i.inst_outputs ==>
       ~IS_SOME (lookup_var x s_o)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (h::insts))) ==>
    let (mp', contrib) = ac_apply_merge_step cands (mp, []) h in
    ?s_c.
      run_insts fuel ctx contrib s_t = OK s_c /\
      state_equiv V s1_o s_c /\
      ac_sim_precond cands mp' dfg insts s_c V
Proof
  rpt gen_tac >> strip_tac >>
  (* Extract head facts from ac_sim_precond (non-destructive, no disjunction split) *)
  `inst_wf h /\ h.inst_opcode <> INVOKE /\
   (!op. MEM op h.inst_operands ==> IS_SOME (eval_operand op s_t)) /\
   (!x. MEM (Var x) h.inst_operands ==> x NOTIN V) /\
   (!x. MEM x h.inst_outputs ==> x NOTIN V)` by
    metis_tac[ac_sim_precond_head_facts] >>
  (* Primary split: ASSERT vs safe_between *)
  Cases_on `h.inst_opcode = ASSERT`
  >- (
    `s1_o = s_o` by metis_tac[step_assert_identity] >> pop_assum SUBST_ALL_TAC >>
    (* ASSERT on equiv state also succeeds *)
    `step_inst fuel ctx h s_t = OK s_t` by (
      `result_equiv V (step_inst fuel ctx h s_o) (step_inst fuel ctx h s_t)` by (
        irule execEquivPropsTheory.step_inst_result_equiv >> simp[] >>
        metis_tac[]) >>
      qpat_x_assum `step_inst _ _ h s_o = _` (fn th => fs[th]) >>
      Cases_on `step_inst fuel ctx h s_t` >> gvs[result_equiv_def] >>
      imp_res_tac step_assert_identity >> gvs[]) >>
    (* Case-split on FIND *)
    Cases_on `FIND (\mc. mc.mc_second_id = h.inst_id) cands`
    >- (
      (* FIND = NONE: NOP or passthrough, mp unchanged *)
      `ac_apply_merge_step cands (mp,[]) h =
         if EXISTS (\mc. mc.mc_first_id = h.inst_id) cands then
           (mp, [h with <| inst_opcode := NOP;
                            inst_operands := [];
                            inst_outputs := [] |>])
         else (mp, [h])` by
        simp[ac_apply_merge_step_def, LET_THM] >>
      `ac_sim_precond cands mp dfg insts s_t V` by (
        qpat_assum `ac_sim_precond _ _ _ (h::_) _ _`
          (fn th => mp_tac (MATCH_MP ac_sim_precond_transfer_same th)) >>
        disch_then match_mp_tac >>
        rpt strip_tac >>
        metis_tac[ac_first_id_pred_zero]) >>
      Cases_on `EXISTS (\mc. mc.mc_first_id = h.inst_id) cands` >>
      gvs[LET_THM, run_insts_def, step_nop_identity] >>
      qexists_tac `s_t` >> simp[]
    )
    >- (
      rename1 `FIND _ _ = SOME mc` >>
      qabbrev_tac `afp = case ALOOKUP mp mc.mc_first_id of
                            SOME p => p | NONE => mc.mc_first_pred` >>
      (* second_pred evaluates to 0w *)
      `eval_operand mc.mc_second_pred s_t = SOME 0w` by
        metis_tac[ac_find_some_second_pred_zero] >>
      Cases_on `afp = mc.mc_second_pred`
      >- (
        (* same preds *)
        `ac_apply_merge_step cands (mp,[]) h =
           if EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands then
             ((mc.mc_second_id, afp)::mp,
              [h with <| inst_opcode := NOP;
                          inst_operands := [];
                          inst_outputs := [] |>])
           else
             ((mc.mc_second_id, afp)::mp, [h])` by
          simp[ac_apply_merge_step_def, LET_THM, Abbr `afp`] >>
        Cases_on `EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands`
        >- (
          gvs[LET_THM, run_insts_def, step_nop_identity] >>
          suspend "same_preds_fid")
        >- (
          gvs[LET_THM, run_insts_def] >> simp[] >>
          suspend "same_preds_nofid")
      )
      >- (
        (* diff preds: OR + ISZERO *)
        qabbrev_tac `or_v = ac_or_var h.inst_id` >>
        qabbrev_tac `iz_v = ac_iz_var h.inst_id` >>
        `ac_apply_merge_step cands (mp,[]) h =
           if EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands then
             ((mc.mc_second_id, Var or_v)::mp,
              [<| inst_id := h.inst_id; inst_opcode := OR;
                  inst_operands := [afp; mc.mc_second_pred];
                  inst_outputs := [or_v] |>;
               <| inst_id := h.inst_id + 1; inst_opcode := ISZERO;
                  inst_operands := [Var or_v];
                  inst_outputs := [iz_v] |>;
               h with <| inst_opcode := NOP;
                          inst_operands := [];
                          inst_outputs := [] |>])
           else
             ((mc.mc_second_id, Var or_v)::mp,
              [<| inst_id := h.inst_id; inst_opcode := OR;
                  inst_operands := [afp; mc.mc_second_pred];
                  inst_outputs := [or_v] |>;
               <| inst_id := h.inst_id + 1; inst_opcode := ISZERO;
                  inst_operands := [Var or_v];
                  inst_outputs := [iz_v] |>;
               h with inst_operands := [Var iz_v]])` by
          simp[ac_apply_merge_step_def, LET_THM, Abbr `afp`,
               Abbr `or_v`, Abbr `iz_v`] >>
        Cases_on `EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands`
        >- (gvs[LET_THM] >> suspend "diff_preds_fid")
        >- (gvs[LET_THM] >> suspend "diff_preds_nofid")
      )
    )
  )
  >- (
    suspend "safe_between"
  )
QED

(* Helper: non-ASSERT instructions get passthrough from ac_sim_precond *)
Triviality ac_sim_precond_passthrough[local]:
  !cands mp dfg h insts s_t V.
    ac_sim_precond cands mp dfg (h::insts) s_t V /\
    h.inst_opcode <> ASSERT ==>
    ac_apply_merge_step cands (mp, []) h = (mp, [h])
Proof
  rpt strip_tac >>
  `FIND (\mc. mc.mc_second_id = h.inst_id) cands = NONE` by (
    Cases_on `FIND (\mc. mc.mc_second_id = h.inst_id) cands` >> simp[] >>
    metis_tac[ac_sim_precond_head_facts]) >>
  `~EXISTS (\mc. mc.mc_first_id = h.inst_id) cands` by
    metis_tac[ac_sim_precond_head_facts] >>
  metis_tac[ac_step_passthrough]
QED

(* Helper: ASSERT on equiv state also succeeds *)
Triviality ac_assert_ok_on_equiv[local]:
  !fuel ctx h s_o s_t V.
    step_inst fuel ctx h s_o = OK s_o /\
    h.inst_opcode = ASSERT /\ h.inst_opcode <> INVOKE /\
    state_equiv V s_o s_t /\
    (!x. MEM (Var x) h.inst_operands ==> x NOTIN V) ==>
    step_inst fuel ctx h s_t = OK s_t
Proof
  rpt strip_tac >>
  `result_equiv V (step_inst fuel ctx h s_o) (step_inst fuel ctx h s_t)` by (
    irule execEquivPropsTheory.step_inst_result_equiv >> simp[] >>
    metis_tac[]) >>
  fs[] >>
  Cases_on `step_inst fuel ctx h s_t` >> gvs[result_equiv_def] >>
  imp_res_tac step_assert_identity
QED

(* Combined forward-reasoning helper: transfer ac_sim_precond through a
   safe_between step. Packages ac_dfg_inv_step + ac_sim_precond_eval_transfer
   into a single lemma usable via match_mp_tac in Resume blocks (avoids the
   irule metavariable problem that breaks batch mode). *)
Triviality ac_sim_precond_step_transfer[local]:
  !h insts cands mp dfg fuel ctx s s_c V.
    ac_sim_precond cands mp dfg insts s V /\
    ac_is_safe_between h /\
    step_inst fuel ctx h s = OK s_c /\
    inst_wf h /\ ~is_terminator h.inst_opcode /\ h.inst_opcode <> INVOKE /\
    (!op. MEM op h.inst_operands ==> IS_SOME (eval_operand op s)) /\
    (!mc x. MEM mc cands /\
       (mc.mc_first_pred = Var x \/ mc.mc_second_pred = Var x) ==>
       ~MEM x h.inst_outputs) /\
    (!id x. ALOOKUP mp id = SOME (Var x) ==> ~MEM x h.inst_outputs) /\
    (!v. MEM v h.inst_outputs /\ dfg_get_def dfg v <> NONE ==>
       dfg_get_def dfg v = SOME h) /\
    (* Self: h's operand vars not among h's outputs *)
    (!op x. MEM op h.inst_operands /\ op = Var x ==>
       ~MEM x h.inst_outputs) /\
    (* No-redefine: h doesn't redefine already-defined variables *)
    (!x. MEM x h.inst_outputs ==> ~IS_SOME (lookup_var x s))
  ==>
    ac_sim_precond cands mp dfg insts s_c V
Proof
  rpt strip_tac >>
  (* Step 1: establish ac_dfg_inv dfg s_c *)
  (Q.SUBGOAL_THEN `ac_dfg_inv dfg s` ASSUME_TAC >-
    metis_tac[ac_sim_precond_dfg_inv]) >>
  (Q.SUBGOAL_THEN `ac_dfg_inv dfg s_c` ASSUME_TAC >- (
    qspecl_then [`fuel`, `ctx`, `h`, `s`, `s_c`, `dfg`]
      mp_tac ac_dfg_inv_step >>
    simp[] >>
    rpt strip_tac >> res_tac >>
    gvs[optionTheory.NOT_IS_SOME_EQ_NONE])) >>
  (* Step 2: apply eval_transfer *)
  match_mp_tac ac_sim_precond_eval_transfer >>
  qexists_tac `s` >>
  simp_tac (srw_ss()) [] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC (* ac_sim_precond *)
  >- first_assum ACCEPT_TAC (* ac_dfg_inv dfg s_c *)
  >- metis_tac[safe_between_step_eval_is_some]
  >- metis_tac[step_eval_operand_preserved]
  >- metis_tac[step_eval_operand_preserved]
QED

(* --- Helpers for diff_preds Resume blocks --- *)

(* The effective first predicate always evaluates to 0w when FIND=SOME.
   Reason: ac_cands_ordered ensures mc.mc_first_id is NOT in (h::insts)
   when mc.mc_second_id = h.inst_id (first comes before second, but
   idx_f < 0 is impossible). So mc.mc_first_id was already processed.
   Then: ALOOKUP mp mc.mc_first_id = SOME p ⇒ eval p s_t = SOME 0w,
         ALOOKUP mp mc.mc_first_id = NONE ⇒ eval mc.mc_first_pred s_t = SOME 0w. *)
(* When mc.mc_second_id = h.inst_id (head), mc.mc_first_id <> h.inst_id.
   Because: if first=second=h, ac_cands_ordered gives idx_f < idx_s with
   both pointing to h (by ALL_DISTINCT), contradiction. *)
Triviality ac_cands_first_ne_second_at_head[local]:
  !cands h insts mc.
    ac_cands_ordered cands (h::insts) /\ MEM mc cands /\
    mc.mc_second_id = h.inst_id ==>
    mc.mc_first_id <> h.inst_id
Proof
  rpt strip_tac >>
  spose_not_then assume_tac >>
  fs[ac_cands_ordered_def] >>
  first_x_assum (qspec_then `mc` mp_tac) >>
  impl_tac
  >- (simp[] >> qexists_tac `h` >> simp[])
  >- (strip_tac >>
      `ALL_DISTINCT (MAP (\i'. i'.inst_id) (h::insts))` by
        simp[ALL_DISTINCT] >>
      `EL idx_s (MAP (\i'. i'.inst_id) (h::insts)) = h.inst_id` by
        simp[EL_MAP] >>
      `EL 0 (MAP (\i'. i'.inst_id) (h::insts)) = h.inst_id` by
        simp[EL_MAP] >>
      `idx_s < LENGTH (MAP (\i'. i'.inst_id) (h::insts))` by simp[] >>
      `0 < LENGTH (MAP (\i'. i'.inst_id) (h::insts))` by simp[] >>
      `idx_s = 0` by metis_tac[ALL_DISTINCT_EL_IMP] >>
      full_simp_tac std_ss [])
QED

(* When FIND=SOME mc at head, mc.mc_first_id is not ANY instruction in h::insts. *)
Triviality ac_cands_first_not_in_list[local]:
  !cands h insts mc.
    ac_cands_ordered cands (h::insts) /\ MEM mc cands /\
    mc.mc_second_id = h.inst_id ==>
    !i. MEM i (h::insts) ==> i.inst_id <> mc.mc_first_id
Proof
  rpt strip_tac >>
  Cases_on `MEM i insts`
  >- metis_tac[ac_cands_second_at_head]
  >- (`i = h` by (full_simp_tac std_ss [MEM]) >>
      full_simp_tac std_ss [] >>
      metis_tac[ac_cands_first_ne_second_at_head])
QED

Triviality ac_effective_first_pred_zero[local]:
  !h insts cands mp dfg s_t V mc afp.
    ac_sim_precond cands mp dfg (h::insts) s_t V /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    afp = (case ALOOKUP mp mc.mc_first_id of
             NONE => mc.mc_first_pred | SOME p => p) ==>
    eval_operand afp s_t = SOME 0w
Proof
  rpt strip_tac >>
  `MEM mc cands` by metis_tac[FIND_MEM] >>
  `mc.mc_second_id = h.inst_id` by
    (imp_res_tac FIND_P >> full_simp_tac std_ss []) >>
  `!i. MEM i (h::insts) ==> i.inst_id <> mc.mc_first_id` by (
    `ac_cands_ordered cands (h::insts)` by (
      qpat_assum `ac_sim_precond _ _ _ (h::_) _ _` mp_tac >>
      simp_tac (srw_ss()) [ac_sim_precond_def] >> metis_tac[]) >>
    metis_tac[ac_cands_first_not_in_list]) >>
  Cases_on `ALOOKUP mp mc.mc_first_id` >> gvs[]
  >- ((* NONE: use "processed first_ids" clause *)
      qpat_assum `ac_sim_precond _ _ _ (h::_) _ _` mp_tac >>
      simp_tac (srw_ss()) [ac_sim_precond_def] >> rpt strip_tac >>
      metis_tac[MEM])
  >- ((* SOME: use "all mp values eval to 0w" clause *)
      qpat_assum `ac_sim_precond _ _ _ (h::_) _ _` mp_tac >>
      simp_tac (srw_ss()) [ac_sim_precond_def] >> rpt strip_tac >>
      metis_tac[])
QED

(* Updating one side with a variable in V preserves state_equiv *)
Triviality state_equiv_update_in_V[local]:
  !V x val s1 s2.
    state_equiv V s1 s2 /\ x IN V ==>
    state_equiv V s1 (update_var x val s2)
Proof
  simp[state_equiv_def, execution_equiv_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >> rpt strip_tac >>
  rw[] >> metis_tac[]
QED

(* Transfer precond through OR+ISZERO fresh var updates.
   Packages transfer_same + update_fresh_var x2 with mc-based freshness.
   Uses sid directly (not mc.mc_second_id) so match_mp_tac can unify. *)
Triviality ac_sim_precond_or_iz_transfer[local]:
  !h insts cands mp sid dfg s_t V or_val iz_val.
    ac_sim_precond cands mp dfg (h::insts) s_t V /\
    (?mc. MEM mc cands /\ mc.mc_second_id = sid) /\
    sid = h.inst_id /\
    (!mc'. MEM mc' cands /\ mc'.mc_first_id = h.inst_id /\
       ALOOKUP mp mc'.mc_first_id = NONE ==>
       eval_operand mc'.mc_first_pred s_t = SOME 0w) ==>
    ac_sim_precond cands mp dfg insts
      (update_var (ac_iz_var sid) iz_val
        (update_var (ac_or_var sid) or_val s_t)) V
Proof
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  `ac_sim_precond cands mp dfg insts s_t V` by (
    qpat_assum `ac_sim_precond _ _ _ (h::_) _ _`
      (fn th => mp_tac (MATCH_MP ac_sim_precond_transfer_same th)) >>
    disch_then match_mp_tac >> metis_tac[]) >>
  irule ac_sim_precond_update_fresh_var >>
  conj_tac >- (
    qpat_assum `ac_sim_precond _ _ _ (h::_) _ _` mp_tac >>
    simp_tac (srw_ss()) [ac_sim_precond_def] >> metis_tac[]) >>
  conj_tac >- (
    rpt strip_tac >>
    qpat_assum `ac_sim_precond _ _ _ (h::_) _ _` mp_tac >>
    simp_tac (srw_ss()) [ac_sim_precond_def] >> metis_tac[]) >>
  conj_tac >- (
    rpt strip_tac >>
    qpat_assum `ac_sim_precond _ _ _ (h::_) _ _` mp_tac >>
    simp_tac (srw_ss()) [ac_sim_precond_def] >> metis_tac[]) >>
  irule ac_sim_precond_update_fresh_var >>
  conj_tac >- (
    qpat_assum `ac_sim_precond _ _ _ (h::_) _ _` mp_tac >>
    simp_tac (srw_ss()) [ac_sim_precond_def] >> metis_tac[]) >>
  conj_tac >- (
    rpt strip_tac >>
    qpat_assum `ac_sim_precond _ _ _ (h::_) _ _` mp_tac >>
    simp_tac (srw_ss()) [ac_sim_precond_def] >> metis_tac[]) >>
  conj_tac >- (
    rpt strip_tac >>
    qpat_assum `ac_sim_precond _ _ _ (h::_) _ _` mp_tac >>
    simp_tac (srw_ss()) [ac_sim_precond_def] >> metis_tac[]) >>
  first_assum ACCEPT_TAC
QED

(* Shared tactic for diff_preds Resume blocks: execute OR+ISZERO chain,
   establish state_equiv and ac_sim_precond at the intermediate state.
   After this tactic, the only remaining goal is about the 3rd instruction. *)
Triviality ac_diff_preds_or_iz[local]:
  !h insts cands mp mc afp dfg fuel ctx s_o s_t V or_v iz_v.
    step_inst fuel ctx h s_o = OK s_o /\
    step_inst fuel ctx h s_t = OK s_t /\
    h.inst_opcode = ASSERT /\ inst_wf h /\
    state_equiv V s_o s_t /\
    ac_sim_precond cands mp dfg (h::insts) s_t V /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    eval_operand mc.mc_second_pred s_t = SOME 0w /\
    afp <> mc.mc_second_pred /\
    Abbrev (afp = case ALOOKUP mp mc.mc_first_id of
                    NONE => mc.mc_first_pred | SOME p => p) /\
    Abbrev (or_v = ac_or_var h.inst_id) /\
    Abbrev (iz_v = ac_iz_var h.inst_id) ==>
    let or_inst = <| inst_id := h.inst_id; inst_opcode := OR;
                     inst_operands := [afp; mc.mc_second_pred];
                     inst_outputs := [or_v] |> in
    let iz_inst = <| inst_id := h.inst_id + 1; inst_opcode := ISZERO;
                     inst_operands := [Var or_v];
                     inst_outputs := [iz_v] |> in
    ?s_iz.
      run_insts fuel ctx [or_inst; iz_inst] s_t = OK s_iz /\
      eval_operand (Var or_v) s_iz = SOME 0w /\
      eval_operand (Var iz_v) s_iz = SOME 1w /\
      state_equiv V s_o s_iz /\
      ac_sim_precond cands mp dfg insts s_iz V /\
      (!op. (!x. op = Var x ==> x <> or_v /\ x <> iz_v) ==>
         eval_operand op s_iz = eval_operand op s_t)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM mc cands` by metis_tac[FIND_MEM] >>
  `mc.mc_second_id = h.inst_id` by (drule FIND_P >> simp[]) >>
  (* or_v, iz_v are fresh (in V) — extract early before ac_or_iz_step *)
  `or_v IN V /\ iz_v IN V` by (
    qpat_assum `ac_sim_precond _ _ _ (h::_) _ _` mp_tac >>
    simp_tac (srw_ss()) [ac_sim_precond_def] >> strip_tac >>
    qpat_x_assum `!mc'. MEM mc' cands ==> _ IN V /\ _ IN V`
      (qspec_then `mc` mp_tac) >>
    simp[Abbr `or_v`, Abbr `iz_v`]) >>
  (* effective first pred evaluates to 0w *)
  `eval_operand afp s_t = SOME 0w` by (
    match_mp_tac ac_effective_first_pred_zero >>
    MAP_EVERY qexists_tac [`h`, `insts`, `cands`, `mp`, `dfg`, `V`, `mc`] >>
    full_simp_tac std_ss [markerTheory.Abbrev_def]) >>
  `or_v <> iz_v` by
    simp[Abbr `or_v`, Abbr `iz_v`, ac_or_var_def, ac_iz_var_def] >>
  (* Execute OR+ISZERO via ac_or_iz_step *)
  simp_tac std_ss [LET_THM] >>
  qabbrev_tac `s_iz = update_var iz_v (bool_to_word (word_or 0w 0w = 0w))
                        (update_var or_v (word_or 0w 0w) s_t)` >>
  qexists_tac `s_iz` >>
  qspecl_then [`fuel`, `ctx`, `s_t`, `afp`, `mc.mc_second_pred`,
               `or_v`, `iz_v`, `h.inst_id`, `0w`, `0w`]
    mp_tac ac_or_iz_step >>
  (impl_tac >- simp[]) >>
  simp_tac (srw_ss()) [LET_THM, wordsTheory.WORD_OR_CLAUSES,
                        bool_to_word_def] >>
  `update_var iz_v (1w:256 word) (update_var or_v 0w s_t) = s_iz` by
    simp[Abbr `s_iz`, wordsTheory.WORD_OR_CLAUSES, bool_to_word_def] >>
  ASM_REWRITE_TAC [] >>
  strip_tac >>
  gvs[instruction_to_literal] >>
  rpt conj_tac
  >- (
    (* state_equiv V s_o s_iz: or_v, iz_v ∈ V so updates are invisible *)
    irule state_equiv_update_in_V >> ASM_REWRITE_TAC [] >>
    irule state_equiv_update_in_V >> ASM_REWRITE_TAC [])
  >- (
    (* ac_sim_precond at s_iz via or_iz_transfer *)
    qpat_x_assum `Abbrev (or_v = _)` (SUBST_ALL_TAC o
      REWRITE_RULE [markerTheory.Abbrev_def]) >>
    qpat_x_assum `Abbrev (iz_v = _)` (SUBST_ALL_TAC o
      REWRITE_RULE [markerTheory.Abbrev_def]) >>
    qspecl_then [`h`, `insts`, `cands`, `mp`, `h.inst_id`, `dfg`,
                 `s_t`, `V`, `0w`, `1w`]
      mp_tac ac_sim_precond_or_iz_transfer >>
    disch_then match_mp_tac >>
    simp_tac (srw_ss()) [] >>
    metis_tac[ac_first_id_pred_zero])
QED

(* --- Resume blocks for ac_sim_step_ok --- *)

(* Shared tactic for same_preds FIND=SOME Resume blocks:
   match_mp_tac transfer_find + instantiate existential h *)
val find_transfer_tac =
  match_mp_tac ac_sim_precond_transfer_find >>
  qexists_tac `h` >>
  simp_tac (srw_ss()) [] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC);

Resume ac_sim_step_ok[same_preds_fid]:
  find_transfer_tac
  >- (rpt strip_tac >>
      qpat_assum `ac_sim_precond _ _ _ (h::_) _ _` mp_tac >>
      simp_tac (srw_ss()) [ac_sim_precond_def] >> metis_tac[FIND_MEM])
  >- (rpt strip_tac >>
      qpat_assum `ac_sim_precond _ _ _ (h::_) _ _` mp_tac >>
      simp_tac (srw_ss()) [ac_sim_precond_def] >> metis_tac[FIND_MEM])
  >- metis_tac[ac_first_id_pred_zero]
QED

Resume ac_sim_step_ok[same_preds_nofid]:
  find_transfer_tac
  >- (rpt strip_tac >>
      qpat_assum `ac_sim_precond _ _ _ (h::_) _ _` mp_tac >>
      simp_tac (srw_ss()) [ac_sim_precond_def] >> metis_tac[FIND_MEM])
  >- (rpt strip_tac >>
      qpat_assum `ac_sim_precond _ _ _ (h::_) _ _` mp_tac >>
      simp_tac (srw_ss()) [ac_sim_precond_def] >> metis_tac[FIND_MEM])
  >- metis_tac[ac_first_id_pred_zero]
QED

(* Packages extend_mp + all 5 side conditions for diff_preds cases.
   Proved in clean context (no inst_wf), usable via match_mp_tac. *)
Triviality ac_sim_precond_diff_preds_extend[local]:
  !cands mp dfg h insts mc s_iz V.
    ac_sim_precond cands mp dfg insts s_iz V /\
    ac_sim_precond cands mp dfg (h::insts) s_t V /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    eval_operand (Var (ac_or_var h.inst_id)) s_iz = SOME 0w ==>
    ac_sim_precond cands
      ((mc.mc_second_id, Var (ac_or_var h.inst_id))::mp) dfg insts s_iz V
Proof
  rpt strip_tac >>
  `mc.mc_second_id = h.inst_id` by (
    first_assum (mp_tac o MATCH_MP FIND_P) >> simp[]) >>
  match_mp_tac ac_sim_precond_extend_mp >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- ((* inst_id disjointness *)
      qpat_assum `ac_sim_precond _ _ _ (h::_) _ _` mp_tac >>
      full_simp_tac std_ss [ac_sim_precond_def, ac_cands_ordered_def,
        MAP, ALL_DISTINCT, MEM_MAP] >> metis_tac[])
  >- first_assum ACCEPT_TAC
  >- ((* output disjointness *)
      rpt strip_tac >>
      full_simp_tac std_ss [operand_11] >>
      `ac_or_var h.inst_id IN V` by (
        `MEM mc cands` by metis_tac[FIND_MEM] >>
        qpat_assum `ac_sim_precond _ _ _ insts _ _` mp_tac >>
        full_simp_tac std_ss [ac_sim_precond_def] >> metis_tac[]) >>
      qpat_assum `ac_sim_precond _ _ _ insts _ _` mp_tac >>
      full_simp_tac std_ss [ac_sim_precond_def] >> metis_tac[])
  >- ((* freshvar disjointness: ac_or_var h.inst_id <> ac_or/iz_var mc'.mc_second_id *)
      rpt strip_tac >>
      (* Var (ac_or_var h.inst_id) = Var x gives x = ac_or_var h.inst_id *)
      full_simp_tac std_ss [operand_11] >>
      (* Need h.inst_id <> mc'.mc_second_id from ALL_DISTINCT *)
      `ALL_DISTINCT (MAP (\i. i.inst_id) (h::insts))` by (
        qpat_assum `ac_sim_precond _ _ _ (h::_) _ _` mp_tac >>
        full_simp_tac std_ss [ac_sim_precond_def, ac_cands_ordered_def]) >>
      full_simp_tac std_ss [MAP, ALL_DISTINCT, MEM_MAP] >>
      `mc'.mc_second_id <> h.inst_id` by metis_tac[] >>
      full_simp_tac std_ss [ac_or_var_inj, ac_or_iz_distinct])
QED

Resume ac_sim_step_ok[diff_preds_fid]:
  `?s_iz.
     run_insts fuel ctx
       [<| inst_id := h.inst_id; inst_opcode := OR;
           inst_operands := [afp; mc.mc_second_pred]; inst_outputs := [or_v] |>;
        <| inst_id := h.inst_id + 1; inst_opcode := ISZERO;
           inst_operands := [Var or_v]; inst_outputs := [iz_v] |>] s_t = OK s_iz /\
     eval_operand (Var or_v) s_iz = SOME 0w /\
     eval_operand (Var iz_v) s_iz = SOME 1w /\
     state_equiv V s_o s_iz /\
     ac_sim_precond cands mp dfg insts s_iz V /\
     (!op. (!x. op = Var x ==> x <> or_v /\ x <> iz_v) ==>
        eval_operand op s_iz = eval_operand op s_t)` by (
    match_mp_tac (SIMP_RULE std_ss [LET_THM] ac_diff_preds_or_iz) >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `s_iz` >>
  `run_insts fuel ctx
     [<| inst_id := h.inst_id; inst_opcode := OR;
         inst_operands := [afp; mc.mc_second_pred]; inst_outputs := [or_v] |>;
      <| inst_id := h.inst_id + 1; inst_opcode := ISZERO;
         inst_operands := [Var or_v]; inst_outputs := [iz_v] |>;
      h with <| inst_opcode := NOP; inst_operands := []; inst_outputs := [] |>]
     s_t = OK s_iz` by (
    match_mp_tac run_insts_two_snoc_nop >>
    conj_tac >- first_assum ACCEPT_TAC >>
    simp_tac (srw_ss()) []) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  full_simp_tac std_ss [Abbr `or_v`] >>
  match_mp_tac ac_sim_precond_diff_preds_extend >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume ac_sim_step_ok[diff_preds_nofid]:
  (* Execute OR+ISZERO via ac_diff_preds_or_iz *)
  `?s_iz.
     run_insts fuel ctx
       [<| inst_id := h.inst_id; inst_opcode := OR;
           inst_operands := [afp; mc.mc_second_pred]; inst_outputs := [or_v] |>;
        <| inst_id := h.inst_id + 1; inst_opcode := ISZERO;
           inst_operands := [Var or_v]; inst_outputs := [iz_v] |>] s_t = OK s_iz /\
     eval_operand (Var or_v) s_iz = SOME 0w /\
     eval_operand (Var iz_v) s_iz = SOME 1w /\
     state_equiv V s_o s_iz /\
     ac_sim_precond cands mp dfg insts s_iz V /\
     (!op. (!x. op = Var x ==> x <> or_v /\ x <> iz_v) ==>
        eval_operand op s_iz = eval_operand op s_t)` by (
    match_mp_tac (SIMP_RULE std_ss [LET_THM] ac_diff_preds_or_iz) >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  (* Modified ASSERT with Var iz_v: iz_v = 1w ≠ 0w -> ASSERT succeeds *)
  `step_inst fuel ctx (h with inst_operands := [Var iz_v]) s_iz = OK s_iz` by (
    qpat_assum `inst_wf _` (K ALL_TAC) >>
    qpat_assum `ac_sim_precond _ _ _ _ _ _` (K ALL_TAC) >>
    qpat_assum `ac_sim_precond _ _ _ _ _ _` (K ALL_TAC) >>
    gvs[step_inst_non_invoke, step_inst_base_def]) >>
  qexists_tac `s_iz` >>
  (* Compose: run_insts [or;iz] s_t = OK s_iz, step h' s_iz = OK s_iz *)
  conj_tac >- (match_mp_tac run_insts_two_snoc >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  full_simp_tac std_ss [Abbr `or_v`] >>
  match_mp_tac ac_sim_precond_diff_preds_extend >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* If lookup_var x is NONE in s1, and x ∉ V, and state_equiv V s1 s2,
   then lookup_var x is also NONE in s2. *)
Theorem no_redefine_state_equiv_transfer:
  !x s1 s2 V.
    lookup_var x s1 = NONE /\ x NOTIN V /\ state_equiv V s1 s2 ==>
    lookup_var x s2 = NONE
Proof
  rpt strip_tac >>
  fs[state_equiv_def, execution_equiv_def]
QED

Resume ac_sim_step_ok[safe_between]:
  `ac_apply_merge_step cands (mp,[]) h = (mp, [h])` by
    metis_tac[ac_sim_precond_passthrough] >>
  pop_assum (fn eq => PURE_REWRITE_TAC[eq]) >>
  PURE_REWRITE_TAC[LET_THM] >> BETA_TAC >>
  `result_equiv V (step_inst fuel ctx h s_o) (step_inst fuel ctx h s_t)` by (
    irule execEquivPropsTheory.step_inst_result_equiv >>
    simp_tac (srw_ss()) [] >> metis_tac[]) >>
  pop_assum mp_tac >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  Cases_on `step_inst fuel ctx h s_t` >>
  full_simp_tac std_ss [result_equiv_def] >>
  rename1 `step_inst fuel ctx h s_t = OK s_c` >>
  qexists_tac `s_c` >>
  PURE_REWRITE_TAC[run_insts_def] >>
  ASM_REWRITE_TAC[run_insts_def] >>
  simp_tac (srw_ss()) [] >>
  `ac_sim_precond cands mp dfg insts s_t V` by
    metis_tac[ac_sim_precond_transfer_non_assert] >>
  `ac_is_safe_between h` by
    metis_tac[ac_sim_precond_head_facts] >>
  drule ac_sim_precond_head_output_facts >> strip_tac >>
  (* Derive no-redefine for s_t from no-redefine for s_o + state_equiv *)
  (Q.SUBGOAL_THEN `!x. MEM x h.inst_outputs ==> lookup_var x s_t = NONE`
    ASSUME_TAC >- (
    rpt strip_tac >>
    qspecl_then [`x`, `s_o`, `s_t`, `V`]
      mp_tac no_redefine_state_equiv_transfer >>
    disch_then match_mp_tac >>
    rpt conj_tac
    >- (res_tac >> gvs[MEM])
    >- metis_tac[ac_sim_precond_head_facts]
    >- first_assum ACCEPT_TAC)) >>
  (* Convert = NONE form to ~IS_SOME form *)
  (Q.SUBGOAL_THEN `!x. MEM x h.inst_outputs ==> ~IS_SOME (lookup_var x s_t)`
    ASSUME_TAC >-
    (rpt strip_tac >> res_tac >>
     gvs[optionTheory.NOT_IS_SOME_EQ_NONE])) >>
  match_mp_tac ac_sim_precond_step_transfer >>
  MAP_EVERY qexists_tac [`h`, `fuel`, `ctx`, `s_t`] >>
  simp_tac (srw_ss()) [] >>
  metis_tac[ac_sim_precond_head_facts]
QED

Finalise ac_sim_step_ok;

(* After stepping the head instruction h successfully, the no-redefine and
   ALL_DISTINCT conditions are maintained for the tail insts. Extracted as a
   shared lemma so both ac_run_insts_sim_ok and ac_run_insts_sim_abort can
   use it without duplicating the maintenance proof. *)
Theorem no_redefine_step_tail:
  !fuel ctx h s_o s1_o insts.
    step_inst fuel ctx h s_o = OK s1_o /\
    ~is_terminator h.inst_opcode /\
    (!i x. MEM i (h::insts) /\ MEM x i.inst_outputs ==>
       ~IS_SOME (lookup_var x s_o)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (h::insts))) ==>
    (!i x. MEM i insts /\ MEM x i.inst_outputs ==>
       ~IS_SOME (lookup_var x s1_o)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (
    rpt strip_tac >>
    `~MEM x h.inst_outputs` by (
      gvs[ALL_DISTINCT_APPEND] >>
      `MEM x (FLAT (MAP (\i. i.inst_outputs) insts))` by
        (simp[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
      metis_tac[]) >>
    `lookup_var x s1_o = lookup_var x s_o` by
      metis_tac[step_preserves_non_output_vars] >>
    metis_tac[MEM])
  >- gvs[ALL_DISTINCT_APPEND]
QED

Theorem ac_run_insts_sim_ok:
  !insts cands mp dfg fuel ctx s_o s_t s_orig V.
    run_insts fuel ctx insts s_o = OK s_orig /\
    state_equiv V s_o s_t /\
    ac_sim_precond cands mp dfg insts s_t V /\
    (!i x. MEM i insts /\ MEM x i.inst_outputs ==>
       ~IS_SOME (lookup_var x s_o)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) ==>
    ?s_trans.
      run_insts fuel ctx
        (SND (FOLDL (ac_apply_merge_step cands) (mp, []) insts)) s_t =
        OK s_trans /\
      state_equiv V s_orig s_trans
Proof
  Induct >- simp[run_insts_def] >>
  rpt gen_tac >> strip_tac >>
  (* Decompose run_insts for h::rest *)
  qpat_x_assum `run_insts _ _ (h::_) _ = _` mp_tac >>
  simp[Once run_insts_def] >>
  Cases_on `step_inst fuel ctx h s_o` >> simp[] >>
  rename1 `step_inst fuel ctx h s_o = OK s1_o` >> strip_tac >>
  (* Apply one-step transfer *)
  drule_all ac_sim_step_ok >> simp[LET_THM] >>
  Cases_on `ac_apply_merge_step cands (mp,[]) h` >>
  rename1 `_ = (mp', contrib)` >> simp[] >>
  strip_tac >>
  (* Decompose FOLDL and use run_insts_append *)
  qspecl_then [`h`, `insts`, `cands`, `mp`] mp_tac ac_foldl_cons >>
  simp[LET_THM] >> strip_tac >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  simp[run_insts_append] >>
  (* Maintain no-redefine for tail: s_o -> s1_o,
     ~IS_SOME(lookup_var x s1_o) from ~IS_SOME(lookup_var x s_o) + ~MEM x h.inst_outputs
     The ~MEM x h.inst_outputs follows from ALL_DISTINCT. *)
  (Q.SUBGOAL_THEN `!i x. MEM i insts /\ MEM x i.inst_outputs ==>
      ~IS_SOME (lookup_var x s1_o)` ASSUME_TAC >- (
    rpt strip_tac >>
    `~is_terminator h.inst_opcode` by
      metis_tac[ac_sim_precond_head_facts] >>
    `~MEM x h.inst_outputs` by (
      gvs[ALL_DISTINCT_APPEND] >>
      `MEM x (FLAT (MAP (\i. i.inst_outputs) insts))` by
        (simp[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
      metis_tac[]) >>
    `lookup_var x s1_o = lookup_var x s_o` by
      metis_tac[step_preserves_non_output_vars] >>
    metis_tac[MEM])) >>
  (* ALL_DISTINCT for tail *)
  (Q.SUBGOAL_THEN `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts))`
    ASSUME_TAC >- gvs[ALL_DISTINCT_APPEND]) >>
  (* Apply IH *)
  first_x_assum (drule_then (drule_then drule)) >>
  simp[] >> disch_then irule >>
  rpt strip_tac >> res_tac >>
  gvs[optionTheory.NOT_IS_SOME_EQ_NONE]
QED
