(*
 * Assert Combiner Pass — Main Proofs (Part 3b)
 *
 * Contains ac_run_insts_sim, ac_block_sim,
 * and the top-level ac_transform_function_correct_proof.
 *)

Theory assertCombinerProofs
Ancestors
  acAbortProofs acSimPrecondProofs acChainProofs acBaseProofs assertCombinerDefs
  passSimulationDefs passSimulationProps
  stateEquiv stateEquivProps execEquivProps execEquivParamProps venomInstProps venomExecProps
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


(* Safe/ASSERT/terminator trichotomy excludes INVOKE *)
Triviality safe_assert_term_no_invoke[local]:
  !insts.
    EVERY (\i. ac_is_safe_between i \/ i.inst_opcode = ASSERT \/
               is_terminator i.inst_opcode) insts ==>
    EVERY (\inst. inst.inst_opcode <> INVOKE) insts
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  spose_not_then assume_tac >> gvs[] >>
  res_tac >> gvs[ac_is_safe_between_def] >>
  pop_assum mp_tac >> EVAL_TAC
QED

(* run_insts on safe_between/ASSERT only returns OK or Abort *)
Triviality run_insts_safe_assert_only_ok_or_abort[local]:
  !insts fuel ctx s.
    EVERY (\i. ac_is_safe_between i \/ i.inst_opcode = ASSERT) insts /\
    EVERY inst_wf insts /\
    (!i op. MEM i insts /\ MEM op i.inst_operands ==>
       IS_SOME (eval_operand op s)) ==>
    (?s'. run_insts fuel ctx insts s = OK s') \/
    (?a sa. run_insts fuel ctx insts s = Abort a sa)
Proof
  Induct >> simp[run_insts_def] >>
  rpt gen_tac >> strip_tac >>
  `(?s'. step_inst fuel ctx h s = OK s') \/
   (?sa'. step_inst fuel ctx h s = Abort Revert_abort sa')` by
    (irule step_safe_or_assert_ok_or_revert >> metis_tac[]) >>
  gvs[] >> (
    first_x_assum (qspecl_then [`fuel`, `ctx`, `s'`] mp_tac) >>
    impl_tac >- (
      rpt strip_tac >>
      irule safe_assert_step_preserves_eval >>
      MAP_EVERY qexists_tac [`ctx`, `fuel`, `h`, `s`] >> simp[] >>
      metis_tac[]
    ) >>
    metis_tac[]
  )
QED

(* Wrapper: ac_sim_precond implies only OK or Abort Revert *)
Triviality ac_precond_ok_or_revert_abort[local]:
  !insts cands mp dfg fuel ctx s V.
    ac_sim_precond cands mp dfg insts s V ==>
    (?s'. run_insts fuel ctx insts s = OK s') \/
    (?sa. run_insts fuel ctx insts s = Abort Revert_abort sa)
Proof
  simp[ac_sim_precond_def] >> rpt strip_tac >>
  `(?s'. run_insts fuel ctx insts s = OK s') \/
   (?a sa. run_insts fuel ctx insts s = Abort a sa)` by
    metis_tac[run_insts_safe_assert_only_ok_or_abort] >>
  gvs[] >>
  metis_tac[run_insts_safe_assert_only_ok_or_revert]
QED

(* Combined via lift_result for ac_block_sim_same *)
Theorem ac_run_insts_sim[local]:
  !insts cands mp dfg fuel ctx s V.
    ac_sim_precond cands mp dfg insts s V /\
    (!i x. MEM i insts /\ MEM x i.inst_outputs ==>
       ~IS_SOME (lookup_var x s)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) ==>
    lift_result (state_equiv V) (execution_equiv UNIV) (execution_equiv UNIV)
      (run_insts fuel ctx insts s)
      (run_insts fuel ctx
        (SND (FOLDL (ac_apply_merge_step cands) (mp, []) insts)) s)
Proof
  rpt strip_tac >>
  `state_equiv V s s` by simp[state_equiv_refl] >>
  `(?s'. run_insts fuel ctx insts s = OK s') \/
   (?sa. run_insts fuel ctx insts s = Abort Revert_abort sa)` by
    metis_tac[ac_precond_ok_or_revert_abort] >>
  pop_assum strip_assume_tac >> rpt BasicProvers.VAR_EQ_TAC
  >- (
    drule_all ac_run_insts_sim_ok >> strip_tac >>
    simp[lift_result_def]
  )
  >- (
    drule_all ac_run_insts_sim_abort >> strip_tac >>
    simp[lift_result_def]
  )
QED

(* The FOLDL transform on (prefix ++ [terminator]) = (FOLDL on prefix) ++ [terminator]
   when the terminator is not a candidate source or target. *)
Triviality ac_foldl_snoc_term[local]:
  !cands mp acc insts term.
    ~EXISTS (\mc. mc.mc_first_id = term.inst_id) cands /\
    FIND (\mc. mc.mc_second_id = term.inst_id) cands = NONE ==>
    SND (FOLDL (ac_apply_merge_step cands) (mp, acc) (SNOC term insts)) =
    SNOC term (SND (FOLDL (ac_apply_merge_step cands) (mp, acc) insts))
Proof
  Induct_on `insts`
  >- (
    rpt strip_tac >> simp[FOLDL, SNOC] >>
    simp[ac_apply_merge_step_def, LET_THM] >>
    simp[SNOC_APPEND])
  >- (
    rpt gen_tac >> strip_tac >>
    simp[SNOC] >>
    Cases_on `ac_apply_merge_step cands (mp, acc) h` >>
    simp[] >>
    first_x_assum (qspecl_then [`cands`, `q`, `r`, `term`] mp_tac) >>
    simp[SNOC_APPEND] >>
    impl_tac >- fs[listTheory.EXISTS_NOT_EVERY] >>
    simp[])
QED

(* ===== ac_scan_block properties ===== *)
(* ac_scan_second_is_assert, ac_scan_first_is_assert, ac_scan_second_id_mem,
   ac_scan_unique_second_id, ac_cands_ordered_full are exported from acChainProofs *)

(* FIND = NONE when no element satisfies the predicate *)
Triviality FIND_NONE[local]:
  !P l. (!x. MEM x l ==> ~P x) ==> FIND P l = NONE
Proof
  Induct_on `l` >> simp[FIND_thm]
QED

(* ASSERT and terminator instructions in the same list have different IDs *)
Triviality assert_term_diff_id[local]:
  !insts a t.
    MEM a insts /\ a.inst_opcode = ASSERT /\
    MEM t insts /\ is_terminator t.inst_opcode /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) ==>
    a.inst_id <> t.inst_id
Proof
  rpt strip_tac >>
  `a <> t` by (strip_tac >> gvs[venomInstTheory.is_terminator_def]) >>
  `?n1 n2. n1 < LENGTH insts /\ EL n1 insts = a /\
           n2 < LENGTH insts /\ EL n2 insts = t` by metis_tac[MEM_EL] >>
  `n1 <> n2` by metis_tac[] >>
  metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP, EL_MAP]
QED

(* No candidate has a terminator's ID (when IDs are distinct, pending=NONE) *)
Triviality scan_no_terminator_id[local]:
  !dfg insts mc term.
    MEM mc (ac_scan_block dfg insts NONE) /\
    MEM term insts /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    is_terminator term.inst_opcode ==>
    mc.mc_first_id <> term.inst_id /\
    mc.mc_second_id <> term.inst_id
Proof
  rpt strip_tac >> gvs[]
  >- (drule ac_scan_first_is_assert >> strip_tac >> gvs[] >>
      metis_tac[assert_term_diff_id])
  >- (drule ac_scan_second_is_assert >> strip_tac >>
      metis_tac[assert_term_diff_id])
QED

(* Terminators are never candidates when IDs are distinct (pending=NONE) *)
Triviality term_not_candidate[local]:
  !insts dfg term.
    MEM term insts /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    is_terminator term.inst_opcode ==>
    ~EXISTS (\mc. mc.mc_first_id = term.inst_id)
            (ac_scan_block dfg insts NONE) /\
    FIND (\mc. mc.mc_second_id = term.inst_id)
         (ac_scan_block dfg insts NONE) = NONE
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (REWRITE_TAC[listTheory.EXISTS_MEM] >>
      metis_tac[scan_no_terminator_id])
  >- (match_mp_tac FIND_NONE >> metis_tac[scan_no_terminator_id])
QED

(* MEM in non-empty list and not LAST implies MEM in FRONT *)
Triviality mem_front_not_last[local]:
  !e l. MEM e l /\ e <> LAST l /\ l <> [] ==> MEM e (FRONT l)
Proof
  Induct_on `l` >> rw[FRONT_DEF] >>
  Cases_on `l` >> fs[FRONT_DEF] >> metis_tac[]
QED

(* Helper: FRONT elements of a well-formed block are not terminators *)
Triviality front_not_term_aux[local]:
  !bb e.
    bb_well_formed bb /\ MEM e (FRONT bb.bb_instructions) ==>
    ~is_terminator e.inst_opcode
Proof
  rpt strip_tac >>
  fs[bb_well_formed_def, MEM_EL] >>
  imp_res_tac FRONT_EL >> imp_res_tac FRONT_LENGTH >>
  gvs[] >> res_tac >> DECIDE_TAC
QED

(* Elements of FRONT are non-terminator, non-INVOKE when bb is well-formed
   and all instructions are safe_between, ASSERT, or terminators *)
Triviality front_not_terminator[local]:
  !bb e.
    bb_well_formed bb /\
    EVERY (\i. ac_is_safe_between i \/ i.inst_opcode = ASSERT \/
               is_terminator i.inst_opcode) bb.bb_instructions /\
    MEM e (FRONT bb.bb_instructions) ==>
    (ac_is_safe_between e \/ e.inst_opcode = ASSERT) /\
    ~is_terminator e.inst_opcode /\ e.inst_opcode <> INVOKE
Proof
  rpt gen_tac >> strip_tac >>
  drule_all front_not_term_aux >> strip_tac >> simp[] >>
  `MEM e bb.bb_instructions` by
    (fs[bb_well_formed_def] >> metis_tac[MEM_FRONT_NOT_NIL]) >>
  `ac_is_safe_between e \/ e.inst_opcode = ASSERT` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  simp[] >>
  fs[ac_is_safe_between_def] >>
  spose_not_then ASSUME_TAC >>
  gvs[venomEffectsTheory.write_effects_def,
      venomEffectsTheory.all_effects_def]
QED

(* Fresh vars from scan candidates are in V *)
Triviality ac_fresh_vars_in_V[local]:
  !dfg bb mc V.
    MEM mc (ac_scan_block dfg bb.bb_instructions NONE) /\
    ac_fresh_vars_block dfg bb SUBSET V ==>
    ac_or_var mc.mc_second_id IN V /\
    ac_iz_var mc.mc_second_id IN V
Proof
  rpt strip_tac >>
  fs[assertCombinerDefsTheory.ac_fresh_vars_block_def, LET_THM,
     SUBSET_DEF, MEM_FLAT, MEM_MAP] >>
  first_x_assum irule >>
  qexists_tac `[ac_or_var mc.mc_second_id; ac_iz_var mc.mc_second_id]` >>
  simp[MEM_MAP] >> metis_tac[]
QED

(* Scan pred operands are evaluable given DFG invariant and all operands evaluable *)
Triviality ac_scan_pred_evaluable[local]:
  !dfg bb mc s.
    MEM mc (ac_scan_block dfg bb.bb_instructions NONE) /\
    ac_dfg_inv dfg s /\
    (!inst op. MEM inst bb.bb_instructions /\ MEM op inst.inst_operands ==>
       IS_SOME (eval_operand op s)) /\
    (!i mc'. MEM i bb.bb_instructions /\
       MEM mc' (ac_scan_block dfg bb.bb_instructions NONE) /\
       mc'.mc_second_id = i.inst_id ==>
       ?v. i.inst_operands = [Var v] /\
           ac_get_iszero_operand dfg {} (Var v) = SOME mc'.mc_second_pred) /\
    (!i mc'. MEM i bb.bb_instructions /\
       MEM mc' (ac_scan_block dfg bb.bb_instructions NONE) /\
       mc'.mc_first_id = i.inst_id ==>
       ?v. i.inst_operands = [Var v] /\
           ac_get_iszero_operand dfg {} (Var v) = SOME mc'.mc_first_pred) ==>
    IS_SOME (eval_operand mc.mc_second_pred s) /\
    IS_SOME (eval_operand mc.mc_first_pred s)
Proof
  rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac ac_scan_second_id_mem >>
  conj_tac
  >- (
    res_tac >> gvs[] >>
    Q.SUBGOAL_THEN `IS_SOME (eval_operand (Var v) s)` ASSUME_TAC
    >- (first_x_assum irule >> simp[]) >>
    drule_all ac_dfg_iszero_bridge >> strip_tac >> simp[]
  )
  >- (
    drule_then strip_assume_tac ac_scan_first_is_assert >> gvs[] >>
    first_x_assum (qspecl_then [`inst`, `mc`] mp_tac) >>
    (impl_tac >- gvs[]) >> strip_tac >> gvs[] >>
    (Q.SUBGOAL_THEN `IS_SOME (eval_operand (Var v) s)` mp_tac
     >- (first_x_assum (qspecl_then [`inst`, `Var v`] mp_tac) >> simp[])) >>
    strip_tac >>
    drule_all ac_dfg_iszero_bridge >> strip_tac >> simp[]
  )
QED

(* Output/pred clash follows from no_redefine + pred evaluability.
   If pred = Var x and IS_SOME (eval_operand pred s), then IS_SOME (lookup_var x s).
   But no_redefine says MEM x i.inst_outputs ==> ~IS_SOME (lookup_var x s).
   Contradiction. *)
Triviality ac_scan_output_pred_clash[local]:
  !dfg bb mc i x s.
    MEM mc (ac_scan_block dfg bb.bb_instructions NONE) /\
    MEM i bb.bb_instructions /\ MEM x i.inst_outputs /\
    (mc.mc_second_pred = Var x \/ mc.mc_first_pred = Var x) /\
    ac_dfg_inv dfg s /\
    (!inst op. MEM inst bb.bb_instructions /\ MEM op inst.inst_operands ==>
       IS_SOME (eval_operand op s)) /\
    (!inst mc'. MEM inst bb.bb_instructions /\
       MEM mc' (ac_scan_block dfg bb.bb_instructions NONE) /\
       mc'.mc_second_id = inst.inst_id ==>
       ?v. inst.inst_operands = [Var v] /\
           ac_get_iszero_operand dfg {} (Var v) = SOME mc'.mc_second_pred) /\
    (!inst mc'. MEM inst bb.bb_instructions /\
       MEM mc' (ac_scan_block dfg bb.bb_instructions NONE) /\
       mc'.mc_first_id = inst.inst_id ==>
       ?v. inst.inst_operands = [Var v] /\
           ac_get_iszero_operand dfg {} (Var v) = SOME mc'.mc_first_pred) /\
    (!inst y. MEM inst bb.bb_instructions /\ MEM y inst.inst_outputs ==>
       ~IS_SOME (lookup_var y s)) ==>
    F
Proof
  rpt gen_tac >> strip_tac >>
  (* Get pred evaluability *)
  drule_all ac_scan_pred_evaluable >> strip_tac >>
  (* pred = Var x, so IS_SOME (lookup_var x s) *)
  gvs[eval_operand_def] >>
  (* no_redefine gives lookup_var x s = NONE, contradicting IS_SOME *)
  res_tac >> gvs[]
QED

(* FRONT preserves ALL_DISTINCT MAP *)
Triviality all_distinct_map_front[local]:
  !(l:'a list) f. ALL_DISTINCT (MAP f l) /\ l <> [] ==>
    ALL_DISTINCT (MAP f (FRONT l))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `l` >> gvs[FRONT_DEF] >>
  fs[ALL_DISTINCT, MAP, MEM_MAP] >>
  Cases_on `t = []` >> gvs[] >>
  metis_tac[MEM_FRONT_NOT_NIL]
QED

(* Scan candidate second_ids index into FRONT (non-terminator) *)
Triviality ac_scan_idx_in_front[local]:
  !dfg bb mc idx.
    MEM mc (ac_scan_block dfg bb.bb_instructions NONE) /\
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    idx < LENGTH bb.bb_instructions /\
    (EL idx bb.bb_instructions).inst_id = mc.mc_second_id ==>
    idx < LENGTH (FRONT bb.bb_instructions)
Proof
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  (Q.SUBGOAL_THEN `bb.bb_instructions <> []` ASSUME_TAC
   >- fs[bb_well_formed_def]) >>
  (Q.SUBGOAL_THEN `idx = PRE (LENGTH bb.bb_instructions)` ASSUME_TAC
   >- fs[LENGTH_FRONT]) >>
  drule_then strip_assume_tac ac_scan_second_is_assert >>
  gvs[MEM_EL] >>
  (* n' is idx of ASSERT inst, PRE(LENGTH) is last position *)
  (* Both map to the same inst_id (= mc.mc_second_id) *)
  (* ALL_DISTINCT_EL_IMP on MAP (\i. i.inst_id) bb => n' = PRE(LENGTH) *)
  qpat_x_assum `ALL_DISTINCT _`
    (mp_tac o REWRITE_RULE[EL_ALL_DISTINCT_EL_EQ, EL_MAP, LENGTH_MAP]) >>
  disch_then (qspecl_then [`n'`, `PRE (LENGTH bb.bb_instructions)`] mp_tac) >>
  simp[EL_MAP] >> strip_tac >>
  gvs[bb_well_formed_def, GSYM LAST_EL, venomInstTheory.is_terminator_def]
QED

(* ac_cands_ordered for FRONT of well-formed block *)
Triviality ac_cands_ordered_front[local]:
  !dfg bb.
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    bb_well_formed bb ==>
    ac_cands_ordered (ac_scan_block dfg bb.bb_instructions NONE)
                     (FRONT bb.bb_instructions)
Proof
  rpt strip_tac >>
  (Q.SUBGOAL_THEN `bb.bb_instructions <> []` ASSUME_TAC
   >- fs[bb_well_formed_def]) >>
  irule ac_cands_ordered_full >> reverse conj_tac
  >- (irule all_distinct_map_front >> fs[bb_well_formed_def])
  >>
  rpt strip_tac >>
  drule_all ac_scan_block_ordered_indices >> strip_tac >>
  qexists_tac `idx_f` >> qexists_tac `idx_s` >>
  (Q.SUBGOAL_THEN `idx_s < LENGTH (FRONT bb.bb_instructions)` ASSUME_TAC
   >- metis_tac[ac_scan_idx_in_front]) >>
  (Q.SUBGOAL_THEN `idx_f < LENGTH (FRONT bb.bb_instructions)` ASSUME_TAC
   >- simp[]) >>
  simp[EL_FRONT, NULL_EQ]
QED

(* ALL_DISTINCT (MAP f l) implies f is injective on l *)
Triviality all_distinct_map_mem_eq[local]:
  !f (l:'a list) x y.
    ALL_DISTINCT (MAP f l) /\ MEM x l /\ MEM y l /\ f x = f y ==> x = y
Proof
  rpt strip_tac >> fs[MEM_EL] >> gvs[] >>
  qpat_x_assum `ALL_DISTINCT _`
    (mp_tac o REWRITE_RULE[EL_ALL_DISTINCT_EL_EQ, EL_MAP, LENGTH_MAP]) >>
  disch_then (qspecl_then [`n`, `n'`] mp_tac) >> simp[EL_MAP]
QED

(* Under SSA, no instruction can use a variable it also defines.
   Proof: def_dominates_uses gives a definer that strictly precedes
   the user within the same block, but both have x in outputs,
   contradicting ALL_DISTINCT on the global output list. *)
Triviality all_distinct_flat_map_unique[local]:
  !ls f (i1:'a) (i2:'a) (x:'b).
    ALL_DISTINCT (FLAT (MAP f ls)) /\
    MEM i1 ls /\ MEM x (f i1) /\
    MEM i2 ls /\ MEM x (f i2) ==>
    i1 = i2
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

Triviality mem_fn_insts[local]:
  !bbs bb i. MEM bb bbs /\ MEM i bb.bb_instructions ==>
    MEM i (fn_insts_blocks bbs)
Proof
  Induct >> simp[venomInstTheory.fn_insts_blocks_def] >> metis_tac[]
QED

Triviality mem_fn_insts_rev[local]:
  !bbs i. MEM i (fn_insts_blocks bbs) ==>
    ?bb. MEM bb bbs /\ MEM i bb.bb_instructions
Proof
  Induct >> simp[venomInstTheory.fn_insts_blocks_def] >> metis_tac[]
QED

(* Combine dfg_build_function_correct + fn_insts_def + mem_fn_insts_rev *)
Triviality dfg_def_in_fn_blocks[local]:
  !fn v inst.
    dfg_get_def (dfg_build_function fn) v = SOME inst ==>
    MEM v inst.inst_outputs /\
    ?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions
Proof
  rpt strip_tac >> imp_res_tac dfg_build_function_correct >>
  fs[venomInstTheory.fn_insts_def] >> metis_tac[mem_fn_insts_rev]
QED

(* fn_inst_ids_distinct gives per-block ALL_DISTINCT on inst_ids *)
Triviality fn_inst_ids_block_distinct[local]:
  !fn bb. fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  simp[venomWfTheory.fn_inst_ids_distinct_def] >>
  rpt strip_tac >>
  ntac 2 (pop_assum mp_tac) >>
  qspec_tac (`fn.fn_blocks`, `bbs`) >>
  Induct >> simp[] >>
  rpt strip_tac >> gvs[ALL_DISTINCT_APPEND, MAP_APPEND, FLAT_APPEND]
QED

Triviality ssa_no_self_reference[local]:
  !fn bb i x.
    wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
    MEM i bb.bb_instructions /\ MEM x i.inst_outputs /\
    MEM (Var x) i.inst_operands ==> F
Proof
  rpt strip_tac >>
  fs[wf_ssa_def] >>
  (* From def_dominates_uses: get def_inst with x in outputs and strict ordering *)
  `?def_bb def_inst.
     MEM def_bb fn.fn_blocks /\ MEM def_inst def_bb.bb_instructions /\
     MEM x def_inst.inst_outputs /\
     fn_dominates fn def_bb.bb_label bb.bb_label /\
     (def_bb = bb ==>
        ?di dj. di < dj /\ dj < LENGTH bb.bb_instructions /\
                EL di bb.bb_instructions = def_inst /\
                EL dj bb.bb_instructions = i)` by
    (fs[def_dominates_uses_def] >> metis_tac[]) >>
  (* Both i and def_inst are in fn_insts fn and have x in outputs.
     By all_distinct_flat_map_unique on fn_insts fn: def_inst = i *)
  (Q.SUBGOAL_THEN
    `ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) (fn_insts fn)))`
    ASSUME_TAC >- fs[ssa_form_def]) >>
  (Q.SUBGOAL_THEN `MEM def_inst (fn_insts fn)` ASSUME_TAC >- (
    simp[venomInstTheory.fn_insts_def] >> metis_tac[mem_fn_insts])) >>
  (Q.SUBGOAL_THEN `MEM i (fn_insts fn)` ASSUME_TAC >- (
    simp[venomInstTheory.fn_insts_def] >> metis_tac[mem_fn_insts])) >>
  (Q.SUBGOAL_THEN `def_inst = i` ASSUME_TAC >- (
    metis_tac[all_distinct_flat_map_unique])) >>
  gvs[] >>
  (* Now def_bb = bb *)
  (* def_bb = bb because def_inst appears in both, contradicting fn_inst_ids_distinct *)
  (Q.SUBGOAL_THEN
    `ALL_DISTINCT (FLAT (MAP (\bb. MAP (\inst. inst.inst_id) bb.bb_instructions) fn.fn_blocks))`
    ASSUME_TAC >- fs[wf_function_def, fn_inst_ids_distinct_def]) >>
  (Q.SUBGOAL_THEN `MEM def_inst.inst_id (MAP (\inst. inst.inst_id) def_bb.bb_instructions)`
    ASSUME_TAC >- (simp[MEM_MAP] >> metis_tac[])) >>
  (Q.SUBGOAL_THEN `MEM def_inst.inst_id (MAP (\inst. inst.inst_id) bb.bb_instructions)`
    ASSUME_TAC >- (simp[MEM_MAP] >> metis_tac[])) >>
  (Q.SUBGOAL_THEN `def_bb = bb` ASSUME_TAC >- (
    mp_tac (ISPECL [``fn.fn_blocks``,
      ``\blk:basic_block. MAP (\i:instruction. i.inst_id) blk.bb_instructions``,
      ``def_bb:basic_block``, ``bb:basic_block``, ``def_inst.inst_id``]
      all_distinct_flat_map_unique) >>
    simp[BETA_THM])) >>
  gvs[] >>
  (* Now di < dj with EL di = EL dj = def_inst in same block, contra ALL_DISTINCT inst_ids *)
  (Q.SUBGOAL_THEN `ALL_DISTINCT (MAP (\inst. inst.inst_id) bb.bb_instructions)`
    ASSUME_TAC >- metis_tac[fn_inst_ids_block_distinct, wf_function_def]) >>
  res_tac >>
  (* di < dj but EL di = EL dj, contradicting ALL_DISTINCT on inst_ids *)
  (Q.SUBGOAL_THEN `EL di (MAP (\inst. inst.inst_id) bb.bb_instructions) =
   EL dj (MAP (\inst. inst.inst_id) bb.bb_instructions)` ASSUME_TAC >-
    simp[EL_MAP]) >>
  metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP, LESS_TRANS, prim_recTheory.LESS_REFL]
QED

(* ac_get_iszero_operand only succeeds on Var operands *)
Triviality ac_get_iszero_operand_is_var[local]:
  !dfg visited op pred.
    ac_get_iszero_operand dfg visited op = SOME pred ==>
    ?v. op = Var v
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[Once assertCombinerDefsTheory.ac_get_iszero_operand_def]
QED

(* Scan structural: mc_second has ISZERO operand chain *)
Triviality ac_scan_second_iszero_chain[local]:
  !dfg insts pending mc.
    MEM mc (ac_scan_block dfg insts pending) ==>
    ?inst op. MEM inst insts /\ inst.inst_id = mc.mc_second_id /\
              inst.inst_operands = [op] /\
              ac_get_iszero_operand dfg {} op = SOME mc.mc_second_pred
Proof
  Induct_on `insts` >> rw[ac_scan_block_def] >>
  BasicProvers.every_case_tac >> gvs[] >> res_tac >> gvs[] >>
  metis_tac[]
QED

(* Scan structural: mc_first has ISZERO operand chain (or comes from pending) *)
Triviality ac_scan_first_iszero_chain[local]:
  !dfg insts pending mc.
    MEM mc (ac_scan_block dfg insts pending) ==>
    (?inst op. MEM inst insts /\ inst.inst_id = mc.mc_first_id /\
               inst.inst_operands = [op] /\
               ac_get_iszero_operand dfg {} op = SOME mc.mc_first_pred) \/
    (pending = SOME (mc.mc_first_id, mc.mc_first_pred))
Proof
  Induct_on `insts` >> rw[ac_scan_block_def] >>
  BasicProvers.every_case_tac >> gvs[] >> res_tac >> gvs[] >>
  metis_tac[]
QED

(* ac_get_iszero_operand result is an operand of some DFG instruction *)
Triviality ac_get_iszero_operand_dfg_mem[local]:
  !dfg visited op pred.
    ac_get_iszero_operand dfg visited op = SOME pred ==>
    ?v di. dfg_get_def dfg v = SOME di /\ MEM pred di.inst_operands
Proof
  recInduct assertCombinerDefsTheory.ac_get_iszero_operand_ind >>
  rpt strip_tac >>
  pop_assum mp_tac >>
  simp[Once assertCombinerDefsTheory.ac_get_iszero_operand_def] >>
  BasicProvers.every_case_tac >> gvs[] >> rpt strip_tac >> gvs[] >>
  metis_tac[MEM]
QED

(* Combined: scan pred (second) is operand of some inst in fn_blocks *)
Triviality ac_scan_second_pred_in_fn[local]:
  !fn bb mc.
    MEM mc (ac_scan_block (dfg_build_function fn) bb.bb_instructions NONE) ==>
    ?di bb'. MEM bb' fn.fn_blocks /\ MEM di bb'.bb_instructions /\
             MEM mc.mc_second_pred di.inst_operands
Proof
  rpt strip_tac >>
  imp_res_tac ac_scan_second_iszero_chain >>
  imp_res_tac ac_get_iszero_operand_dfg_mem >>
  imp_res_tac dfg_def_in_fn_blocks >> metis_tac[]
QED

(* Combined: scan pred (first, pending=NONE) is operand of some inst in fn_blocks *)
Triviality ac_scan_first_pred_in_fn[local]:
  !fn bb mc.
    MEM mc (ac_scan_block (dfg_build_function fn) bb.bb_instructions NONE) ==>
    ?di bb'. MEM bb' fn.fn_blocks /\ MEM di bb'.bb_instructions /\
             MEM mc.mc_first_pred di.inst_operands
Proof
  rpt strip_tac >>
  imp_res_tac ac_scan_first_iszero_chain >>
  gvs[ac_scan_block_def] >>
  imp_res_tac ac_get_iszero_operand_dfg_mem >>
  imp_res_tac dfg_def_in_fn_blocks >> metis_tac[]
QED

(* ac_or_var/ac_iz_var from scan entries are in fresh_vars_fn *)
Triviality ac_scan_fresh_in_fn[local]:
  !fn bb mc.
    MEM bb fn.fn_blocks /\
    MEM mc (ac_scan_block (dfg_build_function fn) bb.bb_instructions NONE) ==>
    ac_or_var mc.mc_second_id IN ac_fresh_vars_fn fn /\
    ac_iz_var mc.mc_second_id IN ac_fresh_vars_fn fn
Proof
  rpt strip_tac >> gvs[] >>
  simp[assertCombinerDefsTheory.ac_fresh_vars_fn_def, LET_THM,
       IN_BIGUNION, MEM_MAP,
       assertCombinerDefsTheory.ac_fresh_vars_block_def] >>
  qexists_tac `ac_fresh_vars_block (dfg_build_function fn) bb` >>
  simp[assertCombinerDefsTheory.ac_fresh_vars_block_def, LET_THM,
       MEM_FLAT, MEM_MAP] >>
  rpt conj_tac >> TRY (metis_tac[]) >>
  qexists_tac `[ac_or_var mc.mc_second_id; ac_iz_var mc.mc_second_id]` >>
  simp[] >> metis_tac[]
QED

(* Scan: first_id comes from insts or pending *)
Triviality ac_scan_first_id_source[local]:
  !dfg insts pending mc.
    MEM mc (ac_scan_block dfg insts pending) ==>
    (?i. MEM i insts /\ i.inst_id = mc.mc_first_id) \/
    (?pred. pending = SOME (mc.mc_first_id, pred))
Proof
  Induct_on `insts` >> rw[ac_scan_block_def] >>
  BasicProvers.every_case_tac >> gvs[] >> res_tac >> gvs[] >>
  metis_tac[]
QED

(* Scan chaining: when two candidates share an id (mc1.second = mc2.first),
   the preds must agree. Specialized to pending = NONE (initial scan call).
   Proof: both preds come from ac_get_iszero_operand on the same instruction
   (by ALL_DISTINCT inst_ids), so they're equal. *)
Triviality ac_scan_chaining[local]:
  !dfg insts mc1 mc2.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    MEM mc1 (ac_scan_block dfg insts NONE) /\
    MEM mc2 (ac_scan_block dfg insts NONE) /\
    mc1.mc_second_id = mc2.mc_first_id ==>
    mc1.mc_second_pred = mc2.mc_first_pred
Proof
  rpt strip_tac >>
  (* mc1.mc_second_pred: from ac_scan_second_iszero_chain applied to mc1 *)
  qpat_x_assum `MEM mc1 _`
    (strip_assume_tac o MATCH_MP ac_scan_second_iszero_chain) >>
  rename1 `MEM i1 insts` >> rename1 `i1.inst_operands = [op1]` >>
  rename1 `ac_get_iszero_operand _ _ op1 = SOME mc1.mc_second_pred` >>
  (* mc2.mc_first_pred: from ac_scan_first_iszero_chain applied to mc2 *)
  qpat_x_assum `MEM mc2 _`
    (strip_assume_tac o MATCH_MP ac_scan_first_iszero_chain) >>
  gvs[] (* eliminates NONE = SOME disjunct *) >>
  rename1 `MEM i2 insts` >> rename1 `i2.inst_operands = [op2]` >>
  rename1 `ac_get_iszero_operand _ _ op2 = SOME mc2.mc_first_pred` >>
  (* i1.inst_id = i2.inst_id = mc2.mc_first_id, ALL_DISTINCT ⇒ i1 = i2 *)
  mp_tac (SIMP_RULE (srw_ss()) []
           (ISPECL [``\i:instruction. i.inst_id``]
                   all_distinct_map_mem_eq)) >>
  disch_then (qspecl_then [`insts`, `i1`, `i2`] mp_tac) >>
  simp[] >> strip_tac >> gvs[]
QED

(* Establish ac_sim_precond from block-level + DFG/scan structural assumptions.
   The DFG/scan assumptions are discharged at ac_block_sim level from
   dfg = dfg_build_function fn + wf_ssa fn. *)
Triviality ac_block_establishes_precond[local]:
  !dfg bb s V.
    ac_dfg_inv dfg s /\
    EVERY inst_wf bb.bb_instructions /\
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    EVERY (\i. ac_is_safe_between i \/ i.inst_opcode = ASSERT \/
               is_terminator i.inst_opcode) bb.bb_instructions /\
    ac_fresh_vars_block dfg bb SUBSET V /\
    (!inst x. MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       x NOTIN V) /\
    (!inst x. MEM inst bb.bb_instructions /\ MEM x inst.inst_outputs ==>
       x NOTIN V) /\
    (!inst op. MEM inst bb.bb_instructions /\ MEM op inst.inst_operands ==>
       IS_SOME (eval_operand op s)) /\
    ac_scan_block dfg bb.bb_instructions NONE <> [] /\
    (* DFG structural: dfg maps output vars to defining instructions *)
    (!i v. MEM i bb.bb_instructions /\ MEM v i.inst_outputs /\
       dfg_get_def dfg v <> NONE ==> dfg_get_def dfg v = SOME i) /\
    (* No self-reference: no instruction uses a variable it defines *)
    (!i x. MEM i bb.bb_instructions /\ MEM x i.inst_outputs /\
       MEM (Var x) i.inst_operands ==> F) /\
    (* Fresh vars not in DFG *)
    (!v. v IN V ==> dfg_get_def dfg v = NONE) /\
    (* DFG operand vars not fresh *)
    (!di x v. dfg_get_def dfg x = SOME di /\
       MEM (Var v) di.inst_operands ==> v NOTIN V) /\
    (* Scan structural: DFG-ISZERO chain for second *)
    (!i mc. MEM i bb.bb_instructions /\
       MEM mc (ac_scan_block dfg bb.bb_instructions NONE) /\
       mc.mc_second_id = i.inst_id ==>
       ?v. i.inst_operands = [Var v] /\
           ac_get_iszero_operand dfg {} (Var v) = SOME mc.mc_second_pred) /\
    (* Scan structural: DFG-ISZERO chain for first *)
    (!i mc. MEM i bb.bb_instructions /\
       MEM mc (ac_scan_block dfg bb.bb_instructions NONE) /\
       mc.mc_first_id = i.inst_id ==>
       ?v. i.inst_operands = [Var v] /\
           ac_get_iszero_operand dfg {} (Var v) = SOME mc.mc_first_pred) /\
    (* Scan structural: chaining *)
    (!mc1 mc2. MEM mc1 (ac_scan_block dfg bb.bb_instructions NONE) /\
       MEM mc2 (ac_scan_block dfg bb.bb_instructions NONE) /\
       mc1.mc_second_id = mc2.mc_first_id ==>
       mc1.mc_second_pred = mc2.mc_first_pred) /\
    (* Cross-candidate pred disjointness from fresh vars *)
    (!mc mc' x. MEM mc (ac_scan_block dfg bb.bb_instructions NONE) /\
       MEM mc' (ac_scan_block dfg bb.bb_instructions NONE) /\
       (mc.mc_second_pred = Var x \/ mc.mc_first_pred = Var x) ==>
       x <> ac_or_var mc'.mc_second_id /\ x <> ac_iz_var mc'.mc_second_id) /\
    (* No-redefine: instruction outputs are undefined in the initial state *)
    (!i x. MEM i bb.bb_instructions /\ MEM x i.inst_outputs ==>
       ~IS_SOME (lookup_var x s)) /\
    (* Processed first_ids: vacuous when first_id always in bb *)
    (!mc. MEM mc (ac_scan_block dfg bb.bb_instructions NONE) /\
       (!i. MEM i (FRONT bb.bb_instructions) ==> i.inst_id <> mc.mc_first_id) ==>
       eval_operand mc.mc_first_pred s = SOME 0w) ==>
    ac_sim_precond
      (ac_scan_block dfg bb.bb_instructions NONE)
      [] dfg (FRONT bb.bb_instructions) s V
Proof
  rpt strip_tac >>
  (Q.SUBGOAL_THEN `bb.bb_instructions <> []` ASSUME_TAC
   >- fs[bb_well_formed_def]) >>
  rw[ac_sim_precond_def] >> rpt strip_tac >>
  (* Most conjuncts lift from bb to FRONT via MEM_FRONT_NOT_NIL *)
  TRY (metis_tac[MEM_FRONT_NOT_NIL]) >>
  (* ALOOKUP [] = vacuous *)
  TRY (fs[] >> NO_TAC) >>
  (* EVERY on FRONT from block-level EVERY *)
  TRY (simp[EVERY_MEM] >> metis_tac[front_not_terminator] >> NO_TAC) >>
  (* ac_or/iz_var ∈ V from ac_fresh_vars_block ⊆ V *)
  TRY (fs[assertCombinerDefsTheory.ac_fresh_vars_block_def, LET_THM,
          SUBSET_DEF, MEM_FLAT, MEM_MAP] >>
       first_x_assum irule >>
       qexists_tac `[ac_or_var mc.mc_second_id; ac_iz_var mc.mc_second_id]` >>
       simp[MEM_MAP] >> metis_tac[] >> NO_TAC) >>
  (* ALL_DISTINCT second_ids *)
  TRY (irule ac_scan_unique_second_id >> simp[] >> NO_TAC) >>
  (* Remaining EVERY/fresh/pred goals *)
  TRY (fs[EVERY_MEM] >> metis_tac[MEM_FRONT_NOT_NIL] >> NO_TAC) >>
  TRY (drule_all ac_scan_pred_evaluable >> simp[] >> NO_TAC) >>
  TRY (gvs[] >> imp_res_tac ac_fresh_vars_in_V >>
       metis_tac[MEM_FRONT_NOT_NIL] >> NO_TAC) >>
  (* FIND/EXISTS second/first_id = ASSERT: via scan lemma + ALL_DISTINCT *)
  TRY (imp_res_tac FIND_MEM >> imp_res_tac FIND_P >>
       imp_res_tac ac_scan_second_is_assert >> gvs[] >>
       metis_tac[MEM_FRONT_NOT_NIL, all_distinct_map_mem_eq]) >>
  TRY (gvs[listTheory.EXISTS_MEM] >>
       imp_res_tac ac_scan_first_is_assert >> gvs[] >>
       metis_tac[MEM_FRONT_NOT_NIL, all_distinct_map_mem_eq])
  (* Remaining: ac_cands_ordered + output/pred clash *)
  >- metis_tac[ac_cands_ordered_front]
  >- (CCONTR_TAC >> gvs[DE_MORGAN_THM] >>
      (Q.SUBGOAL_THEN `MEM i bb.bb_instructions` ASSUME_TAC
       >- metis_tac[MEM_FRONT_NOT_NIL]) >>
      mp_tac (Q.SPECL [`dfg`, `bb`, `mc`, `i`, `x`, `s`]
                ac_scan_output_pred_clash) >>
      simp[] >> metis_tac[])
QED

(* Bridge: run_insts prefix simulation implies run_block simulation
   when both blocks share the same terminator and start from the same state *)
Triviality front_el_eq[local]:
  !(bb:'a list). bb <> [] ==>
    !k. k < LENGTH (FRONT bb) ==> EL (0 + k) bb = EL k (FRONT bb)
Proof
  rpt strip_tac >> simp[] >> metis_tac[EL_FRONT, NULL_EQ]
QED

Triviality run_insts_front_sim_run_block_fail[local]:
  !fuel ctx bb1 bb2 s V.
    bb1.bb_instructions <> [] /\ bb2.bb_instructions <> [] /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
          (FRONT bb1.bb_instructions) /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
          (FRONT bb2.bb_instructions) /\
    s.vs_inst_idx = 0 /\
    ~(?s1'. run_insts fuel ctx (FRONT bb1.bb_instructions) s = OK s1') /\
    lift_result (state_equiv V) (execution_equiv UNIV) (execution_equiv UNIV)
      (run_insts fuel ctx (FRONT bb1.bb_instructions) s)
      (run_insts fuel ctx (FRONT bb2.bb_instructions) s)
  ==>
    lift_result (state_equiv V) (execution_equiv UNIV) (execution_equiv UNIV)
      (run_block fuel ctx bb1 s)
      (run_block fuel ctx bb2 s)
Proof
  rpt strip_tac >>
  Q.SUBGOAL_THEN `s with vs_inst_idx := 0 = s` ASSUME_TAC
  >- simp[venom_state_component_equality] >>
  Q.SUBGOAL_THEN `~(?s2'. run_insts fuel ctx (FRONT bb2.bb_instructions) s = OK s2')` ASSUME_TAC
  >- (strip_tac >>
      Cases_on `run_insts fuel ctx (FRONT bb1.bb_instructions) s` >>
      gvs[lift_result_def]) >>
  (* Chain: run_block bb1 ~ run_insts FRONT bb1 ~ run_insts FRONT bb2 ~ run_block bb2 *)
  mp_tac (Q.SPECL [`state_equiv V`, `execution_equiv UNIV`,
                    `FRONT bb1.bb_instructions`] run_block_prefix_fail_lift) >>
  simp[valid_state_rel_UNIV] >>
  disch_then (qspecl_then [`fuel`, `ctx`, `bb1`, `s`, `0`] mp_tac) >>
  simp[LENGTH_FRONT] >>
  (impl_tac >- (conj_tac
    >- (rpt strip_tac >> irule (GSYM EL_FRONT) >> simp[NULL_EQ, LENGTH_FRONT])
    >- gvs[])) >> strip_tac >>
  mp_tac (Q.SPECL [`state_equiv V`, `execution_equiv UNIV`,
                    `FRONT bb2.bb_instructions`] run_insts_lift_run_block) >>
  simp[valid_state_rel_UNIV] >>
  disch_then (qspecl_then [`fuel`, `ctx`, `bb2`, `s`, `0`] mp_tac) >>
  simp[LENGTH_FRONT] >>
  (impl_tac >- (conj_tac
    >- (rpt strip_tac >> irule (GSYM EL_FRONT) >> simp[NULL_EQ, LENGTH_FRONT])
    >- gvs[])) >> strip_tac >>
  irule (REWRITE_RULE [AND_IMP_INTRO] lift_result_trans) >>
  rpt conj_tac
  >- metis_tac[state_equiv_trans]
  >- metis_tac[execution_equiv_trans]
  >- (qexists_tac `run_insts fuel ctx (FRONT bb1.bb_instructions) s` >>
      conj_tac
      >- first_assum ACCEPT_TAC
      >- (irule (REWRITE_RULE [AND_IMP_INTRO] lift_result_trans) >>
          rpt conj_tac
          >- metis_tac[state_equiv_trans]
          >- metis_tac[execution_equiv_trans]
          >- (qexists_tac `run_insts fuel ctx (FRONT bb2.bb_instructions) s` >>
              metis_tac[])))
QED

(* Terminator step on different-idx states preserves lift_result through halted_wrap *)
Triviality terminator_halted_wrap_lift_result[local]:
  !inst s1 s2 n1 n2 V.
    is_terminator inst.inst_opcode /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    state_equiv V s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN V) ==>
    lift_result (state_equiv V) (execution_equiv UNIV) (execution_equiv UNIV)
      (case step_inst_base inst (s1 with vs_inst_idx := n1) of
         OK s => if s.vs_halted then Halt s else OK s
       | Halt s => Halt s | Abort a s => Abort a s
       | IntRet l s => IntRet l s | Error e => Error e)
      (case step_inst_base inst (s2 with vs_inst_idx := n2) of
         OK s => if s.vs_halted then Halt s else OK s
       | Halt s => Halt s | Abort a s => Abort a s
       | IntRet l s => IntRet l s | Error e => Error e)
Proof
  rpt strip_tac >>
  Q.SUBGOAL_THEN `result_equiv V (step_inst_base inst s1) (step_inst_base inst s2)`
    ASSUME_TAC
  >- (irule step_inst_base_result_equiv >> simp[] >> metis_tac[]) >>
  fs[result_equiv_is_lift_result] >>
  mp_tac (Q.SPECL [`inst`, `s1`, `n1`]
    instIdxIndepTheory.terminator_step_inst_base_idx_norm0) >>
  mp_tac (Q.SPECL [`inst`, `s2`, `n2`]
    instIdxIndepTheory.terminator_step_inst_base_idx_norm0) >>
  Q.SUBGOAL_THEN `s1 with vs_inst_idx := 0 = s1` (fn th => REWRITE_TAC[th])
  >- simp[venom_state_component_equality] >>
  Q.SUBGOAL_THEN `s2 with vs_inst_idx := 0 = s2` (fn th => REWRITE_TAC[th])
  >- simp[venom_state_component_equality] >>
  ntac 2 strip_tac >>
  Cases_on `step_inst_base inst s1` >>
  Cases_on `step_inst_base inst s2` >>
  Cases_on `step_inst_base inst (s1 with vs_inst_idx := n1)` >>
  Cases_on `step_inst_base inst (s2 with vs_inst_idx := n2)` >>
  gvs[instIdxIndepTheory.exec_result_map_def, lift_result_def] >>
  imp_res_tac instIdxIndepTheory.terminator_OK_inst_idx_0 >>
  gvs[venom_state_component_equality] >>
  Cases_on `v'.vs_halted` >>
  fs[lift_result_def, state_equiv_def, execution_equiv_def] >>
  rpt strip_tac >> fs[lookup_var_def]
QED

Triviality run_insts_front_sim_run_block_ok[local]:
  !fuel ctx bb1 bb2 s s1' s2' V.
    bb1.bb_instructions <> [] /\ bb2.bb_instructions <> [] /\
    LAST bb1.bb_instructions = LAST bb2.bb_instructions /\
    is_terminator (LAST bb1.bb_instructions).inst_opcode /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
          (FRONT bb1.bb_instructions) /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
          (FRONT bb2.bb_instructions) /\
    s.vs_inst_idx = 0 /\
    run_insts fuel ctx (FRONT bb1.bb_instructions) s = OK s1' /\
    run_insts fuel ctx (FRONT bb2.bb_instructions) s = OK s2' /\
    state_equiv V s1' s2' /\
    (!x. MEM (Var x) (LAST bb1.bb_instructions).inst_operands ==> x NOTIN V)
  ==>
    lift_result (state_equiv V) (execution_equiv UNIV) (execution_equiv UNIV)
      (run_block fuel ctx bb1 s)
      (run_block fuel ctx bb2 s)
Proof
  rpt strip_tac >>
  Q.SUBGOAL_THEN `s with vs_inst_idx := 0 = s` ASSUME_TAC
  >- simp[venom_state_component_equality] >>
  Q.SUBGOAL_THEN `s1'.vs_inst_idx = 0` ASSUME_TAC
  >- metis_tac[run_insts_preserves_idx] >>
  Q.SUBGOAL_THEN `s2'.vs_inst_idx = 0` ASSUME_TAC
  >- metis_tac[run_insts_preserves_idx] >>
  (* Advance run_block past prefix to terminator position *)
  Q.SUBGOAL_THEN `run_block fuel ctx bb1 s =
       run_block fuel ctx bb1
         (s1' with vs_inst_idx := LENGTH (FRONT bb1.bb_instructions))`
  ASSUME_TAC
  >- (mp_tac (Q.SPECL [`FRONT bb1.bb_instructions`, `fuel`, `ctx`,
                        `bb1`, `s`, `0`, `s1'`] run_block_skip_prefix) >>
      simp[LENGTH_FRONT] >> disch_then match_mp_tac >>
      rpt strip_tac >> irule (GSYM EL_FRONT) >> simp[NULL_EQ, LENGTH_FRONT]) >>
  Q.SUBGOAL_THEN `run_block fuel ctx bb2 s =
       run_block fuel ctx bb2
         (s2' with vs_inst_idx := LENGTH (FRONT bb2.bb_instructions))`
  ASSUME_TAC
  >- (mp_tac (Q.SPECL [`FRONT bb2.bb_instructions`, `fuel`, `ctx`,
                        `bb2`, `s`, `0`, `s2'`] run_block_skip_prefix) >>
      simp[LENGTH_FRONT] >> disch_then match_mp_tac >>
      rpt strip_tac >> irule (GSYM EL_FRONT) >> simp[NULL_EQ, LENGTH_FRONT]) >>
  ntac 2 (pop_assum (fn th => REWRITE_TAC[th])) >>
  (* Structural: EL at FRONT length = LAST *)
  Q.SUBGOAL_THEN `LENGTH (FRONT bb1.bb_instructions) < LENGTH bb1.bb_instructions`
  ASSUME_TAC >- (simp[LENGTH_FRONT] >> Cases_on `LENGTH bb1.bb_instructions` >> fs[]) >>
  Q.SUBGOAL_THEN `LENGTH (FRONT bb2.bb_instructions) < LENGTH bb2.bb_instructions`
  ASSUME_TAC >- (simp[LENGTH_FRONT] >> Cases_on `LENGTH bb2.bb_instructions` >> fs[]) >>
  Q.SUBGOAL_THEN `EL (LENGTH (FRONT bb1.bb_instructions)) bb1.bb_instructions =
                   LAST bb2.bb_instructions`
  ASSUME_TAC >- metis_tac[EL_LENGTH_SNOC, SNOC_LAST_FRONT] >>
  Q.SUBGOAL_THEN `EL (LENGTH (FRONT bb2.bb_instructions)) bb2.bb_instructions =
                   LAST bb2.bb_instructions`
  ASSUME_TAC >- metis_tac[EL_LENGTH_SNOC, SNOC_LAST_FRONT] >>
  Q.SUBGOAL_THEN `(LAST bb2.bb_instructions).inst_opcode <> INVOKE` ASSUME_TAC
  >- (strip_tac >> gvs[venomInstTheory.is_terminator_def]) >>
  (* Unfold run_block at terminator position *)
  CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV [run_block_def]))) >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  simp[venomInstTheory.get_instruction_def,
       venomExecSemanticsTheory.step_inst_non_invoke] >>
  Q.SUBGOAL_THEN `is_terminator (LAST bb2.bb_instructions).inst_opcode`
  ASSUME_TAC >- metis_tac[] >>
  simp[] >>
  (* Apply the combined terminator+halted_wrap helper *)
  irule terminator_halted_wrap_lift_result >> simp[]
QED

Triviality run_insts_front_sim_run_block[local]:
  !fuel ctx bb1 bb2 s V.
    bb1.bb_instructions <> [] /\ bb2.bb_instructions <> [] /\
    LAST bb1.bb_instructions = LAST bb2.bb_instructions /\
    is_terminator (LAST bb1.bb_instructions).inst_opcode /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
          (FRONT bb1.bb_instructions) /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
          (FRONT bb2.bb_instructions) /\
    s.vs_inst_idx = 0 /\
    lift_result (state_equiv V) (execution_equiv UNIV) (execution_equiv UNIV)
      (run_insts fuel ctx (FRONT bb1.bb_instructions) s)
      (run_insts fuel ctx (FRONT bb2.bb_instructions) s) /\
    (!x. MEM (Var x) (LAST bb1.bb_instructions).inst_operands ==> x NOTIN V)
  ==>
    lift_result (state_equiv V) (execution_equiv UNIV) (execution_equiv UNIV)
      (run_block fuel ctx bb1 s)
      (run_block fuel ctx bb2 s)
Proof
  rpt strip_tac >>
  Cases_on `?s1'. run_insts fuel ctx (FRONT bb1.bb_instructions) s = OK s1'`
  >- (
    gvs[] >>
    Cases_on `run_insts fuel ctx (FRONT bb2.bb_instructions) s` >>
    gvs[lift_result_def] >>
    irule run_insts_front_sim_run_block_ok >> simp[] >> metis_tac[])
  >- (irule run_insts_front_sim_run_block_fail >> simp[] >> metis_tac[])
QED

(* The FRONT of the AC transform is the FOLDL on the FRONT of the original *)
Triviality ac_transform_front[local]:
  !dfg bb.
    bb.bb_instructions <> [] /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    ac_scan_block dfg bb.bb_instructions NONE <> [] ==>
    let cands = ac_scan_block dfg bb.bb_instructions NONE in
    let trans = ac_transform_block dfg bb in
    trans.bb_instructions =
      SND (FOLDL (ac_apply_merge_step cands) ([], [])
                  (FRONT bb.bb_instructions)) ++ [LAST bb.bb_instructions] /\
    LAST trans.bb_instructions = LAST bb.bb_instructions /\
    trans.bb_instructions <> []
Proof
  rpt strip_tac >> simp[LET_THM, ac_transform_block_def] >>
  `bb.bb_instructions = SNOC (LAST bb.bb_instructions)
                             (FRONT bb.bb_instructions)` by
    simp[SNOC_LAST_FRONT] >>
  qabbrev_tac `term = LAST bb.bb_instructions` >>
  qabbrev_tac `cands = ac_scan_block dfg bb.bb_instructions NONE` >>
  `MEM term bb.bb_instructions` by simp[Abbr `term`, MEM_LAST_NOT_NIL] >>
  `~EXISTS (\mc. mc.mc_first_id = term.inst_id) cands /\
   FIND (\mc. mc.mc_second_id = term.inst_id) cands = NONE` by
    (qunabbrev_tac `cands` >>
     match_mp_tac term_not_candidate >> simp[]) >>
  `SND (FOLDL (ac_apply_merge_step cands) ([], [])
              (SNOC term (FRONT bb.bb_instructions))) =
   SNOC term (SND (FOLDL (ac_apply_merge_step cands) ([], [])
                          (FRONT bb.bb_instructions)))` by
    metis_tac[ac_foldl_snoc_term] >>
  ONCE_ASM_REWRITE_TAC[] >>
  simp[SNOC_APPEND, LAST_APPEND_CONS]
QED

(* ac_apply_merge_step preserves the non-term non-INVOKE property *)
Triviality ac_merge_step_non_term[local]:
  !cands mp acc inst.
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) acc /\
    (ac_is_safe_between inst \/ inst.inst_opcode = ASSERT) ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
          (SND (ac_apply_merge_step cands (mp, acc) inst))
Proof
  rpt strip_tac >>
  simp[ac_apply_merge_step_def, LET_THM] >>
  BasicProvers.every_case_tac >>
  gvs[EVERY_APPEND, venomInstTheory.is_terminator_def,
      ac_is_safe_between_def] >>
  simp[venomInstTheory.is_terminator_def] >>
  strip_tac >> gvs[venomEffectsTheory.write_effects_def,
                    venomEffectsTheory.all_effects_def]
QED

(* FOLDL of ac_apply_merge_step preserves non-term non-INVOKE *)
Triviality ac_foldl_non_term[local]:
  !cands mp acc insts.
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) acc /\
    EVERY (\i. ac_is_safe_between i \/ i.inst_opcode = ASSERT) insts ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
          (SND (FOLDL (ac_apply_merge_step cands) (mp, acc) insts))
Proof
  Induct_on `insts` >> simp[] >>
  rpt strip_tac >>
  Cases_on `ac_apply_merge_step cands (mp, acc) h` >>
  first_x_assum match_mp_tac >> simp[] >>
  `r = SND (ac_apply_merge_step cands (mp, acc) h)` by simp[] >>
  gvs[] >> metis_tac[ac_merge_step_non_term]
QED

(* FRONT of ac transform is all non-terminator non-INVOKE *)
Triviality ac_transform_front_non_term[local]:
  !dfg bb.
    bb_well_formed bb /\
    EVERY (\i. ac_is_safe_between i \/ i.inst_opcode = ASSERT \/
               is_terminator i.inst_opcode) bb.bb_instructions ==>
    let cands = ac_scan_block dfg bb.bb_instructions NONE in
    let trans_insts = SND (FOLDL (ac_apply_merge_step cands) ([], [])
                                  (FRONT bb.bb_instructions)) in
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
          trans_insts
Proof
  rpt strip_tac >> simp[LET_THM] >>
  match_mp_tac ac_foldl_non_term >> simp[] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  metis_tac[front_not_terminator]
QED

(* ALL_DISTINCT on FRONT from ALL_DISTINCT on full list *)
Triviality all_distinct_outputs_front[local]:
  !bb. bb.bb_instructions <> [] /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (FRONT bb.bb_instructions)))
Proof
  rpt strip_tac >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  (Q.SUBGOAL_THEN `bb.bb_instructions = SNOC (LAST bb.bb_instructions)
       (FRONT bb.bb_instructions)` (fn th => CONV_TAC (DEPTH_CONV (REWR_CONV th)))
   >- simp[SNOC_LAST_FRONT]) >>
  simp[SNOC_APPEND, MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]
QED

(* ac_block_sim_same: per-block simulation when cands are non-empty.
   Assumes ac_sim_precond directly; discharged by ac_block_establishes_precond
   at the ac_block_sim level. *)
Theorem ac_block_sim_same_nonempty[local]:
  !cands dfg bb fuel ctx s V.
    cands = ac_scan_block dfg bb.bb_instructions NONE /\
    cands <> [] /\
    ac_dfg_inv dfg s /\
    EVERY inst_wf bb.bb_instructions /\
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    EVERY (\i. ac_is_safe_between i \/ i.inst_opcode = ASSERT \/
               is_terminator i.inst_opcode) bb.bb_instructions /\
    s.vs_inst_idx = 0 /\
    ac_fresh_vars_block dfg bb SUBSET V /\
    (!inst x. MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       x NOTIN V) /\
    (!inst x. MEM inst bb.bb_instructions /\ MEM x inst.inst_outputs ==>
       x NOTIN V) /\
    (!inst op. MEM inst bb.bb_instructions /\ MEM op inst.inst_operands ==>
       IS_SOME (eval_operand op s)) /\
    ac_sim_precond cands [] dfg (FRONT bb.bb_instructions) s V /\
    (!i x. MEM i bb.bb_instructions /\ MEM x i.inst_outputs ==>
       ~IS_SOME (lookup_var x s)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
    lift_result
      (state_equiv V)
      (execution_equiv UNIV)
      (execution_equiv UNIV)
      (run_block fuel ctx bb s)
      (run_block fuel ctx (ac_transform_block dfg bb) s)
Proof
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  (Q.SUBGOAL_THEN `bb.bb_instructions <> []` ASSUME_TAC >- fs[bb_well_formed_def]) >>
  (Q.SUBGOAL_THEN `is_terminator (LAST bb.bb_instructions).inst_opcode` ASSUME_TAC
   >- fs[bb_well_formed_def]) >>
  qabbrev_tac `cands = ac_scan_block dfg bb.bb_instructions NONE` >>
  (* Derive no_redefine and ALL_DISTINCT for FRONT *)
  (Q.SUBGOAL_THEN
    `(!i x. MEM i (FRONT bb.bb_instructions) /\ MEM x i.inst_outputs ==>
        ~IS_SOME (lookup_var x s)) /\
     ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (FRONT bb.bb_instructions)))`
    STRIP_ASSUME_TAC >-
    (conj_tac
     >- (rpt strip_tac >> first_x_assum irule >> metis_tac[MEM_FRONT_NOT_NIL])
     >- metis_tac[all_distinct_outputs_front])) >>
  (Q.SUBGOAL_THEN
    `lift_result (state_equiv V) (execution_equiv UNIV) (execution_equiv UNIV)
       (run_insts fuel ctx (FRONT bb.bb_instructions) s)
       (run_insts fuel ctx
          (SND (FOLDL (ac_apply_merge_step cands) ([], [])
                       (FRONT bb.bb_instructions))) s)`
    ASSUME_TAC >-
    (irule ac_run_insts_sim >> metis_tac[])) >>
  Q.SUBGOAL_THEN
    `(ac_transform_block dfg bb).bb_instructions =
     SND (FOLDL (ac_apply_merge_step cands) ([], [])
                 (FRONT bb.bb_instructions)) ++ [LAST bb.bb_instructions] /\
     LAST (ac_transform_block dfg bb).bb_instructions =
       LAST bb.bb_instructions /\
     (ac_transform_block dfg bb).bb_instructions <> []`
    STRIP_ASSUME_TAC
  >- (qunabbrev_tac `cands` >>
      mp_tac ac_transform_front >> simp[LET_THM]) >>
  Q.SUBGOAL_THEN
    `FRONT (ac_transform_block dfg bb).bb_instructions =
     SND (FOLDL (ac_apply_merge_step cands) ([], [])
                 (FRONT bb.bb_instructions))`
    ASSUME_TAC
  >- simp[FRONT_APPEND] >>
  match_mp_tac run_insts_front_sim_run_block >>
  pop_assum (fn front_eq => REWRITE_TAC[front_eq]) >>
  simp[] >> rpt conj_tac
  >- (simp[EVERY_MEM] >> metis_tac[front_not_terminator])
  >- (qunabbrev_tac `cands` >>
      irule (SIMP_RULE (srw_ss()) [LET_THM] ac_transform_front_non_term) >>
      simp[])
  >- (rpt strip_tac >> metis_tac[MEM_LAST_NOT_NIL])
QED

(* Wrapper: handles both empty and non-empty candidate cases *)
Theorem ac_block_sim_same[local]:
  !dfg bb fuel ctx s V.
    ac_dfg_inv dfg s /\
    EVERY inst_wf bb.bb_instructions /\
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    EVERY (\i. ac_is_safe_between i \/ i.inst_opcode = ASSERT \/
               is_terminator i.inst_opcode) bb.bb_instructions /\
    s.vs_inst_idx = 0 /\
    ac_fresh_vars_block dfg bb SUBSET V /\
    (!inst x. MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       x NOTIN V) /\
    (!inst x. MEM inst bb.bb_instructions /\ MEM x inst.inst_outputs ==>
       x NOTIN V) /\
    (!inst op. MEM inst bb.bb_instructions /\ MEM op inst.inst_operands ==>
       IS_SOME (eval_operand op s)) /\
    (ac_scan_block dfg bb.bb_instructions NONE <> [] ==>
     ac_sim_precond (ac_scan_block dfg bb.bb_instructions NONE) []
       dfg (FRONT bb.bb_instructions) s V) /\
    (!i x. MEM i bb.bb_instructions /\ MEM x i.inst_outputs ==>
       ~IS_SOME (lookup_var x s)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
    lift_result
      (state_equiv V)
      (execution_equiv UNIV)
      (execution_equiv UNIV)
      (run_block fuel ctx bb s)
      (run_block fuel ctx (ac_transform_block dfg bb) s)
Proof
  rpt strip_tac >>
  Cases_on `ac_scan_block dfg bb.bb_instructions NONE = []`
  >- (
    (Q.SUBGOAL_THEN `bb.bb_instructions <> []` ASSUME_TAC >- fs[bb_well_formed_def]) >>
    (Q.SUBGOAL_THEN `ac_transform_block dfg bb = bb` ASSUME_TAC
     >- fs[ac_block_sim_same_no_cands]) >>
    pop_assum (fn th => REWRITE_TAC[th]) >>
    irule lift_result_refl >> simp[state_equiv_refl, execution_equiv_refl]
  )
  >- (
    irule ac_block_sim_same_nonempty >> metis_tac[]
  )
QED

(* ALL_DISTINCT (FLAT ls) ∧ MEM l ls ⟹ ALL_DISTINCT l *)
Triviality all_distinct_flat_mem[local]:
  !ls (l:'a list). ALL_DISTINCT (FLAT ls) /\ MEM l ls ==> ALL_DISTINCT l
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[ALL_DISTINCT_APPEND]
QED

(* ssa_form gives per-block ALL_DISTINCT on outputs *)
Triviality ssa_form_block_outputs_distinct[local]:
  !fn bb. ssa_form fn /\ MEM bb fn.fn_blocks ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
Proof
  simp[venomWfTheory.ssa_form_def, venomInstTheory.fn_insts_def] >>
  rpt strip_tac >>
  ntac 2 (pop_assum mp_tac) >>
  qspec_tac (`fn.fn_blocks`, `bbs`) >>
  Induct >> simp[venomInstTheory.fn_insts_blocks_def] >>
  rpt strip_tac >> gvs[ALL_DISTINCT_APPEND, MAP_APPEND, FLAT_APPEND]
QED

(* state_equiv V s1 s2 ∧ x ∉ V ⟹ lookup_var x s1 = lookup_var x s2 *)
Triviality state_equiv_lookup_var[local]:
  !V x s1 s2. state_equiv V s1 s2 /\ x NOTIN V ==>
    lookup_var x s1 = lookup_var x s2
Proof
  rw[state_equiv_def, execution_equiv_def]
QED

(* Derive ac_block_establishes_precond hypotheses from fn-level facts.
   Each conjunct is proved as a separate Proof step — no multi-goal dispatch. *)
Triviality ac_fn_block_precond[local]:
  !fn bb s.
    MEM bb fn.fn_blocks /\
    fn_inst_wf fn /\ wf_function fn /\ wf_ssa fn /\
    (!bb' i. MEM bb' fn.fn_blocks /\ MEM i bb'.bb_instructions ==>
       ac_is_safe_between i \/ i.inst_opcode = ASSERT \/
       is_terminator i.inst_opcode) /\
    ac_inv fn (dfg_build_function fn) s /\
    (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN ac_fresh_vars_fn fn) /\
    (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM x inst.inst_outputs ==> x NOTIN ac_fresh_vars_fn fn) /\
    (!bb' i x. MEM bb' fn.fn_blocks /\ MEM i bb'.bb_instructions /\
       MEM x i.inst_outputs ==> ~IS_SOME (lookup_var x s)) /\
    ac_scan_block (dfg_build_function fn) bb.bb_instructions NONE <> [] ==>
    ac_dfg_inv (dfg_build_function fn) s /\
    EVERY inst_wf bb.bb_instructions /\
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    EVERY (\i. ac_is_safe_between i \/ i.inst_opcode = ASSERT \/
               is_terminator i.inst_opcode) bb.bb_instructions /\
    ac_fresh_vars_block (dfg_build_function fn) bb SUBSET ac_fresh_vars_fn fn /\
    (!inst x. MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       x NOTIN ac_fresh_vars_fn fn) /\
    (!inst x. MEM inst bb.bb_instructions /\ MEM x inst.inst_outputs ==>
       x NOTIN ac_fresh_vars_fn fn) /\
    (!inst op. MEM inst bb.bb_instructions /\ MEM op inst.inst_operands ==>
       IS_SOME (eval_operand op s)) /\
    ac_scan_block (dfg_build_function fn) bb.bb_instructions NONE <> [] /\
    (!i v. MEM i bb.bb_instructions /\ MEM v i.inst_outputs /\
       dfg_get_def (dfg_build_function fn) v <> NONE ==>
       dfg_get_def (dfg_build_function fn) v = SOME i) /\
    (!i x. MEM i bb.bb_instructions /\ MEM x i.inst_outputs /\
       MEM (Var x) i.inst_operands ==> F) /\
    (!v. v IN ac_fresh_vars_fn fn ==>
       dfg_get_def (dfg_build_function fn) v = NONE) /\
    (!di x v. dfg_get_def (dfg_build_function fn) x = SOME di /\
       MEM (Var v) di.inst_operands ==> v NOTIN ac_fresh_vars_fn fn) /\
    (!i mc. MEM i bb.bb_instructions /\
       MEM mc (ac_scan_block (dfg_build_function fn)
                 bb.bb_instructions NONE) /\
       mc.mc_second_id = i.inst_id ==>
       ?v. i.inst_operands = [Var v] /\
           ac_get_iszero_operand (dfg_build_function fn) {}
             (Var v) = SOME mc.mc_second_pred) /\
    (!i mc. MEM i bb.bb_instructions /\
       MEM mc (ac_scan_block (dfg_build_function fn)
                 bb.bb_instructions NONE) /\
       mc.mc_first_id = i.inst_id ==>
       ?v. i.inst_operands = [Var v] /\
           ac_get_iszero_operand (dfg_build_function fn) {}
             (Var v) = SOME mc.mc_first_pred) /\
    (!mc1 mc2.
       MEM mc1 (ac_scan_block (dfg_build_function fn)
                  bb.bb_instructions NONE) /\
       MEM mc2 (ac_scan_block (dfg_build_function fn)
                  bb.bb_instructions NONE) /\
       mc1.mc_second_id = mc2.mc_first_id ==>
       mc1.mc_second_pred = mc2.mc_first_pred) /\
    (!mc mc' x.
       MEM mc (ac_scan_block (dfg_build_function fn)
                 bb.bb_instructions NONE) /\
       MEM mc' (ac_scan_block (dfg_build_function fn)
                  bb.bb_instructions NONE) /\
       (mc.mc_second_pred = Var x \/ mc.mc_first_pred = Var x) ==>
       x <> ac_or_var mc'.mc_second_id /\
       x <> ac_iz_var mc'.mc_second_id) /\
    (!i x. MEM i bb.bb_instructions /\ MEM x i.inst_outputs ==>
       ~IS_SOME (lookup_var x s)) /\
    (!mc.
       MEM mc (ac_scan_block (dfg_build_function fn)
                 bb.bb_instructions NONE) /\
       (!i. MEM i (FRONT bb.bb_instructions) ==>
          i.inst_id <> mc.mc_first_id) ==>
       eval_operand mc.mc_first_pred s = SOME 0w)
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac
  (* 1: ac_dfg_inv *)        >- fs[ac_inv_def]
  (* 2: EVERY inst_wf *)     >- (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[])
  (* 3: bb_well_formed *)    >- (fs[venomWfTheory.wf_function_def] >> metis_tac[])
  (* 4: ALL_DISTINCT ids *)  >- metis_tac[fn_inst_ids_block_distinct,
                                   venomWfTheory.wf_function_def]
  (* 5: EVERY safe/ASSERT *) >- (simp[EVERY_MEM] >> metis_tac[])
  (* 6: fresh_vars SUBSET *) >- (simp[assertCombinerDefsTheory.ac_fresh_vars_fn_def,
                                   LET_THM] >>
                                  irule SUBSET_BIGUNION_I >> simp[MEM_MAP] >>
                                  metis_tac[])
  (* 7: operands not in V *) >- metis_tac[]
  (* 8: outputs not in V *)  >- metis_tac[]
  (* 9: operands evaluable *)
  >- (rpt strip_tac >> fs[ac_inv_def, EVERY_MEM] >> metis_tac[])
  (* 10: scan <> [] *)       >- first_assum ACCEPT_TAC
  (* 11: unique definer *)
  >- (rpt strip_tac >>
      (Q.SUBGOAL_THEN `MEM i (fn_insts fn)` ASSUME_TAC
       >- (simp[venomInstTheory.fn_insts_def] >> metis_tac[mem_fn_insts])) >>
      imp_res_tac dfg_build_function_defs_complete >>
      imp_res_tac dfg_build_function_correct >>
      metis_tac[all_distinct_flat_map_unique,
        venomWfTheory.wf_ssa_def, ssa_form_def])
  (* 12: no self-reference *)
  >- (rpt strip_tac >>
      metis_tac[ssa_no_self_reference, MEM_FRONT_NOT_NIL,
        venomWfTheory.wf_function_def, bb_well_formed_def])
  (* 13: fresh vars not in DFG *)
  >- (rpt strip_tac >>
      Cases_on `dfg_get_def (dfg_build_function fn) v` >- simp[] >>
      imp_res_tac dfg_def_in_fn_blocks >> metis_tac[])
  (* 14: DFG operand vars not fresh *)
  >- (rpt strip_tac >> imp_res_tac dfg_def_in_fn_blocks >> metis_tac[])
  (* 15: ISZERO chain second *)
  >- (rpt strip_tac >>
      (Q.SUBGOAL_THEN `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)`
        ASSUME_TAC
       >- metis_tac[fn_inst_ids_block_distinct,
            venomWfTheory.wf_function_def]) >>
      imp_res_tac ac_scan_second_iszero_chain >>
      imp_res_tac ac_get_iszero_operand_is_var >> gvs[] >>
      metis_tac[all_distinct_map_mem_eq])
  (* 16: ISZERO chain first *)
  >- (rpt strip_tac >>
      (Q.SUBGOAL_THEN `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)`
        ASSUME_TAC
       >- metis_tac[fn_inst_ids_block_distinct,
            venomWfTheory.wf_function_def]) >>
      imp_res_tac ac_scan_first_iszero_chain >>
      gvs[ac_scan_block_def] >>
      imp_res_tac ac_get_iszero_operand_is_var >> gvs[] >>
      metis_tac[all_distinct_map_mem_eq])
  (* 17: chaining *)
  >- (rpt strip_tac >> irule ac_scan_chaining >>
      metis_tac[fn_inst_ids_block_distinct, venomWfTheory.wf_function_def])
  (* 18: pred disjointness — pred vars ∉ fresh, but or_var/iz_var ∈ fresh *)
  >- (rpt strip_tac >> CCONTR_TAC >> fs[] >>
      imp_res_tac ac_scan_fresh_in_fn >>
      imp_res_tac ac_scan_second_pred_in_fn >>
      imp_res_tac ac_scan_first_pred_in_fn >>
      metis_tac[])
  (* 19: no_redefine — block-level from fn-level *)
  >- metis_tac[]
  (* 20: processed first_ids — mc.mc_first_id is an ASSERT, hence in FRONT;
         this contradicts the hypothesis that no FRONT inst has that id *)
  >- (rpt strip_tac >>
      drule ac_scan_first_is_assert >> simp[] >> strip_tac >>
      (Q.SUBGOAL_THEN `bb_well_formed bb` ASSUME_TAC
       >- metis_tac[venomWfTheory.wf_function_def]) >>
      (Q.SUBGOAL_THEN `MEM inst (FRONT bb.bb_instructions)` ASSUME_TAC
       >- (irule mem_front_not_last >> simp[] >> conj_tac
           >- (CCONTR_TAC >> fs[] >>
               gvs[bb_well_formed_def, venomInstTheory.is_terminator_def])
           >- fs[bb_well_formed_def])) >>
      metis_tac[])
QED

(* Derive block-level simulation from function-level facts.
   Uses ac_fn_block_precond for the 20 preconditions. *)
Triviality ac_block_sim_same_from_fn[local]:
  !fn bb fuel ctx s.
    MEM bb fn.fn_blocks /\
    fn_inst_wf fn /\
    wf_function fn /\
    wf_ssa fn /\
    (!bb' i. MEM bb' fn.fn_blocks /\ MEM i bb'.bb_instructions ==>
       ac_is_safe_between i \/ i.inst_opcode = ASSERT \/
       is_terminator i.inst_opcode) /\
    ac_inv fn (dfg_build_function fn) s /\
    s.vs_inst_idx = 0 /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN ac_fresh_vars_fn fn) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM x inst.inst_outputs ==> x NOTIN ac_fresh_vars_fn fn) /\
    (!bb' i x. MEM bb' fn.fn_blocks /\ MEM i bb'.bb_instructions /\
       MEM x i.inst_outputs ==> ~IS_SOME (lookup_var x s)) ==>
    lift_result
      (state_equiv (ac_fresh_vars_fn fn))
      (execution_equiv UNIV)
      (run_block fuel ctx bb s)
      (run_block fuel ctx (ac_transform_block (dfg_build_function fn) bb) s)
Proof
  rpt strip_tac >>
  irule ac_block_sim_same >> rpt conj_tac >>
  TRY (fs[ac_inv_def] >> NO_TAC) >>
  TRY (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[] >> NO_TAC) >>
  TRY (fs[venomWfTheory.wf_function_def] >> metis_tac[] >> NO_TAC) >>
  TRY (metis_tac[fn_inst_ids_block_distinct,
         venomWfTheory.wf_function_def] >> NO_TAC) >>
  TRY (simp[EVERY_MEM] >> metis_tac[] >> NO_TAC) >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (simp[assertCombinerDefsTheory.ac_fresh_vars_fn_def, LET_THM] >>
       irule SUBSET_BIGUNION_I >> simp[MEM_MAP] >> metis_tac[] >> NO_TAC) >>
  TRY (rpt strip_tac >> res_tac >> NO_TAC) >>
  TRY (fs[ac_inv_def, EVERY_MEM] >> metis_tac[] >> NO_TAC) >>
  TRY (metis_tac[ssa_form_block_outputs_distinct,
         venomWfTheory.wf_ssa_def] >> NO_TAC) >>
  (* ac_sim_precond: use ac_fn_block_precond + ac_block_establishes_precond *)
  strip_tac >>
  mp_tac (Q.SPECL [`fn`, `bb`, `s`] ac_fn_block_precond) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  irule ac_block_establishes_precond >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Cross-state per-block sim via reversed triangle *)
Theorem ac_block_sim[local]:
  !fn dfg bb fuel ctx s1 s2.
    dfg = dfg_build_function fn /\
    MEM bb fn.fn_blocks /\
    fn_inst_wf fn /\
    wf_function fn /\
    wf_ssa fn /\
    (!bb' i. MEM bb' fn.fn_blocks /\ MEM i bb'.bb_instructions ==>
       ac_is_safe_between i \/ i.inst_opcode = ASSERT \/
       is_terminator i.inst_opcode) /\
    state_equiv (ac_fresh_vars_fn fn) s1 s2 /\
    ac_inv fn dfg s1 /\
    ac_inv fn dfg s2 /\
    s1.vs_inst_idx = 0 /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN ac_fresh_vars_fn fn) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM x inst.inst_outputs ==> x NOTIN ac_fresh_vars_fn fn) /\
    (* no_redefine: no block instruction output is defined in s2 *)
    (!bb' i x. MEM bb' fn.fn_blocks /\ MEM i bb'.bb_instructions /\
       MEM x i.inst_outputs ==> ~IS_SOME (lookup_var x s2)) ==>
    lift_result
      (state_equiv (ac_fresh_vars_fn fn))
      (execution_equiv UNIV)
      (run_block fuel ctx bb s1)
      (run_block fuel ctx (ac_transform_block dfg bb) s2)
Proof
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  (* Step 1: state_equiv gives result_equiv for original block *)
  (Q.SUBGOAL_THEN
    `result_equiv (ac_fresh_vars_fn fn)
       (run_block fuel ctx bb s1) (run_block fuel ctx bb s2)`
    ASSUME_TAC >-
    (irule run_block_result_equiv >> simp[] >> conj_tac
     >- metis_tac[]
     >- (irule safe_assert_term_no_invoke >>
         simp[EVERY_MEM] >> metis_tac[]))) >>
  (* Step 2: same-state sim for s2 via helper *)
  (Q.SUBGOAL_THEN
    `lift_result (state_equiv (ac_fresh_vars_fn fn))
       (execution_equiv UNIV) (execution_equiv UNIV)
       (run_block fuel ctx bb s2)
       (run_block fuel ctx (ac_transform_block (dfg_build_function fn) bb) s2)`
    ASSUME_TAC >-
    (irule ac_block_sim_same_from_fn >> simp[] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (fs[state_equiv_def] >> NO_TAC) >>
     rpt strip_tac >> res_tac >> gvs[])) >>
  (* Step 3: compose via transitivity *)
  qpat_x_assum `result_equiv _ _ _` mp_tac >>
  simp[result_equiv_is_lift_result] >> strip_tac >>
  irule (REWRITE_RULE [AND_IMP_INTRO]
    (Q.SPECL [`state_equiv (ac_fresh_vars_fn fn)`,
              `execution_equiv UNIV`] lift_result_trans)) >>
  rpt conj_tac
  >- metis_tac[execution_equiv_trans]
  >- metis_tac[state_equiv_trans]
  >- (qexists_tac `run_block fuel ctx bb s2` >>
      metis_tac[lift_result_weaken_UNIV])
QED

(* ===== Main Theorem ===== *)

Theorem ac_transform_function_correct_proof:
  !fuel ctx fn s.
    let fn' = ac_transform_function fn in
    let dfg = dfg_build_function fn in
    wf_ssa fn /\
    wf_function fn /\
    fn_inst_wf fn /\
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
       ac_is_safe_between inst \/ inst.inst_opcode = ASSERT \/
       is_terminator inst.inst_opcode) /\
    (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN ac_fresh_vars_fn fn) /\
    (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM x inst.inst_outputs ==> x NOTIN ac_fresh_vars_fn fn) /\
    ac_inv fn dfg s /\
    (* no_redefine: all instruction outputs are undefined in initial state *)
    (!bb' inst x. MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions /\
       MEM x inst.inst_outputs ==> ~IS_SOME (lookup_var x s)) /\
    (* Combined invariant preservation for fn blocks *)
    (!bb fuel' ctx' s0 s0'.
       MEM bb fn.fn_blocks /\
       ac_inv fn dfg s0 /\
       (!bb' inst x. MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions /\
          MEM x inst.inst_outputs ==> ~IS_SOME (lookup_var x s0)) /\
       s0.vs_inst_idx = 0 /\
       run_block fuel' ctx' bb s0 = OK s0' /\ ~s0'.vs_halted ==>
       ac_inv fn dfg s0' /\
       (!bb' inst x. MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions /\
          MEM x inst.inst_outputs ==> ~IS_SOME (lookup_var x s0'))) /\
    (* Combined invariant preservation for fn' blocks *)
    (!bb fuel' ctx' s0 s0'.
       MEM bb fn'.fn_blocks /\
       ac_inv fn dfg s0 /\
       (!bb' inst x. MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions /\
          MEM x inst.inst_outputs ==> ~IS_SOME (lookup_var x s0)) /\
       s0.vs_inst_idx = 0 /\
       run_block fuel' ctx' bb s0 = OK s0' /\ ~s0'.vs_halted ==>
       ac_inv fn dfg s0' /\
       (!bb' inst x. MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions /\
          MEM x inst.inst_outputs ==> ~IS_SOME (lookup_var x s0'))) /\
    s.vs_inst_idx = 0 ==>
    lift_result (state_equiv (ac_fresh_vars_fn fn))
               (execution_equiv UNIV) (execution_equiv UNIV)
      (run_function fuel ctx fn s)
      (run_function fuel ctx fn' s)
Proof
  simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  ONCE_REWRITE_TAC[ac_transform_as_fmt] >>
  mp_tac (SIMP_RULE (srw_ss()) [LET_THM] block_sim_function_inv_cross) >>
  disch_then (qspecl_then [
    `state_equiv (ac_fresh_vars_fn fn)`,
    `execution_equiv UNIV`,
    `ac_transform_block (dfg_build_function fn)`,
    `fn`,
    `\s. ac_inv fn (dfg_build_function fn) s /\
         (!bb' inst x. MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions /\
            MEM x inst.inst_outputs ==> ~IS_SOME (lookup_var x s))`
  ] mp_tac) >>
  BETA_TAC >> PURE_REWRITE_TAC[GSYM CONJ_ASSOC] >> disch_then irule >>
  rpt conj_tac >> simp[valid_state_rel_UNIV, ac_transform_block_label] >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (rpt gen_tac >> strip_tac >>
       irule ac_block_sim >> simp[] >> metis_tac[] >> NO_TAC) >>
  ONCE_REWRITE_TAC[GSYM ac_transform_as_fmt] >> first_assum ACCEPT_TAC
QED
