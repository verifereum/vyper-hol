Theory makeSsaCurrentCleanupOwnerReady
Ancestors makeSsaCurrentInsertionInputOrigin makeSsaCurrentActualDefined
  makeSsaCurrentPhaseShape makeSsaCurrentCleanupCopyOrigin
  makeSsaCurrentReinsertionSlots makeSsaCurrentDefs
  makeSsaCurrentInsertedValue makeSsaCurrentCompletedBatch
  makeSsaCurrentRetainedNonclobber rich_list
  venomExecProps venomExecSemantics venomState venomInst venomWf finite_map pred_set list

(* Availability is monotone across a successful parallel batch, even with
   repeated outputs.  No claim about preservation of the particular value. *)
Theorem current_inserted_owner_source_post_defined:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  current_actual_inserted fn v h /\
  lookup_block p fn.fn_blocks = SOME pb /\
  lookup_block h fn.fn_blocks = SOME hb /\ fn_cfg_edge fn p h /\
  current_actual_domain_cut fn (CurrentBody fuel pb) before /\
  before.vs_current_bb = p /\
  get_instruction pb before.vs_inst_idx = SOME inst /\ inst_wf inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst before = OK after /\
  incoming.vs_vars = after.vs_vars /\
  eval_phis incoming hb.bb_instructions = OK source_post ==>
  ?value. lookup_var v source_post = SOME value
Proof
  strip_tac >>
  `v IN FDOM source_post.vs_vars` suffices_by
    simp[lookup_var_def, FLOOKUP_DEF] >>
  Cases_on `!i. i < LENGTH (collect_phis hb.bb_instructions) ==>
    ~MEM v (inst_defs (EL i hb.bb_instructions))`
  >- (`?value. lookup_var v after = SOME value` by
        (irule current_actual_insertion_input_defined >> metis_tac[]) >>
      `v IN FDOM incoming.vs_vars` by
        gvs[lookup_var_def, FLOOKUP_DEF, AllCaseEqs()] >>
      drule current_eval_phis_domain >> simp[SUBSET_DEF] >> metis_tac[]) >>
  gvs[NOT_FORALL_THM, inst_defs_def] >>
  irule current_eval_phis_outputs >>
  qexistsl_tac [`EL i hb.bb_instructions`, `hb.bb_instructions`, `incoming`] >>
  simp[] >>
  `phi_prefix_length hb.bb_instructions =
    LENGTH (collect_phis hb.bb_instructions)` by
    (qspec_then `hb.bb_instructions` (map_every assume_tac o CONJUNCTS)
      current_collect_phi_split >>
     metis_tac[current_phi_prefix_maximal_length]) >>
  qspec_then `hb.bb_instructions` (map_every assume_tac o CONJUNCTS)
    current_collect_phi_split >>
  `LENGTH (collect_phis hb.bb_instructions) <= LENGTH hb.bb_instructions` by
    metis_tac[LENGTH_APPEND, arithmeticTheory.LESS_EQ_ADD] >>
  simp[MEM_EL] >> qexists `i` >> simp[EL_TAKE] >> decide_tac
QED

(* A collapsed replay slot cannot belong to a retained source PHI. *)
Theorem current_replay_collapsed_owner:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\ fn_phis_non_degenerate fn /\
  lookup_block h fn.fn_blocks = SOME old ==>
  ?pre renamed final.
    fn'.fn_blocks = simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
    lookup_block h renamed = SOME final /\
    EVERY (\i. i.inst_opcode = PHI) pre /\
    (!k. k < LENGTH pre ==> ?v. (EL k pre).inst_outputs = [v]) /\
    (!v. current_actual_inserted fn v h <=>
      ?inst. MEM inst pre /\ MEM v inst.inst_outputs) /\
    (!k. k < LENGTH final.bb_instructions /\
      (EL k final.bb_instructions).inst_opcode = PHI /\
      (simplify_current_phi (EL k final.bb_instructions)).inst_opcode <> PHI ==>
      ?v n. current_actual_inserted fn v h /\
        (EL k final.bb_instructions).inst_outputs = [n] /\
        current_token_name H (CurrentInserted v h) = SOME n)
Proof
  strip_tac >> drule_all current_certificate_block_replay >> strip_tac >>
  qexistsl_tac [`pre`, `renamed`, `final`] >> simp[] >>
  `EVERY (\i. i.inst_opcode = PHI) pre /\
   (!k. k < LENGTH pre ==> ?v. (EL k pre).inst_outputs = [v])` by
    (conj_tac
     >- (gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
         simp[build_phi_inst_supply_def] >> rpt strip_tac >> gvs[]) >>
     rpt strip_tac >>
     `?id v. EL k pre = build_phi_inst_supply id v
       (case ALOOKUP (current_pred_map fn) h of NONE => [] | SOME ps => ps)` by
       (gvs[EVERY_EL] >> metis_tac[]) >> simp[build_phi_inst_supply_def]) >>
  simp[] >> rpt strip_tac >> Cases_on `k < LENGTH pre`
  >- (`?v. (EL k pre).inst_outputs = [v]` by metis_tac[] >>
      `current_actual_inserted fn v h` by
        (first_x_assum (irule o iffRL) >> qexists `EL k pre` >> simp[MEM_EL] >>
         metis_tac[]) >> metis_tac[]) >>
  drule current_replay_phi_flags >> strip_tac >>
  `LENGTH final.bb_instructions = LENGTH pre + LENGTH old.bb_instructions` by
    metis_tac[LENGTH_MAP, LENGTH_APPEND] >>
  `k - LENGTH pre < LENGTH old.bb_instructions /\
   LENGTH pre + (k - LENGTH pre) = k` by decide_tac >>
  `(EL (k - LENGTH pre) old.bb_instructions).inst_opcode = PHI` by
    (qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `EL k`) >>
     simp[EL_MAP, EL_APPEND_EQN]) >>
  `inst_wf (EL (k - LENGTH pre) old.bb_instructions)` by
    (qpat_x_assum `fn_inst_wf fn` mp_tac >> simp[fn_inst_wf_def] >>
     disch_then irule >> qexists `old` >>
     conj_tac >- metis_tac[lookup_block_MEM] >>
     simp[MEM_EL] >> qexists `k - LENGTH pre` >> simp[]) >>
  `?v. (EL (k - LENGTH pre) old.bb_instructions).inst_outputs = [v]` by
    (gvs[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  first_x_assum (qspecl_then [`k - LENGTH pre`, `v`] mp_tac) >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem current_certificate_cleanup_assign_owner:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\ fn_phis_non_degenerate fn /\
  lookup_block h fn.fn_blocks = SOME old ==>
  ?renamed final out pp tt k m.
    fn'.fn_blocks = simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
    lookup_block h renamed = SOME final /\ lookup_block h fn'.fn_blocks = SOME out /\
    final.bb_instructions = pp ++ tt /\
    EVERY (\i. i.inst_opcode = PHI) pp /\ (tt = [] \/ (HD tt).inst_opcode <> PHI) /\
    k = (if blocks_have_leading_phi fn.fn_blocks then
      LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pp))
      else LENGTH pp) /\
    m = (if blocks_have_leading_phi fn.fn_blocks then
      LENGTH (FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pp)) else 0) /\
    (!inst n y. MEM inst (TAKE m (DROP k out.bb_instructions)) /\
      inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [n] /\
      inst.inst_operands = [Var y] ==>
      ?v. current_actual_inserted fn v h /\
        current_token_name H (CurrentInserted v h) = SOME n)
Proof
  strip_tac >> drule_all current_replay_collapsed_owner >> strip_tac >>
  qspec_then `final.bb_instructions` (map_every assume_tac o CONJUNCTS)
    current_collect_phi_split >>
  qabbrev_tac `pp = collect_phis final.bb_instructions` >>
  qabbrev_tac `tt = DROP (LENGTH pp) final.bb_instructions` >>
  qabbrev_tac `k = if blocks_have_leading_phi fn.fn_blocks then
    LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pp)) else LENGTH pp` >>
  qabbrev_tac `m = if blocks_have_leading_phi fn.fn_blocks then
    LENGTH (FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pp)) else 0` >>
  `?out. lookup_block h (simplify_current_phis_if
      (blocks_have_leading_phi fn.fn_blocks) renamed) = SOME out /\
    LENGTH (TAKE k out.bb_instructions) = k /\
    LENGTH (TAKE m (DROP k out.bb_instructions)) = m /\
    (!inst. MEM inst (TAKE m (DROP k out.bb_instructions)) ==>
      ?original. MEM original pp /\ (simplify_current_phi original).inst_opcode <> PHI /\
        current_inst_no_id inst = current_inst_no_id (simplify_current_phi original))` by
    (irule current_cleanup_if_copy_inverse >> simp[Abbr `k`, Abbr `m`] >>
     metis_tac[]) >>
  qexistsl_tac [`renamed`, `final`, `out`, `pp`, `tt`, `k`, `m`] >>
  simp[Abbr `k`, Abbr `m`] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  `?j. j < LENGTH pp /\ original = EL j pp` by metis_tac[MEM_EL] >>
  `j < LENGTH final.bb_instructions /\ EL j final.bb_instructions = original /\
   original.inst_opcode = PHI` by
    (gvs[EVERY_EL, EL_APPEND_EQN] >> metis_tac[arithmeticTheory.LESS_ADD]) >>
  first_x_assum (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  `inst.inst_outputs = (simplify_current_phi original).inst_outputs` by
    metis_tac[current_no_id_fields] >>
  qspec_then `original` mp_tac (GEN_ALL current_simplify_phi_outputs) >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem current_certificate_cleanup_owner_ready:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\ fn_phis_non_degenerate fn /\
  fn_defs_reach_uses fn /\
  lookup_block p fn.fn_blocks = SOME pb /\ lookup_block h fn.fn_blocks = SOME hb /\
  fn_cfg_edge fn p h /\ current_actual_domain_cut fn (CurrentBody fuel pb) before /\
  before.vs_current_bb = p /\ get_instruction pb before.vs_inst_idx = SOME inst /\
  inst_wf inst /\ is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst before = OK after /\ incoming.vs_vars = after.vs_vars /\
  eval_phis incoming hb.bb_instructions = OK source_post ==>
  ?renamed final out pp tt k m.
    fn'.fn_blocks = simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
    lookup_block h renamed = SOME final /\ lookup_block h fn'.fn_blocks = SOME out /\
    final.bb_instructions = pp ++ tt /\
    EVERY (\i. i.inst_opcode = PHI) pp /\ (tt = [] \/ (HD tt).inst_opcode <> PHI) /\
    k = (if blocks_have_leading_phi fn.fn_blocks then
      LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pp))
      else LENGTH pp) /\
    m = (if blocks_have_leading_phi fn.fn_blocks then
      LENGTH (FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pp)) else 0) /\
    (!copy n y. MEM copy (TAKE m (DROP k out.bb_instructions)) /\
      copy.inst_opcode = ASSIGN /\ copy.inst_outputs = [n] /\
      copy.inst_operands = [Var y] ==>
      ?v value. current_actual_inserted fn v h /\
        current_token_name H (CurrentInserted v h) = SOME n /\
        lookup_var v source_post = SOME value)
Proof
  strip_tac >> drule_all current_certificate_cleanup_assign_owner >> strip_tac >>
  qexistsl_tac [`renamed`, `final`, `out`, `pp`, `tt`, `k`, `m`] >>
  gvs[] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `?value. lookup_var v source_post = SOME value` by
    (irule current_inserted_owner_source_post_defined >> metis_tac[]) >>
  metis_tac[]
QED
