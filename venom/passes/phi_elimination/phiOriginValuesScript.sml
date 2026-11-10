Theory phiOriginValues
Ancestors
  phiCopyRegion venomWfProps venomWf venomState finite_map list pred_set
  venomInstProps venomExecProps venomExecSemantics phiDefs venomInst

Theorem phi_single_origin_in_fdom:
  wf_function fn /\ wf_ssa fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  fn_reachable fn s.vs_current_bb /\ strict_dom_vars_defined fn s /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
  phi_single_origin (dfg_build_function fn) i = SOME root ==>
  root IN FDOM s.vs_vars
Proof
  strip_tac >>
  `fn_reachable fn bb.bb_label` by metis_tac[] >>
  drule_all phi_single_origin_strict_dominance >> strip_tac >>
  fs[strict_dom_vars_defined_def] >> metis_tac[]
QED

Definition point_available_def:
  point_available fn bb n v <=>
    ?db k. MEM db fn.fn_blocks /\ k < LENGTH db.bb_instructions /\
      MEM v (EL k db.bb_instructions).inst_outputs /\
      fn_dominates fn db.bb_label bb.bb_label /\ (db = bb ==> k < n)
End

Definition region_live_eq_def:
  region_live_eq fn region root bb n s <=>
    !v. v IN region /\ point_available fn bb n v ==>
      lookup_var v s = lookup_var root s
End

Theorem point_inst_index_unique[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  i < LENGTH bb.bb_instructions /\ j < LENGTH bb.bb_instructions /\
  EL i bb.bb_instructions = EL j bb.bb_instructions ==> i = j
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (irule all_distinct_flat_map_member >>
     qexists `MAP (\b. b.bb_instructions) fn.fn_blocks` >>
     gvs[wf_function_def, fn_inst_ids_distinct_def, MAP_COMPOSE, combinTheory.o_DEF, MEM_MAP] >>
     metis_tac[]) >>
  `EL i (MAP (\i. i.inst_id) bb.bb_instructions) =
   EL j (MAP (\i. i.inst_id) bb.bb_instructions)` by simp[EL_MAP] >>
  metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP]
QED

Theorem point_available_some:
  wf_function fn /\ MEM bb fn.fn_blocks /\ n < LENGTH bb.bb_instructions ==>
  (point_available fn bb n v <=>
   def_available_at fn bb (SOME (EL n bb.bb_instructions)) v)
Proof
  strip_tac >> simp[point_available_def, def_available_at_def] >> eq_tac
  >- (strip_tac >> qexistsl [`db`, `EL k db.bb_instructions`] >>
      simp[EL_MEM] >> strip_tac >> gvs[] >>
      qexistsl [`k`, `n`] >> simp[]) >>
  strip_tac >>
  Cases_on `def_bb = bb`
  >- (gvs[] >> `j = n` by metis_tac[point_inst_index_unique] >>
      qexistsl [`bb`, `i`] >> simp[] >> decide_tac) >>
  `?k. k < LENGTH def_bb.bb_instructions /\
       def_inst = EL k def_bb.bb_instructions` by metis_tac[listTheory.MEM_EL] >>
  qexistsl [`def_bb`, `k`] >> gvs[]
QED

Theorem point_available_exit:
  point_available fn bb (LENGTH bb.bb_instructions) v <=>
  def_available_at fn bb NONE v
Proof
  simp[point_available_def, def_available_at_def] >> eq_tac
  >- (strip_tac >> qexistsl [`db`, `EL k db.bb_instructions`] >>
      simp[EL_MEM]) >>
  strip_tac >>
  `?k. k < LENGTH def_bb.bb_instructions /\
       def_inst = EL k def_bb.bb_instructions` by metis_tac[listTheory.MEM_EL] >>
  qexistsl [`def_bb`, `k`] >> simp[] >> metis_tac[]
QED

Theorem point_available_suc:
  point_available fn bb (SUC n) v ==>
  point_available fn bb n v \/ MEM v (EL n bb.bb_instructions).inst_outputs
Proof
  simp[point_available_def] >> strip_tac >>
  Cases_on `db = bb /\ k = n` >- gvs[] >>
  disj1_tac >> qexistsl [`db`, `k`] >> simp[] >> strip_tac >> gvs[]
QED

Theorem copy_region_unavailable_after_root:
  wf_function fn /\ wf_ssa fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  copy_region fn region {root} /\ root NOTIN region /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  n < LENGTH bb.bb_instructions /\
  MEM root (EL n bb.bb_instructions).inst_outputs /\ v IN region ==>
  ~point_available fn bb (SUC n) v
Proof
  strip_tac >> strip_tac >> drule point_available_suc >> strip_tac
  >- (drule_all point_available_some >> strip_tac >>
      `MEM (EL n bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
      metis_tac[copy_region_unavailable_at_root]) >>
  `MEM (EL n bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  metis_tac[copy_region_root_output_disjoint]
QED

Theorem region_live_eq_empty_store:
  s.vs_vars = FEMPTY ==> region_live_eq fn region root bb n s
Proof
  simp[region_live_eq_def, lookup_var_def]
QED

Theorem assign_region_lookup[local]:
  i.inst_opcode = ASSIGN /\ i.inst_outputs = [v] /\
  assign_var_operand i = SOME u /\ step_inst fuel ctx i s = OK t ==>
  lookup_var v t = lookup_var u s
Proof
  simp[assign_var_operand_def, AllCaseEqs()] >> strip_tac >>
  gvs[step_inst_def, step_inst_base_def, eval_operand_def, AllCaseEqs()] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem region_live_eq_step:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  copy_region fn region {root} /\ root NOTIN region /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  n < LENGTH bb.bb_instructions /\ i = EL n bb.bb_instructions /\
  i.inst_opcode <> PHI /\ region_live_eq fn region root bb n s /\
  step_inst fuel ctx i s = OK t ==>
  region_live_eq fn region root bb (SUC n) t
Proof
  strip_tac >>
  `MEM i bb.bb_instructions` by metis_tac[EL_MEM] >>
  Cases_on `MEM root i.inst_outputs`
  >- (simp[region_live_eq_def] >> rpt strip_tac >>
      metis_tac[copy_region_unavailable_after_root]) >>
  `!x. ~MEM x i.inst_outputs ==> lookup_var x t = lookup_var x s` by
    (Cases_on `is_terminator i.inst_opcode` >>
     metis_tac[step_terminator_preserves_vars, step_preserves_non_output_vars]) >>
  simp[region_live_eq_def] >> rpt strip_tac >>
  Cases_on `MEM v i.inst_outputs`
  >- suspend "assign"
  >> drule point_available_suc >> strip_tac >>
  gvs[region_live_eq_def]
QED

Resume region_live_eq_step[assign]:
  drule_all copy_region_inst_inputs >> strip_tac >> fs[] >>
  `MEM (Var u) (EL n bb.bb_instructions).inst_operands` by
    gvs[assign_var_operand_def, AllCaseEqs()] >>
  `def_available_at fn bb (SOME (EL n bb.bb_instructions)) u` by
    (gvs[wf_ssa_def, def_dominates_uses_def] >>
     qpat_x_assum `!bb inst. _` (qspecl_then [`bb`, `EL n bb.bb_instructions`] mp_tac) >>
     simp[]) >>
  `point_available fn bb n u` by metis_tac[point_available_some] >>
  `lookup_var u s = lookup_var root s` by
    (fs[region_live_eq_def] >> metis_tac[]) >>
  drule_all assign_region_lookup >> strip_tac >>
  metis_tac[MEM]
QED

Finalise region_live_eq_step

Theorem point_available_predecessor:
  wf_function fn /\ MEM db fn.fn_blocks /\ MEM bb fn.fn_blocks /\
  fn_dominates fn db.bb_label bb.bb_label /\ db <> bb /\
  fn_cfg_edge fn pb.bb_label bb.bb_label /\ fn_reachable fn pb.bb_label /\
  k < LENGTH db.bb_instructions /\ MEM v (EL k db.bb_instructions).inst_outputs ==>
  point_available fn pb (LENGTH pb.bb_instructions) v
Proof
  strip_tac >>
  `db.bb_label <> bb.bb_label` by
    metis_tac[venomExecProofsTheory.same_label_same_block] >>
  `fn_dominates fn db.bb_label pb.bb_label` by
    metis_tac[venomExecProofsTheory.fn_dominates_predecessor] >>
  simp[point_available_def] >> qexistsl [`db`, `k`] >> simp[] >> metis_tac[]
QED

Theorem region_live_phi_root_frame[local]:
  wf_function fn /\ wf_ssa fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  copy_region fn region {root} /\ root NOTIN region /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  v IN region /\ point_available fn bb (phi_prefix_length bb.bb_instructions) v ==>
  !i. MEM i bb.bb_instructions ==> ~MEM root i.inst_outputs
Proof
  strip_tac >> gen_tac >> strip_tac >> strip_tac >>
  fs[point_available_def] >>
  `MEM (EL k db.bb_instructions) db.bb_instructions` by simp[EL_MEM] >>
  `db.bb_label = bb.bb_label` by
    metis_tac[copy_region_no_strict_dominator_at_root] >>
  `db = bb` by metis_tac[venomExecProofsTheory.same_label_same_block] >>
  gvs[] >>
  `MEM (EL k bb.bb_instructions)
       (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` by
    (simp[MEM_EL] >> qexists `k` >>
     simp[EL_TAKE, LENGTH_TAKE, venomExecProofsTheory.phi_prefix_length_le]) >>
  ` (EL k bb.bb_instructions).inst_opcode = PHI` by metis_tac[phi_prefix_mem] >>
  drule_all copy_region_phi_root_strict_dominance >> strip_tac >>
  `ssa_form fn` by fs[wf_ssa_def] >>
  `di = i` by metis_tac[ssa_form_output_unique] >>
  metis_tac[wf_function_instruction_block]
QED

Theorem region_live_eq_phis:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  copy_region fn region {root} /\ root NOTIN region /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  MEM pb fn.fn_blocks /\ fn_reachable fn pb.bb_label /\
  fn_cfg_edge fn pb.bb_label bb.bb_label /\ s.vs_prev_bb = SOME pb.bb_label /\
  region_live_eq fn region root pb (LENGTH pb.bb_instructions) s /\
  eval_phis s bb.bb_instructions = OK t ==>
  region_live_eq fn region root bb (phi_prefix_length bb.bb_instructions) t
Proof
  strip_tac >> simp[region_live_eq_def] >> rpt strip_tac >>
  `!i. MEM i bb.bb_instructions ==> ~MEM root i.inst_outputs` by
    metis_tac[region_live_phi_root_frame] >>
  `lookup_var root t = lookup_var root s` by
    (irule eval_phis_lookup_frame >> metis_tac[phi_prefix_mem]) >>
  Cases_on `?i. MEM i (TAKE (phi_prefix_length bb.bb_instructions)
                              bb.bb_instructions) /\ MEM v i.inst_outputs`
  >- suspend "written"
  >> `lookup_var v t = lookup_var v s` by
       (irule eval_phis_lookup_frame >> metis_tac[]) >>
  `point_available fn pb (LENGTH pb.bb_instructions) v` by
    (qpat_x_assum `point_available fn bb _ v` mp_tac >>
     simp[Once point_available_def] >> strip_tac >>
     `db <> bb` by
       (strip_tac >> gvs[] >>
        `MEM (EL k bb.bb_instructions)
          (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` by
          (simp[MEM_EL] >> qexists `k` >>
           simp[EL_TAKE, LENGTH_TAKE, venomExecProofsTheory.phi_prefix_length_le]) >>
        metis_tac[]) >>
     irule point_available_predecessor >> metis_tac[]) >>
  fs[region_live_eq_def]
QED

Resume region_live_eq_phis[written]:
  pop_assum strip_assume_tac >>
  `MEM i bb.bb_instructions /\ i.inst_opcode = PHI` by metis_tac[phi_prefix_mem] >>
  `ALL_DISTINCT (FLAT (MAP (\j. j.inst_outputs) bb.bb_instructions))` by
    metis_tac[ssa_form_block_outputs_distinct, wf_ssa_def] >>
  drule_all eval_phis_lookup_output >> strip_tac >>
  `phi_well_formed i.inst_operands` by
    (`inst_wf i` by (fs[fn_inst_wf_def] >> metis_tac[]) >>
     qpat_x_assum `inst_wf i` mp_tac >> simp[inst_wf_def]) >>
  gvs[eval_one_phi_def, AllCaseEqs()] >>
  drule_all resolve_phi_well_formed >> strip_tac >> gvs[eval_operand_def] >>
  `MEM out i.inst_outputs` by simp[] >>
  drule_all copy_region_inst_inputs >> strip_tac >> fs[] >>
  `var IN region \/ var = root` by
    (drule resolve_phi_in_operands >> fs[SUBSET_DEF]) >>
  `def_available_at fn pb NONE var` by
    (drule_all resolved_phi_input_available >> strip_tac >>
     `pb' = pb` by metis_tac[venomExecProofsTheory.same_label_same_block] >> gvs[]) >>
  fs[region_live_eq_def, point_available_exit] >> metis_tac[]
QED

Finalise region_live_eq_phis

(* Source entries retain the incoming, pre-PHI snapshot.  The relation is
   independent of the context's designated entry function and of any fuel
   history; each edge records one successful source block execution. *)
Inductive source_entry_reachable:
  (!ctx fn s0. source_entry_reachable ctx fn s0 s0) /\
  (!ctx fn s0 s bb fuel t.
    source_entry_reachable ctx fn s0 s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    run_block fuel ctx bb s = OK t ==>
    source_entry_reachable ctx fn s0 t)
End

Theorem source_entry_reachable_seed:
  source_entry_reachable ctx fn s0 s0
Proof
  metis_tac[source_entry_reachable_rules]
QED

Theorem source_entry_reachable_step:
  source_entry_reachable ctx fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block fuel ctx bb s = OK t ==>
  source_entry_reachable ctx fn s0 t
Proof
  metis_tac[source_entry_reachable_rules]
QED

Theorem source_entry_run_blocks_recursive_call:
  source_entry_reachable ctx fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block fuel ctx bb s = OK t /\ ~t.vs_halted ==>
  source_entry_reachable ctx fn s0 t /\
  run_blocks (SUC fuel) ctx fn s = run_blocks fuel ctx fn t
Proof
  metis_tac[source_entry_reachable_step, run_blocks_step]
QED

Theorem source_entry_empty_seed:
  fn_entry_label fn = SOME s0.vs_current_bb /\ s0.vs_vars = FEMPTY ==>
  source_entry_reachable ctx fn s0 s0 /\ strict_dom_vars_defined fn s0 /\
  region_live_eq fn region root bb n s0
Proof
  metis_tac[source_entry_reachable_seed, strict_dom_vars_defined_entry,
            region_live_eq_empty_store]
QED

Theorem source_entry_reachable_invariant:
  !ctx fn s0 P.
    P s0 /\
    (!s bb fuel t. source_entry_reachable ctx fn s0 s /\ P s /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      run_block fuel ctx bb s = OK t ==> P t) ==>
    !s. source_entry_reachable ctx fn s0 s ==> P s
Proof
  rpt gen_tac >> strip_tac >>
  qspec_then `\c f z s. c = ctx /\ f = fn /\ z = s0 ==> P s`
    mp_tac source_entry_reachable_strongind >>
  simp[] >> impl_tac >- metis_tac[] >> metis_tac[]
QED

Theorem region_live_eq_exec_block:
  !s t.
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  copy_region fn region {root} /\ root NOTIN region /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  s.vs_inst_idx <= LENGTH bb.bb_instructions /\
  region_live_eq fn region root bb s.vs_inst_idx s /\
  exec_block fuel ctx bb s = OK t ==>
  region_live_eq fn region root bb (LENGTH bb.bb_instructions) t
Proof
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def, get_instruction_def] >>
  IF_CASES_TAC >> simp[] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode <> PHI` by
    metis_tac[venomExecProofsTheory.step_inst_ok_imp_not_phi] >>
  `region_live_eq fn region root bb (SUC s.vs_inst_idx) s''` by
    (irule region_live_eq_step >> metis_tac[]) >>
  Cases_on `is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode`
  >- (`SUC s.vs_inst_idx = LENGTH bb.bb_instructions` by
        (`s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by
          (fs[wf_function_def, bb_well_formed_def] >> metis_tac[]) >>
         decide_tac) >> gvs[]) >>
  gvs[] >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  simp[] >>
  disch_then (qspec_then `s'' with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  fs[region_live_eq_def, lookup_var_def]
QED

Definition source_entry_inv_def:
  source_entry_inv fn s0 s <=>
    fn_reachable fn s.vs_current_bb /\ strict_dom_vars_defined fn s /\
    (s = s0 \/ ?pb. MEM pb fn.fn_blocks /\ fn_reachable fn pb.bb_label /\
      s.vs_prev_bb = SOME pb.bb_label /\
      fn_cfg_edge fn pb.bb_label s.vs_current_bb /\
      !region root. copy_region fn region {root} /\ root NOTIN region ==>
        region_live_eq fn region root pb (LENGTH pb.bb_instructions) s)
End

Theorem source_entry_inv_seed[local]:
  fn_entry_label fn = SOME s0.vs_current_bb ==> source_entry_inv fn s0 s0
Proof
  simp[source_entry_inv_def, fn_reachable_def] >>
  metis_tac[relationTheory.RTC_REFL, strict_dom_vars_defined_entry]
QED

Theorem source_entry_inv_phis:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  fn_entry_label fn = SOME s0.vs_current_bb /\ s0.vs_vars = FEMPTY /\
  source_entry_inv fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  copy_region fn region {root} /\ root NOTIN region /\
  eval_phis s bb.bb_instructions = OK p ==>
  region_live_eq fn region root bb (phi_prefix_length bb.bb_instructions) p
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM, lookup_block_label] >>
  fs[source_entry_inv_def] >- suspend "seed" >>
  irule region_live_eq_phis >> metis_tac[]
QED

Resume source_entry_inv_phis[seed]:
  gvs[] >>
  `bb = HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm]) >>
  gvs[] >>
  `eval_phis s (HD fn.fn_blocks).bb_instructions = OK s` by
    metis_tac[venomExecProofsTheory.eval_phis_no_phis] >>
  gvs[] >> irule region_live_eq_empty_store >> simp[]
QED

Finalise source_entry_inv_phis

Theorem source_entry_inv_step[local]:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  fn_entry_label fn = SOME s0.vs_current_bb /\ s0.vs_vars = FEMPTY /\
  source_entry_inv fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block fuel ctx bb s = OK t ==> source_entry_inv fn s0 t
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM, lookup_block_label] >>
  `bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions` by
    (fs[wf_function_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `fn_reachable fn s.vs_current_bb /\ strict_dom_vars_defined fn s` by
    fs[source_entry_inv_def] >>
  `strict_dom_vars_defined fn t` by
    (irule strict_dom_vars_defined_run_block_entry >> metis_tac[]) >>
  mp_tac (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  strip_tac >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  simp[run_block_def] >> strip_tac >> gvs[] >>
  rename1 `eval_phis s bb.bb_instructions = OK p` >>
  `p.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  `(!i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    bb.bb_instructions <> []` by
    (fs[bb_well_formed_def] >> rpt strip_tac >>
     `i = PRE (LENGTH bb.bb_instructions)` by simp[] >> decide_tac) >>
  `MEM t.vs_current_bb (bb_succs bb) /\
    t.vs_prev_bb = SOME s.vs_current_bb` by
    (conj_tac
     >- (irule exec_block_current_bb_in_succs >> simp[] >>
         qexistsl [`ctx`, `fuel`,
           `p with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >>
         simp[venomExecProofsTheory.phi_prefix_length_le]) >>
     ` (p with vs_inst_idx := phi_prefix_length bb.bb_instructions).vs_inst_idx <=
         LENGTH bb.bb_instructions` by
       simp[venomExecProofsTheory.phi_prefix_length_le] >>
     drule_all exec_block_ok_prev_bb_general >> simp[]) >>
  `fn_cfg_edge fn bb.bb_label t.vs_current_bb` by
    (simp[fn_cfg_edge_def] >> metis_tac[]) >>
  simp[source_entry_inv_def] >> conj_tac
  >- metis_tac[venomExecProofsTheory.fn_reachable_step] >>
  disj2_tac >> qexists `bb` >> simp[] >> rpt strip_tac >>
  irule region_live_eq_exec_block >> simp[] >>
  qexistsl [`ctx`, `fuel`,
    `p with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >>
  simp[venomExecProofsTheory.phi_prefix_length_le] >>
  `region_live_eq fn region root bb (phi_prefix_length bb.bb_instructions) p` by
    (irule source_entry_inv_phis >> metis_tac[]) >>
  fs[region_live_eq_def, lookup_var_def]
QED

Theorem source_entry_reachable_inv:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  fn_entry_label fn = SOME s0.vs_current_bb /\ s0.vs_vars = FEMPTY ==>
  !s. source_entry_reachable ctx fn s0 s ==> source_entry_inv fn s0 s
Proof
  strip_tac >> ho_match_mp_tac source_entry_reachable_invariant >>
  conj_tac >- metis_tac[source_entry_inv_seed] >>
  rpt strip_tac >> irule source_entry_inv_step >> metis_tac[]
QED

Theorem source_entry_reachable_defined:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  fn_entry_label fn = SOME s0.vs_current_bb /\ s0.vs_vars = FEMPTY /\
  source_entry_reachable ctx fn s0 s ==>
  strict_dom_vars_defined fn s
Proof
  metis_tac[source_entry_reachable_inv, source_entry_inv_def]
QED

Theorem phi_single_origin_block_frame:
  wf_function fn /\ wf_ssa fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
  phi_single_origin (dfg_build_function fn) i = SOME root ==>
  !j. MEM j bb.bb_instructions ==> ~MEM root j.inst_outputs
Proof
  strip_tac >> drule_all phi_single_origin_strict_dominance >> strip_tac >>
  rpt strip_tac >>
  `ssa_form fn` by fs[wf_ssa_def] >>
  `di = j` by metis_tac[ssa_form_output_unique] >>
  metis_tac[wf_function_instruction_block]
QED

Theorem phi_single_origin_incoming_value:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  fn_entry_label fn = SOME s0.vs_current_bb /\ s0.vs_vars = FEMPTY /\
  source_entry_reachable ctx fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
  phi_single_origin (dfg_build_function fn) i = SOME root ==>
  ?out value. i.inst_outputs = [out] /\ lookup_var root s = SOME value /\
    eval_one_phi s i = SOME (out,value)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM, lookup_block_label] >>
  `source_entry_inv fn s0 s` by metis_tac[source_entry_reachable_inv] >>
  `root IN FDOM s.vs_vars` by
    (irule phi_single_origin_in_fdom >> fs[source_entry_inv_def] >> metis_tac[]) >>
  `?value. lookup_var root s = SOME value` by
    fs[lookup_var_def, FLOOKUP_DEF] >>
  `MEM i (fn_insts fn)` by metis_tac[fmp_fn_insts_blocks_intro, fn_insts_def] >>
  drule_all phi_single_origin_copy_region >> strip_tac >>
  rename1 `copy_region fn region {root}` >>
  fs[source_entry_inv_def]
  >- (gvs[] >>
      `bb = HD fn.fn_blocks` by
        (Cases_on `fn.fn_blocks` >>
         gvs[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm]) >>
      fs[EVERY_MEM] >> metis_tac[]) >>
  `phi_edge_uses_wf fn bb i` by
    (fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]) >>
  `?op. resolve_phi pb.bb_label i.inst_operands = SOME op` by
    (fs[phi_edge_uses_wf_def] >>
     `?p. MEM p (phi_pairs i.inst_operands) /\ FST p = pb.bb_label` by metis_tac[] >>
     PairCases_on `p` >> gvs[] >>
     irule phi_pairs_resolve_phi_some >> metis_tac[]) >>
  `?v. op = Var v` by metis_tac[resolve_phi_well_formed, phi_edge_uses_wf_def] >>
  gvs[] >>
  `def_available_at fn pb NONE v` by
    (drule_all resolved_phi_input_available >> strip_tac >>
     `pb' = pb` by metis_tac[venomExecProofsTheory.same_label_same_block] >> gvs[]) >>
  `MEM out i.inst_outputs` by simp[] >>
  `v IN region \/ v = root` by
    (drule_all copy_region_inst_inputs >> strip_tac >> fs[] >>
     drule resolve_phi_in_operands >> fs[SUBSET_DEF]) >>
  `lookup_var v s = SOME value` by
    (fs[region_live_eq_def, point_available_exit] >> metis_tac[]) >>
  simp[eval_one_phi_def, eval_operand_def]
QED

Theorem phi_single_origin_eval_phis_frame:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  fn_entry_label fn = SOME s0.vs_current_bb /\ s0.vs_vars = FEMPTY /\
  source_entry_reachable ctx fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
  phi_single_origin (dfg_build_function fn) i = SOME root /\
  (!j. MEM j ps ==> MEM j bb.bb_instructions) /\
  eval_phis s ps = OK t ==>
  lookup_var root t = lookup_var root s
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM, lookup_block_label] >>
  `fn_reachable fn bb.bb_label` by
    metis_tac[source_entry_reachable_inv, source_entry_inv_def] >>
  irule eval_phis_lookup_frame >>
  qexists `ps` >> simp[] >> rpt strip_tac >>
  metis_tac[phi_single_origin_block_frame, phi_prefix_mem]
QED
