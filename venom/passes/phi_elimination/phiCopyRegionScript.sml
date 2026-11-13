(* Static copy regions extracted from PHI origin computations. *)
Theory phiCopyRegion
Ancestors
  phiOrigins phiDefs dfgAnalysisProps venomWfProps venomWf venomInst pred_set list

Theorem dfg_build_function_lookup_correct:
  !fn v inst.
    dfg_lookup (dfg_build_function fn) v = SOME inst
    ==>
    inst.inst_outputs = [v] /\ MEM inst (fn_insts fn)
Proof
  rpt strip_tac >>
  drule dfg_lookup_implies_get_def >> strip_tac >>
  drule dfg_build_function_correct >> simp[]
QED

Definition copy_region_def:
  copy_region fn S E <=>
    FINITE S /\
    !v. v IN S ==>
      ?i. MEM i (fn_insts fn) /\ i.inst_outputs = [v] /\
          ((i.inst_opcode = PHI /\
            set (phi_var_operands i.inst_operands) SUBSET S UNION E) \/
           (i.inst_opcode = ASSIGN /\
            ?u. assign_var_operand i = SOME u /\ u IN S UNION E))
End

Definition visited_copy_outputs_def:
  visited_copy_outputs fn V =
    {v | ?i. MEM i (fn_insts fn) /\
             (i.inst_opcode = PHI \/ i.inst_opcode = ASSIGN) /\
             i.inst_id IN V /\ MEM v i.inst_outputs}
End

Theorem copy_region_empty:
  !fn E. copy_region fn {} E
Proof
  simp[copy_region_def]
QED

Theorem copy_region_weaken:
  !fn S E F. copy_region fn S E /\ E SUBSET F ==>
    copy_region fn S F
Proof
  rw[copy_region_def, SUBSET_DEF] >> metis_tac[IN_UNION]
QED

Theorem copy_region_union:
  !fn A B E F. copy_region fn A E /\ copy_region fn B F ==>
    copy_region fn (A UNION B) (E UNION F)
Proof
  rw[copy_region_def, SUBSET_DEF] >> metis_tac[IN_UNION]
QED

Theorem copy_region_absorb:
  !fn S E v i.
    copy_region fn S (v INSERT E) /\
    MEM i (fn_insts fn) /\ i.inst_outputs = [v] /\
    ((i.inst_opcode = PHI /\
      set (phi_var_operands i.inst_operands) SUBSET (v INSERT S) UNION E) \/
     (i.inst_opcode = ASSIGN /\
      ?u. assign_var_operand i = SOME u /\ u IN (v INSERT S) UNION E)) ==>
    copy_region fn (v INSERT S) E
Proof
  rw[copy_region_def, SUBSET_DEF] >> metis_tac[IN_UNION, IN_INSERT]
QED

Theorem copy_region_remove_exits:
  !fn S E. copy_region fn S E ==> copy_region fn (S DIFF E) E
Proof
  rw[copy_region_def, SUBSET_DEF] >> metis_tac[IN_UNION, IN_DIFF]
QED

Theorem visited_copy_outputs_empty:
  !fn. visited_copy_outputs fn {} = {}
Proof
  simp[visited_copy_outputs_def, EXTENSION]
QED

Theorem visited_copy_outputs_insert:
  !fn i V.
    wf_function fn /\ MEM i (fn_insts fn) ==>
    visited_copy_outputs fn (i.inst_id INSERT V) SUBSET
      visited_copy_outputs fn V UNION
      (if i.inst_opcode = PHI \/ i.inst_opcode = ASSIGN
       then set i.inst_outputs else {})
Proof
  rpt gen_tac >> strip_tac >>
  `!bbs. MAP (\j. j.inst_id) (fn_insts_blocks bbs) =
    FLAT (MAP (\bb. MAP (\j. j.inst_id) bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  `ALL_DISTINCT (MAP (\j. j.inst_id) (fn_insts fn))` by
    gvs[wf_function_def, fn_inst_ids_distinct_def, fn_insts_def] >>
  `!j. MEM j (fn_insts fn) /\ j.inst_id = i.inst_id ==> j = i` by
    (rpt strip_tac >> gvs[MEM_EL] >>
     `EL n (MAP (\j. j.inst_id) (fn_insts fn)) =
      EL n' (MAP (\j. j.inst_id) (fn_insts fn))` by simp[EL_MAP] >>
     `n = n'` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >>
     gvs[]) >>
  Cases_on `i.inst_opcode = PHI` >> Cases_on `i.inst_opcode = ASSIGN` >>
  simp[visited_copy_outputs_def, SUBSET_DEF, IN_UNION, GSPECIFICATION] >>
  metis_tac[]
QED

Theorem get_origins_copy_region:
  (!dfg V vars fn.
    wf_function fn /\ dfg = dfg_build_function fn ==>
    ?S. copy_region fn S
          (get_origins_list dfg V vars UNION visited_copy_outputs fn V) /\
        set vars SUBSET
          S UNION get_origins_list dfg V vars UNION visited_copy_outputs fn V) /\
  (!dfg V i fn v.
    wf_function fn /\ dfg = dfg_build_function fn /\
    MEM i (fn_insts fn) /\ i.inst_outputs = [v] ==>
    ?S. copy_region fn S
          (get_origins dfg V i UNION visited_copy_outputs fn V) /\
        v IN S UNION get_origins dfg V i UNION visited_copy_outputs fn V)
Proof
  ho_match_mp_tac get_origins_ind >> rpt conj_tac
  >- (rpt strip_tac >> qexists_tac `{}` >>
      simp[get_origins_def, copy_region_empty])
  >- (rpt strip_tac >> gvs[] >>
      Cases_on `dfg_lookup (dfg_build_function fn) v` >> gvs[]
      >- (first_x_assum (qspec_then `fn` mp_tac) >> simp[] >>
          disch_then (qx_choose_then `region` strip_assume_tac) >>
          qexists_tac `region` >> once_rewrite_tac[get_origins_def] >> simp[] >>
          conj_tac >- (irule copy_region_weaken >>
            qexists_tac `get_origins_list (dfg_build_function fn) V vars UNION
                         visited_copy_outputs fn V` >> simp[SUBSET_DEF]) >>
          gvs[SUBSET_DEF] >> metis_tac[]) >>
      rename1 `dfg_lookup _ v = SOME src` >>
      drule dfg_build_function_lookup_correct >> strip_tac >>
      qpat_x_assum `!fn v. _` (qspecl_then [`fn`, `v`] mp_tac) >> simp[] >>
      disch_then (qx_choose_then `A` (CONJUNCTS_THEN assume_tac)) >>
      first_x_assum (qspec_then `fn` mp_tac) >> simp[] >>
      disch_then (qx_choose_then `B` strip_assume_tac) >>
      qexists_tac `A UNION B` >> once_rewrite_tac[get_origins_def] >> simp[] >>
      conj_tac >- (irule copy_region_weaken >>
        qexists_tac `(get_origins (dfg_build_function fn) V src UNION
                        visited_copy_outputs fn V) UNION
                     (get_origins_list (dfg_build_function fn) V vars UNION
                        visited_copy_outputs fn V)` >>
        conj_tac >- (simp[SUBSET_DEF] >> metis_tac[]) >>
        irule copy_region_union >> simp[]) >>
      gvs[SUBSET_DEF] >> metis_tac[]) >>
  suspend "instruction"
QED

Resume get_origins_copy_region[instruction]:
  rpt strip_tac >> gvs[] >>
  drule_all visited_copy_outputs_insert >> disch_tac >>
  Cases_on `i.inst_opcode = PHI`
  >- (Cases_on `i.inst_id IN V`
      >- (qexists_tac `{}` >>
          once_rewrite_tac[get_origins_def] >>
          simp[copy_region_empty, visited_copy_outputs_def] >>
          metis_tac[MEM]) >>
      Cases_on `CARD (get_origins_list (dfg_build_function fn)
                  (i.inst_id INSERT V) (phi_var_operands i.inst_operands)) > 1`
      >- (qexists_tac `{}` >> once_rewrite_tac[get_origins_def] >>
          simp[copy_region_empty]) >>
      gvs[] >> first_x_assum (qspec_then `fn` mp_tac) >> simp[] >>
      disch_then (qx_choose_then `region` (CONJUNCTS_THEN assume_tac)) >>
      qexists_tac `v INSERT region` >>
      once_rewrite_tac[get_origins_def] >> simp[] >>
      irule copy_region_absorb >>
      conj_tac >- (qexists_tac `i` >> simp[] >>
                   gvs[SUBSET_DEF] >> metis_tac[]) >>
      irule copy_region_weaken >> goal_assum (drule_at Any) >>
      gvs[SUBSET_DEF] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = ASSIGN`
  >- (Cases_on `i.inst_id IN V`
      >- (qexists_tac `{}` >> once_rewrite_tac[get_origins_def] >>
          simp[copy_region_empty, visited_copy_outputs_def] >>
          metis_tac[MEM]) >>
      Cases_on `assign_var_operand i`
      >- (qexists_tac `{}` >> once_rewrite_tac[get_origins_def] >>
          simp[copy_region_empty]) >>
      rename1 `assign_var_operand i = SOME u` >>
      Cases_on `dfg_lookup (dfg_build_function fn) u`
      >- (qexists_tac `{v}` >> once_rewrite_tac[get_origins_def] >> simp[] >>
          simp[copy_region_def] >> qexists_tac `i` >> simp[]) >>
      rename1 `dfg_lookup _ u = SOME src` >>
      drule dfg_build_function_lookup_correct >> strip_tac >>
      qpat_x_assum `!v' i'. _` (qspecl_then [`u`, `src`] mp_tac) >> simp[] >>
      disch_then (qspec_then `fn` mp_tac) >> simp[] >>
      disch_then (qx_choose_then `region` (CONJUNCTS_THEN assume_tac)) >>
      qexists_tac `v INSERT region` >>
      once_rewrite_tac[get_origins_def] >> simp[] >>
      irule copy_region_absorb >>
      conj_tac >- (qexists_tac `i` >> simp[] >>
                   gvs[SUBSET_DEF] >> metis_tac[]) >>
      irule copy_region_weaken >> goal_assum (drule_at Any) >>
      gvs[SUBSET_DEF] >> metis_tac[]) >>
  qexists_tac `{}` >> once_rewrite_tac[get_origins_def] >>
  simp[copy_region_empty]
QED

Finalise get_origins_copy_region

Theorem phi_single_origin_copy_region:
  !fn i root.
    wf_function fn /\ MEM i (fn_insts fn) /\
    phi_single_origin (dfg_build_function fn) i = SOME root ==>
    ?out S. i.inst_outputs = [out] /\ out IN S /\
            root NOTIN S /\ copy_region fn S {root}
Proof
  rpt strip_tac >> drule phi_single_origin_boundary >> strip_tac >>
  drule_at (Pos last) (CONJUNCT2 get_origins_copy_region) >>
  disch_then (qspecl_then [`dfg_build_function fn`, `{}`, `fn`] mp_tac) >>
  gvs[GSYM compute_origins_def, visited_copy_outputs_empty] >>
  disch_then (qx_choose_then `region` (CONJUNCTS_THEN assume_tac)) >>
  qexists_tac `region DIFF {root}` >>
  simp[] >> irule copy_region_remove_exits >> simp[]
QED

(* Unique SSA definitions let region certificates describe encountered writes. *)
Theorem copy_region_inst_inputs:
  wf_ssa fn /\ copy_region fn region exits /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  MEM v inst.inst_outputs /\ v IN region ==>
  inst.inst_outputs = [v] /\
  ((inst.inst_opcode = PHI /\
    set (phi_var_operands inst.inst_operands) SUBSET region UNION exits) \/
   (inst.inst_opcode = ASSIGN /\
    ?u. assign_var_operand inst = SOME u /\ u IN region UNION exits))
Proof
  strip_tac >>
  `MEM inst (fn_insts_blocks fn.fn_blocks)` by
    metis_tac[fmp_fn_insts_blocks_intro] >>
  qpat_x_assum `copy_region _ _ _` mp_tac >>
  simp[copy_region_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `inst = i` by
    (gvs[wf_ssa_def, fn_insts_def] >> metis_tac[ssa_outputs_same_inst, MEM]) >>
  gvs[]
QED

Theorem phi_var_operands_pairs[local]:
  !ops. phi_var_operands ops = MAP SND (phi_pairs ops)
Proof
  recInduct phi_pairs_ind >> simp[phi_pairs_def, phi_var_operands_def]
QED

Theorem copy_region_input_on_path[local]:
  wf_function fn /\ wf_ssa fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  copy_region fn region exits /\
  is_fn_path fn path /\ path <> [] /\
  fn_entry_label fn = SOME (HD path) /\
  MEM bb fn.fn_blocks /\ LAST path = bb.bb_label /\
  j < LENGTH bb.bb_instructions /\
  MEM v (EL j bb.bb_instructions).inst_outputs /\ v IN region ==>
  ?u. u IN region UNION exits /\
    ((?k rb ri. k < LENGTH path - 1 /\ MEM rb fn.fn_blocks /\
       rb.bb_label = EL k path /\ MEM ri rb.bb_instructions /\
       MEM u ri.inst_outputs) \/
     ((EL j bb.bb_instructions).inst_opcode <> PHI /\
      ?k. k < j /\ MEM u (EL k bb.bb_instructions).inst_outputs))
Proof
  strip_tac >>
  `MEM (EL j bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  drule_all copy_region_inst_inputs >> strip_tac
  >- suspend "phi"
  >> suspend "assign"
QED

Resume copy_region_input_on_path[assign]:
  `MEM (Var u) (EL j bb.bb_instructions).inst_operands` by
    gvs[assign_var_operand_def, AllCaseEqs()] >>
  drule_all wf_ssa_defs_reach_uses >>
  simp[fn_defs_reach_uses_def] >>
  disch_then (qspecl_then [`bb`, `EL j bb.bb_instructions`] mp_tac) >> simp[] >>
  disch_then (qspec_then `u` mp_tac) >> simp[] >>
  simp[def_on_all_paths_def] >>
  disch_then (qspec_then `path` mp_tac) >> simp[] >>
  strip_tac
  >- (qexists_tac `u` >> gvs[] >> metis_tac[]) >>
  `j' = j` by
    (irule ssa_form_no_dup_in_block >>
     qexistsl_tac [`bb`, `fn`, `v`] >> gvs[wf_ssa_def]) >>
  qexists_tac `u` >> gvs[] >> metis_tac[]
QED

Resume copy_region_input_on_path[phi]:
  Cases_on `path` using SNOC_CASES >- gvs[] >>
  rename1 `is_fn_path fn (SNOC lbl pre)` >>
  Cases_on `pre = []`
  >- (gvs[fn_entry_label_def, entry_block_def] >>
      Cases_on `fn.fn_blocks` >> gvs[wf_function_def, fn_has_entry_def] >>
      gvs[EVERY_EL, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `is_fn_path fn pre /\ fn_cfg_edge fn (LAST pre) lbl` by
    metis_tac[is_fn_path_init, is_fn_path_last_edge] >>
  `phi_edge_uses_wf fn bb (EL j bb.bb_instructions)` by
    (gvs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]) >>
  gvs[phi_edge_uses_wf_def] >>
  PairCases_on `p` >> gvs[] >>
  `p1 IN region UNION exits` by
    (qpat_x_assum `_ SUBSET _` mp_tac >>
     simp[SUBSET_DEF, phi_var_operands_pairs, MEM_MAP] >> metis_tac[pairTheory.SND]) >>
  qpat_x_assum `!pred v'. _` drule >> strip_tac >>
  drule_all def_available_on_all_paths >>
  simp[def_on_all_paths_def] >>
  disch_then (qspec_then `pre` mp_tac) >>
  `HD (SNOC bb.bb_label pre) = HD pre` by (Cases_on `pre` >> gvs[SNOC]) >>
  simp[] >> strip_tac
  >- (qexists_tac `p1` >> conj_tac >- gvs[] >>
      qexistsl_tac [`k`, `def_bb`, `def_inst`] >> simp[EL_SNOC] >>
      decide_tac) >>
  qexists_tac `p1` >> conj_tac >- gvs[] >>
  qexistsl_tac [`LENGTH pre - 1`, `pred_bb`, `EL i pred_bb.bb_instructions`] >>
  simp[EL_MEM, EL_SNOC] >>
  `LENGTH pre - 1 < LENGTH pre` by (Cases_on `pre` >> gvs[]) >>
  simp[EL_SNOC, LAST_EL, arithmeticTheory.PRE_SUB1]
QED

Finalise copy_region_input_on_path

Theorem copy_region_root_on_path:
  !path j fn region root bb v.
  wf_function fn /\ wf_ssa fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  copy_region fn region {root} /\ root NOTIN region /\
  is_fn_path fn path /\ path <> [] /\
  fn_entry_label fn = SOME (HD path) /\
  MEM bb fn.fn_blocks /\ LAST path = bb.bb_label /\
  j < LENGTH bb.bb_instructions /\
  MEM v (EL j bb.bb_instructions).inst_outputs /\ v IN region ==>
    ((?k rb ri. k < LENGTH path - 1 /\ MEM rb fn.fn_blocks /\
       rb.bb_label = EL k path /\ MEM ri rb.bb_instructions /\
       MEM root ri.inst_outputs) \/
     ((EL j bb.bb_instructions).inst_opcode <> PHI /\
      ?k. k < j /\ MEM root (EL k bb.bb_instructions).inst_outputs))
Proof
  measureInduct_on `LENGTH path` >> completeInduct_on `j` >>
  rpt strip_tac >> drule_all copy_region_input_on_path >>
  disch_then (qx_choose_then `u` (CONJUNCTS_THEN assume_tac)) >>
  Cases_on `u = root` >- (gvs[] >> metis_tac[]) >>
  `u IN region` by gvs[] >>
  qpat_x_assum `(?k rb ri. _) \/ _` strip_assume_tac
  >- suspend "earlier_block"
  >> suspend "earlier_inst"
QED

Resume copy_region_root_on_path[earlier_block]:
  `k < LENGTH path` by decide_tac >>
  drule_all is_fn_path_prefix_at >> strip_tac >>
  `?n. n < LENGTH rb.bb_instructions /\ ri = EL n rb.bb_instructions`
    by metis_tac[MEM_EL] >>
  `MEM u (EL n rb.bb_instructions).inst_outputs` by metis_tac[] >>
  `LENGTH (TAKE (SUC k) path) < LENGTH path` by (simp[] >> decide_tac) >>
  `fn_entry_label fn = SOME (HD (TAKE (SUC k) path))` by simp[] >>
  `LAST (TAKE (SUC k) path) = rb.bb_label` by metis_tac[] >>
  first_x_assum (qspec_then `TAKE (SUC k) path` mp_tac) >>
  disch_then drule_all >> strip_tac
  >- (disj1_tac >>
      `k' < SUC k` by decide_tac >>
      gvs[EL_TAKE] >> qexistsl [`k'`, `rb'`, `ri'`] >> simp[] >> decide_tac) >>
  disj1_tac >> qexistsl [`k`, `rb`, `EL k' rb.bb_instructions`] >>
  simp[] >> metis_tac[MEM_EL, arithmeticTheory.LESS_TRANS]
QED

Resume copy_region_root_on_path[earlier_inst]:
  `k < LENGTH bb.bb_instructions` by decide_tac >>
  qpat_x_assum `!m. m < j ==> _` (qspec_then `k` mp_tac) >>
  disch_then drule_all >> strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >> simp[] >> qexists `k'` >> simp[] >> decide_tac
QED

Finalise copy_region_root_on_path

Theorem phi_single_origin_reachable:
  !fn bb inst r.
    wf_ssa fn /\ MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    phi_single_origin (dfg_build_function fn) inst = SOME r ==>
    fn_reachable fn bb.bb_label
Proof
  rpt strip_tac >>
  `inst.inst_opcode = PHI` by
    metis_tac[phi_single_origin_is_phi, is_phi_inst_def] >>
  `compute_origins (dfg_build_function fn) inst = {r}` by
    metis_tac[phi_single_origin_boundary] >>
  `phi_var_operands inst.inst_operands <> []` by
    (strip_tac >>
     fs[compute_origins_def, Once (cj 3 get_origins_def)] >>
     gvs[cj 1 get_origins_def]) >>
  `phi_pairs inst.inst_operands <> []` by
    metis_tac[phi_var_operands_pairs, listTheory.MAP] >>
  `?p v. MEM (p,v) (phi_pairs inst.inst_operands)` by
    (Cases_on `phi_pairs inst.inst_operands` >> gvs[] >>
     Cases_on `h` >> metis_tac[MEM]) >>
  `phi_edge_uses_wf fn bb inst` by
    (fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]) >>
  `?pb. MEM pb fn.fn_blocks /\ fn_cfg_edge fn pb.bb_label bb.bb_label /\
         def_available_at fn pb NONE v` by
    metis_tac[phi_edge_uses_wf_def] >>
  `fn_reachable fn pb.bb_label` by
    fs[def_available_at_def, fn_dominates_def] >>
  metis_tac[venomExecProofsTheory.fn_reachable_step]
QED

Theorem copy_region_root_on_all_paths:
  wf_function fn /\ wf_ssa fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  copy_region fn region {root} /\ root NOTIN region /\
  MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\
  MEM v i.inst_outputs /\ v IN region ==>
  def_on_all_paths fn bb (SOME i) root
Proof
  strip_tac >>
  `?j. j < LENGTH bb.bb_instructions /\ i = EL j bb.bb_instructions`
    by metis_tac[MEM_EL] >>
  simp[def_on_all_paths_def] >> rpt strip_tac >>
  `fn_entry_label fn = SOME (HD path)` by metis_tac[] >>
  `MEM v (EL j bb.bb_instructions).inst_outputs` by metis_tac[] >>
  drule_all copy_region_root_on_path >> strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >> qexists `k` >> simp[] >>
  qexists `j` >> simp[] >> decide_tac
QED

Theorem copy_region_root_available:
  wf_function fn /\ wf_ssa fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  copy_region fn region {root} /\ root NOTIN region /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  MEM i bb.bb_instructions /\ MEM v i.inst_outputs /\ v IN region ==>
  def_available_at fn bb (SOME i) root
Proof
  strip_tac >> drule_all copy_region_root_on_all_paths >> strip_tac >>
  irule def_on_all_paths_available >> fs[wf_ssa_def] >> metis_tac[]
QED

Theorem copy_region_phi_root_strict_dominance:
  wf_function fn /\ wf_ssa fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  copy_region fn region {root} /\ root NOTIN region /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  MEM i bb.bb_instructions /\ MEM v i.inst_outputs /\ v IN region /\
  i.inst_opcode = PHI ==>
  ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM root di.inst_outputs /\ fn_dominates fn db.bb_label bb.bb_label /\
    db.bb_label <> bb.bb_label
Proof
  strip_tac >>
  `?j. j < LENGTH bb.bb_instructions /\ i = EL j bb.bb_instructions`
    by metis_tac[MEM_EL] >>
  `MEM v (EL j bb.bb_instructions).inst_outputs` by metis_tac[] >>
  `!path. is_fn_path fn path /\ path <> [] /\
      fn_entry_label fn = SOME (HD path) /\ LAST path = bb.bb_label ==>
      ?k rb ri. k < LENGTH path - 1 /\ MEM rb fn.fn_blocks /\
        rb.bb_label = EL k path /\ MEM ri rb.bb_instructions /\
        MEM root ri.inst_outputs` by
    (rpt strip_tac >> drule_all copy_region_root_on_path >>
     gvs[] >> metis_tac[]) >>
  `def_on_all_paths fn bb (SOME i) root` by
    (irule copy_region_root_on_all_paths >> metis_tac[]) >>
  drule_all def_on_all_paths_first_witness >> strip_tac >>
  `ssa_form fn` by fs[wf_ssa_def] >>
  `fn_dominates fn db.bb_label bb.bb_label` by
    (irule def_on_all_paths_dominating_witness >> metis_tac[]) >>
  qexistsl [`db`, `di`] >> simp[] >>
  fs[fn_reachable_def] >> drule venomExecProofsTheory.rtc_to_fn_path >> strip_tac >>
  drule_all is_fn_path_first_arrival >> strip_tac >>
  qpat_x_assum `!path. _` (qspec_then `pre ++ [bb.bb_label]` mp_tac) >>
  simp[] >> strip_tac >>
  `ri = di` by metis_tac[ssa_form_output_unique] >>
  `rb = db` by metis_tac[wf_function_instruction_block] >>
  `MEM rb.bb_label pre` by
    (simp[MEM_EL] >> qexists `k` >> gvs[rich_listTheory.EL_APPEND1]) >>
  metis_tac[]
QED

Theorem phi_single_origin_strict_dominance:
  wf_function fn /\ wf_ssa fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
  phi_single_origin (dfg_build_function fn) i = SOME root ==>
  ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM root di.inst_outputs /\ fn_dominates fn db.bb_label bb.bb_label /\
    db.bb_label <> bb.bb_label
Proof
  strip_tac >>
  `MEM i (fn_insts fn)` by metis_tac[fmp_fn_insts_blocks_intro, fn_insts_def] >>
  drule_all phi_single_origin_copy_region >> strip_tac >>
  irule copy_region_phi_root_strict_dominance >> simp[] >>
  qexistsl [`i`, `S'`, `out`] >> simp[]
QED

Theorem copy_region_root_output_disjoint:
  wf_ssa fn /\ copy_region fn region {root} /\ root NOTIN region /\
  MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\
  MEM root i.inst_outputs /\ v IN region ==>
  ~MEM v i.inst_outputs
Proof
  strip_tac >> strip_tac >>
  drule_all copy_region_inst_inputs >> strip_tac >> gvs[]
QED

Theorem copy_region_no_strict_dominator_at_root:
  wf_function fn /\ wf_ssa fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  copy_region fn region {root} /\ root NOTIN region /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  MEM i bb.bb_instructions /\ MEM root i.inst_outputs /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
  MEM v di.inst_outputs /\ v IN region /\
  fn_dominates fn db.bb_label bb.bb_label ==>
  db.bb_label = bb.bb_label
Proof
  strip_tac >> spose_not_then assume_tac >>
  `ssa_form fn` by fs[wf_ssa_def] >>
  fs[fn_reachable_def] >>
  drule venomExecProofsTheory.rtc_to_fn_path >> strip_tac >>
  drule_all is_fn_path_first_arrival >> strip_tac >>
  `MEM db.bb_label pre` by
    (qpat_x_assum `fn_dominates _ _ _` mp_tac >>
     simp[fn_dominates_def] >> strip_tac >>
     first_x_assum (qspec_then `pre ++ [bb.bb_label]` mp_tac) >> simp[]) >>
  `?k. k < LENGTH pre /\ EL k pre = db.bb_label` by metis_tac[MEM_EL] >>
  `k < LENGTH (pre ++ [bb.bb_label])` by simp[] >>
  `EL k (pre ++ [bb.bb_label]) = db.bb_label` by
    simp[rich_listTheory.EL_APPEND1] >>
  drule_all is_fn_path_prefix_at >> strip_tac >>
  `?j. j < LENGTH db.bb_instructions /\ di = EL j db.bb_instructions`
    by metis_tac[MEM_EL] >>
  `MEM v (EL j db.bb_instructions).inst_outputs` by metis_tac[] >>
  `fn_entry_label fn = SOME (HD (TAKE (SUC k) (pre ++ [bb.bb_label])))`
    by simp[] >>
  `LAST (TAKE (SUC k) (pre ++ [bb.bb_label])) = db.bb_label` by metis_tac[] >>
  drule_all copy_region_root_on_path >> strip_tac
  >- suspend "earlier_block"
  >> suspend "same_block"
QED

Resume copy_region_no_strict_dominator_at_root[earlier_block]:
  `ri = i` by metis_tac[ssa_form_output_unique] >>
  `rb = bb` by metis_tac[wf_function_instruction_block] >>
  `k' < LENGTH pre` by (gvs[] >> decide_tac) >>
  `EL k' pre = bb.bb_label` by
    (gvs[EL_TAKE, rich_listTheory.EL_APPEND1]) >>
  metis_tac[MEM_EL]
QED

Resume copy_region_no_strict_dominator_at_root[same_block]:
  `MEM (EL k' db.bb_instructions) db.bb_instructions` by
    (simp[EL_MEM] >> decide_tac) >>
  `EL k' db.bb_instructions = i` by metis_tac[ssa_form_output_unique] >>
  metis_tac[wf_function_instruction_block]
QED

Finalise copy_region_no_strict_dominator_at_root

Theorem copy_region_unavailable_at_root:
  wf_function fn /\ wf_ssa fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  copy_region fn region {root} /\ root NOTIN region /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  MEM i bb.bb_instructions /\ MEM root i.inst_outputs /\ v IN region ==>
  ~def_available_at fn bb (SOME i) v
Proof
  strip_tac >> strip_tac >>
  `ssa_form fn` by fs[wf_ssa_def] >>
  gvs[def_available_at_def] >>
  `def_bb.bb_label = bb.bb_label` by
    (irule copy_region_no_strict_dominator_at_root >> metis_tac[]) >>
  `def_bb = bb` by metis_tac[venomExecProofsTheory.same_label_same_block] >>
  gvs[] >>
  fs[fn_reachable_def] >>
  drule venomExecProofsTheory.rtc_to_fn_path >> strip_tac >>
  drule_all is_fn_path_first_arrival >> strip_tac >>
  `i' < LENGTH bb.bb_instructions` by decide_tac >>
  `MEM v (EL i' bb.bb_instructions).inst_outputs` by metis_tac[] >>
  `fn_entry_label fn = SOME (HD (pre ++ [bb.bb_label]))` by simp[] >>
  `pre ++ [bb.bb_label] <> []` by simp[] >>
  `LAST (pre ++ [bb.bb_label]) = bb.bb_label` by simp[] >>
  drule_all copy_region_root_on_path >> strip_tac
  >- suspend "earlier_block"
  >> suspend "earlier_inst"
QED

Resume copy_region_unavailable_at_root[earlier_block]:
  `ri = EL j bb.bb_instructions` by metis_tac[ssa_form_output_unique] >>
  `rb = bb` by metis_tac[wf_function_instruction_block] >>
  `k < LENGTH pre` by gvs[] >>
  `EL k pre = bb.bb_label` by gvs[rich_listTheory.EL_APPEND1] >>
  metis_tac[MEM_EL]
QED

Resume copy_region_unavailable_at_root[earlier_inst]:
  `k < LENGTH bb.bb_instructions` by decide_tac >>
  `k = j` by
    (irule ssa_form_no_dup_in_block >>
     qexistsl [`bb`, `fn`, `root`] >> simp[]) >>
  decide_tac
QED

Finalise copy_region_unavailable_at_root
