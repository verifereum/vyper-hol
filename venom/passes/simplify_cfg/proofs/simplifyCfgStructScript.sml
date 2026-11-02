Theory simplifyCfgStruct
Ancestors
  simplifyCfgLabelProps simplifyCfgCompute simplifyCfgDefs cfgWf venomWf venomInst
  cfgTransform list rich_list sorting

(* Boundary probes: wf_function intentionally does not require inst_wf. *)
Definition struct_cycle_def:
  struct_cycle = mk_raw_function "cycle"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 JNZ [Var "c"; Label "back"; Label "exit"] []] |>;
     <| bb_label := "back"; bb_instructions :=
        [mk_inst 1 NOP [] []; mk_inst 2 JMP [Label "entry"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 3 STOP [] []] |>]
End

Definition struct_bypass_def:
  struct_bypass = mk_raw_function "bypass"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 JNZ [Var "c"; Label "back"; Label "exit"] []] |>;
     <| bb_label := "back"; bb_instructions :=
        [mk_inst 1 JMP [Label "entry"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 2 STOP [] []] |>]
End

Definition struct_phi_def:
  struct_phi = mk_raw_function "phi"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 PHI [] ["x"];
         mk_inst 1 PHI [Var "bad"] ["y"];
         mk_inst 2 PHI [Var "bad"; Var "w"] ["z"];
         mk_inst 3 STOP [] []] |>]
End

Theorem struct_inputs_wf:
  wf_function struct_cycle /\ wf_function struct_bypass /\
  wf_function struct_phi
Proof
  EVAL_TAC
QED

Theorem struct_outputs_wf:
  wf_function (simplify_cfg_fn struct_cycle) /\
  wf_function (simplify_cfg_fn struct_bypass) /\
  wf_function (simplify_cfg_fn struct_phi)
Proof
  EVAL_TAC
QED

Theorem struct_outputs_ssa:
  ssa_form (simplify_cfg_fn struct_cycle) /\
  ssa_form (simplify_cfg_fn struct_bypass) /\
  ssa_form (simplify_cfg_fn struct_phi)
Proof
  EVAL_TAC
QED

Theorem struct_cycle_blocks:
  (simplify_cfg_fn struct_cycle).fn_blocks =
    [<| bb_label := "back"; bb_instructions :=
        [mk_inst 1 NOP [] [];
         mk_inst 0 JNZ [Var "c"; Label "back"; Label "exit"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 3 STOP [] []] |>]
Proof
  EVAL_TAC
QED

Theorem struct_bypass_blocks:
  (simplify_cfg_fn struct_bypass).fn_blocks =
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 JNZ [Var "c"; Label "entry"; Label "exit"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 2 STOP [] []] |>]
Proof
  EVAL_TAC
QED

Theorem struct_phi_blocks:
  (simplify_cfg_fn struct_phi).fn_blocks =
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 1 PHI [Var "bad"] ["y"];
         mk_inst 0 NOP [] [];
         mk_inst 2 ASSIGN [Var "w"] ["z"];
         mk_inst 3 STOP [] []] |>]
Proof
  EVAL_TAC
QED

Theorem struct_outputs_reachable:
  all_reachable (simplify_cfg_fn struct_cycle) /\
  all_reachable (simplify_cfg_fn struct_bypass) /\
  all_reachable (simplify_cfg_fn struct_phi)
Proof
  simp[all_reachable_def, fn_reachable_def, fn_entry_label_def,
       entry_block_def, struct_cycle_blocks, struct_bypass_blocks,
       struct_phi_blocks] >>
  rpt conj_tac >> rpt strip_tac >> gvs[] >>
  irule relationTheory.RTC_SINGLE >>
  simp[fn_cfg_edge_def, struct_cycle_blocks, struct_bypass_blocks,
       bb_succs_def, mk_inst_def, get_successors_def,
       RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC
QED

Theorem fix_phi_inst_non_phi:
  inst.inst_opcode <> PHI ==> fix_phi_inst actual_preds inst = inst
Proof
  simp[fix_phi_inst_def]
QED

Theorem fix_phi_inst_id:
  (fix_phi_inst actual_preds inst).inst_id = inst.inst_id
Proof
  simp[fix_phi_inst_def] >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  Cases_on `filter_phi_ops actual_preds inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[]
QED

Theorem fix_phi_inst_outputs:
  (fix_phi_inst actual_preds inst).inst_outputs = [] \/
  (fix_phi_inst actual_preds inst).inst_outputs = inst.inst_outputs
Proof
  simp[fix_phi_inst_def] >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  Cases_on `filter_phi_ops actual_preds inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[]
QED

Theorem fix_phi_inst_terminator:
  is_terminator (fix_phi_inst actual_preds inst).inst_opcode =
  is_terminator inst.inst_opcode
Proof
  simp[fix_phi_inst_def] >>
  Cases_on `inst.inst_opcode = PHI` >> simp[is_terminator_def] >>
  Cases_on `filter_phi_ops actual_preds inst.inst_operands` >>
  simp[is_terminator_def] >>
  Cases_on `t` >> simp[is_terminator_def] >>
  Cases_on `t'` >> simp[is_terminator_def]
QED

Theorem sublist_flat_map_filter:
  !xs. sublist (FLAT (MAP f (FILTER P xs))) (FLAT (MAP f xs))
Proof
  Induct >- simp[sublist_refl] >>
  gen_tac >> Cases_on `P h` >> simp[]
  >- (irule sublist_append_pair >> simp[sublist_refl]) >>
  irule sublist_trans >> qexists `FLAT (MAP f xs)` >>
  simp[sublist_refl] >>
  metis_tac[sublist_append_pair, sublist_nil, APPEND, sublist_refl]
QED

Theorem fn_insts_projection_blocks:
  !bbs. FLAT (MAP project (fn_insts_blocks bbs)) =
    FLAT (MAP (\bb. FLAT (MAP project bb.bb_instructions)) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

Theorem remove_unreachable_blocks_ssa:
  ssa_form func ==> ssa_form (remove_unreachable_blocks func)
Proof
  simp[remove_unreachable_blocks_def] >>
  Cases_on `fn_entry_label func` >> simp[] >>
  simp[ssa_form_def, fn_insts_def, fn_insts_projection_blocks] >>
  strip_tac >> irule sublist_ALL_DISTINCT >>
  goal_assum (drule_at Any) >> simp[sublist_flat_map_filter]
QED

Theorem remove_unreachable_blocks_ids:
  fn_inst_ids_distinct func ==>
  fn_inst_ids_distinct (remove_unreachable_blocks func)
Proof
  simp[remove_unreachable_blocks_def] >>
  Cases_on `fn_entry_label func` >> simp[] >>
  simp[fn_inst_ids_distinct_def] >>
  strip_tac >> irule sublist_ALL_DISTINCT >>
  goal_assum (drule_at Any) >> simp[sublist_flat_map_filter]
QED

Theorem remove_unreachable_blocks_entry:
  fn_entry_label (remove_unreachable_blocks func) = fn_entry_label func
Proof
  Cases_on `func.fn_blocks` >>
  simp[remove_unreachable_blocks_def, fn_entry_label_def, entry_block_def] >>
  `reachable func h.bb_label` by
    simp[reachable_def, fn_entry_label_def, entry_block_def] >>
  simp[fn_entry_label_def, entry_block_def]
QED

Theorem remove_unreachable_blocks_edge:
  ALL_DISTINCT (fn_labels func) /\ fn_reachable func src /\
  fn_cfg_edge func src dst ==>
  fn_cfg_edge (remove_unreachable_blocks func) src dst
Proof
  rpt strip_tac >>
  `reachable func src` by metis_tac[fn_reachable_iff_reachable] >>
  gvs[fn_cfg_edge_def, remove_unreachable_blocks_def, reachable_def] >>
  qexists `bb` >> simp[MEM_FILTER, reachable_def] >>
  metis_tac[]
QED

Theorem remove_unreachable_blocks_path:
  ALL_DISTINCT (fn_labels func) ==>
  !src dst. RTC (fn_cfg_edge func) src dst ==>
    fn_reachable func src ==>
    RTC (fn_cfg_edge (remove_unreachable_blocks func)) src dst
Proof
  strip_tac >> ho_match_mp_tac relationTheory.RTC_STRONG_INDUCT_RIGHT1 >>
  simp[] >> rpt strip_tac >>
  rename1 `fn_cfg_edge func middle target` >>
  `fn_reachable func middle` by
    (gvs[fn_reachable_def] >>
     irule relationTheory.RTC_TRANS >> goal_assum (drule_at Any) >> simp[]) >>
  irule relationTheory.RTC_TRANS >> qexists `middle` >> conj_tac
  >- metis_tac[] >>
  irule relationTheory.RTC_SINGLE >>
  irule remove_unreachable_blocks_edge >> simp[]
QED

Theorem remove_unreachable_blocks_member:
  wf_function func ==>
  (MEM bb (remove_unreachable_blocks func).fn_blocks <=>
   MEM bb func.fn_blocks /\ fn_reachable func bb.bb_label)
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels func)` by gvs[wf_function_def] >>
  simp[fn_reachable_iff_reachable] >>
  Cases_on `func.fn_blocks` >>
  gvs[wf_function_def, fn_has_entry_def] >>
  `reachable func h.bb_label` by
    simp[reachable_def, fn_entry_label_def, entry_block_def] >>
  simp[remove_unreachable_blocks_def, fn_entry_label_def, entry_block_def,
       MEM_FILTER] >> metis_tac[]
QED

Theorem remove_unreachable_blocks_reachable:
  wf_function func ==> all_reachable (remove_unreachable_blocks func)
Proof
  strip_tac >> simp[all_reachable_def] >> rpt strip_tac >>
  drule remove_unreachable_blocks_member >>
  disch_then (qspec_then `bb` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `fn_reachable func _` mp_tac >>
  simp[fn_reachable_def] >> strip_tac >>
  qexists `entry` >> simp[remove_unreachable_blocks_entry] >>
  irule remove_unreachable_blocks_path >>
  simp[wf_function_def] >> conj_tac
  >- gvs[wf_function_def] >>
  simp[fn_reachable_def]
QED

Theorem remove_unreachable_blocks_closed:
  wf_function func ==> fn_succs_closed (remove_unreachable_blocks func)
Proof
  strip_tac >> simp[fn_succs_closed_def] >> rpt strip_tac >>
  `MEM bb func.fn_blocks /\ fn_reachable func bb.bb_label` by
    metis_tac[remove_unreachable_blocks_member] >>
  `MEM succ (fn_labels func)` by
    metis_tac[wf_function_def, fn_succs_closed_def] >>
  `fn_cfg_edge func bb.bb_label succ` by
    (simp[fn_cfg_edge_def] >> metis_tac[]) >>
  `fn_reachable func succ` by
    (gvs[fn_reachable_def] >>
     irule relationTheory.RTC_TRANS >> qexists `bb.bb_label` >>
     simp[relationTheory.RTC_SINGLE]) >>
  gvs[fn_labels_def, MEM_MAP] >>
  metis_tac[remove_unreachable_blocks_member]
QED

Theorem remove_unreachable_blocks_wf:
  wf_function func ==> wf_function (remove_unreachable_blocks func)
Proof
  strip_tac >>
  `fn_has_entry (remove_unreachable_blocks func)` by
    (Cases_on `func.fn_blocks` >> gvs[wf_function_def, fn_has_entry_def] >>
     `reachable func h.bb_label` by
       simp[reachable_def, fn_entry_label_def, entry_block_def] >>
     simp[fn_has_entry_def, remove_unreachable_blocks_def,
          fn_entry_label_def, entry_block_def]) >>
  simp[wf_function_def] >> rpt conj_tac
  >- metis_tac[wf_function_def, fn_labels_remove_unreachable_all_distinct]
  >- (rpt strip_tac >>
      metis_tac[remove_unreachable_blocks_member, wf_function_def])
  >- metis_tac[remove_unreachable_blocks_closed] >>
  metis_tac[remove_unreachable_blocks_ids, wf_function_def]
QED

Theorem perm_partition:
  PERM (FILTER P xs ++ FILTER (\x. ~P x) xs) xs
Proof
  mp_tac (Q.INST [`R` |-> `\x y. P x`] PERM3_FILTER) >>
  disch_then (qspecl_then [`xs`, `ARB`] mp_tac) >>
  Cases_on `P ARB` >> simp[PERM_SYM, ETA_THM]
QED

Theorem fix_phis_in_block_perm:
  PERM (fix_phis_in_block actual_preds bb).bb_instructions
       (MAP (fix_phi_inst actual_preds) bb.bb_instructions)
Proof
  simp[fix_phis_in_block_def, perm_partition]
QED

Theorem fix_phis_in_block_ids:
  PERM (MAP (\i. i.inst_id)
            (fix_phis_in_block actual_preds bb).bb_instructions)
       (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  `MAP (\i. i.inst_id) bb.bb_instructions =
   MAP (\i. i.inst_id) (MAP (fix_phi_inst actual_preds) bb.bb_instructions)` by
    simp[MAP_MAP_o, combinTheory.o_DEF, fix_phi_inst_id] >>
  pop_assum SUBST1_TAC >>
  irule PERM_MAP >> simp[fix_phis_in_block_perm]
QED

Theorem fix_phi_inst_outputs_sublist:
  sublist (fix_phi_inst actual_preds inst).inst_outputs inst.inst_outputs
Proof
  mp_tac fix_phi_inst_outputs >> strip_tac >>
  simp[sublist_nil, sublist_refl]
QED

Theorem fix_phi_outputs_flat_sublist:
  !xs. sublist
    (FLAT (MAP (\i. (fix_phi_inst actual_preds i).inst_outputs) xs))
    (FLAT (MAP (\i. i.inst_outputs) xs))
Proof
  Induct >> simp[sublist_refl] >> gen_tac >>
  irule sublist_append_pair >> simp[fix_phi_inst_outputs_sublist]
QED
Theorem fix_all_phis_ids:
  fn_inst_ids_distinct func ==> fn_inst_ids_distinct (fix_all_phis func)
Proof
  simp[fn_inst_ids_distinct_def, fix_all_phis_def, MAP_MAP_o,
       combinTheory.o_DEF] >> strip_tac >>
  `PERM
    (FLAT (MAP (\bb. MAP (\i. i.inst_id)
       (fix_phis_in_block (pred_labels func bb.bb_label) bb).bb_instructions)
       func.fn_blocks))
    (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) func.fn_blocks))` by
    (Q.SPEC_TAC (`func.fn_blocks`, `bbs`) >> Induct >> simp[] >>
     gen_tac >> irule PERM_CONG >> simp[fix_phis_in_block_ids]) >>
  metis_tac[ALL_DISTINCT_PERM]
QED

Theorem fix_phi_blocks_outputs_sublist:
  !bbs. sublist
    (FLAT (MAP (\bb. FLAT (MAP (\i.
       (fix_phi_inst (pred_fn bb.bb_label) i).inst_outputs)
       bb.bb_instructions)) bbs))
    (FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs)
       bb.bb_instructions)) bbs))
Proof
  Induct >> simp[sublist_refl] >> gen_tac >>
  irule sublist_append_pair >> simp[fix_phi_outputs_flat_sublist]
QED

Theorem fix_phis_blocks_outputs_distinct:
  ALL_DISTINCT (FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs)
    bb.bb_instructions)) bbs)) ==>
  ALL_DISTINCT (FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs)
    (fix_phis_in_block (pred_fn bb.bb_label) bb).bb_instructions)) bbs))
Proof
  strip_tac >>
  `PERM
    (FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs)
       (fix_phis_in_block (pred_fn bb.bb_label) bb).bb_instructions)) bbs))
    (FLAT (MAP (\bb. FLAT (MAP (\i.
       (fix_phi_inst (pred_fn bb.bb_label) i).inst_outputs)
       bb.bb_instructions)) bbs))` by
    (qid_spec_tac `bbs` >> Induct >> simp[] >> gen_tac >>
     irule PERM_CONG >> conj_tac
     >- (rewrite_tac[GSYM combinTheory.o_DEF, GSYM MAP_MAP_o] >>
         pure_rewrite_tac[ETA_THM] >>
         irule PERM_FLAT >> irule PERM_MAP >> simp[fix_phis_in_block_perm]) >>
     simp[]) >>
  `ALL_DISTINCT
    (FLAT (MAP (\bb. FLAT (MAP (\i.
       (fix_phi_inst (pred_fn bb.bb_label) i).inst_outputs)
       bb.bb_instructions)) bbs))` by
    (irule sublist_ALL_DISTINCT >> goal_assum (drule_at Any) >>
     simp[fix_phi_blocks_outputs_sublist]) >>
  metis_tac[ALL_DISTINCT_PERM]
QED

Theorem fix_all_phis_ssa:
  ssa_form func ==> ssa_form (fix_all_phis func)
Proof
  simp[ssa_form_def, fn_insts_def, fn_insts_projection_blocks,
       fix_all_phis_def, MAP_MAP_o, combinTheory.o_DEF] >>
  strip_tac >> irule fix_phis_blocks_outputs_distinct >> simp[]
QED

Theorem bb_well_formed_front_nonterminators:
  bb_well_formed bb ==>
  EVERY (\inst. ~is_terminator inst.inst_opcode) (FRONT bb.bb_instructions)
Proof
  simp[bb_well_formed_def, EVERY_EL] >> rpt strip_tac >>
  rename1 `is_terminator (EL i (FRONT bb.bb_instructions)).inst_opcode` >>
  `i < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[LENGTH_FRONT]) >>
  `EL i (FRONT bb.bb_instructions) = EL i bb.bb_instructions` by
    (irule EL_FRONT >> gvs[LENGTH_FRONT] >>
     Cases_on `bb.bb_instructions` >> gvs[]) >>
  gvs[] >>
  qpat_x_assum `!i. _ /\ is_terminator _ ==> _` drule >>
  gvs[LENGTH_FRONT]
QED

Theorem phi_partition_prefix:
  EVERY (\inst. inst.inst_opcode = PHI) phis /\
  EVERY (\inst. inst.inst_opcode <> PHI) body_insts ==>
  !i j. i < j /\ j < LENGTH (phis ++ body_insts) /\
        (EL j (phis ++ body_insts)).inst_opcode = PHI ==>
        (EL i (phis ++ body_insts)).inst_opcode = PHI
Proof
  simp[EVERY_EL, EL_APPEND_EQN] >> rpt strip_tac >>
  Cases_on `j < LENGTH phis` >> gvs[]
QED

Theorem bb_well_formed_partition:
  EVERY (\inst. ~is_terminator inst.inst_opcode) xs /\
  is_terminator term_inst.inst_opcode ==>
  bb_well_formed (bb with bb_instructions :=
    FILTER (\inst. inst.inst_opcode = PHI) xs ++
    FILTER (\inst. inst.inst_opcode <> PHI) xs ++ [term_inst])
Proof
  strip_tac >>
  `term_inst.inst_opcode <> PHI` by
    (strip_tac >> gvs[is_terminator_def]) >>
  `!i j. i < j /\
    j < LENGTH (FILTER (\inst. inst.inst_opcode = PHI) xs ++
                (FILTER (\inst. inst.inst_opcode <> PHI) xs ++ [term_inst])) /\
    (EL j (FILTER (\inst. inst.inst_opcode = PHI) xs ++
           (FILTER (\inst. inst.inst_opcode <> PHI) xs ++ [term_inst]))).inst_opcode = PHI ==>
    (EL i (FILTER (\inst. inst.inst_opcode = PHI) xs ++
           (FILTER (\inst. inst.inst_opcode <> PHI) xs ++ [term_inst]))).inst_opcode = PHI` by
    (rpt gen_tac >> strip_tac >> irule phi_partition_prefix >>
     simp[EVERY_FILTER, EVERY_MEM] >> qexists `j` >>
     gvs[APPEND_ASSOC]) >>
  qmatch_goalsub_abbrev_tac `pre_insts ++ [term_inst]` >>
  `EVERY (\inst. ~is_terminator inst.inst_opcode) pre_insts` by
    (qpat_x_assum `!i j. _` kall_tac >>
     simp[Abbr `pre_insts`, EVERY_APPEND, EVERY_FILTER, EVERY_MEM,
          is_terminator_def] >> gvs[EVERY_MEM] >> metis_tac[]) >>
  gvs[bb_well_formed_def, APPEND_ASSOC] >> conj_tac
  >- (simp[EL_APPEND_EQN] >> rpt strip_tac >>
      Cases_on `i < LENGTH pre_insts` >> gvs[EVERY_EL] >>
      `i = LENGTH pre_insts` by decide_tac >> simp[]) >>
  map_every qx_gen_tac [`i`, `j`] >> strip_tac >>
  qpat_x_assum `!i j. _` (qspecl_then [`i`, `j`] mp_tac) >>
  gvs[Abbr `pre_insts`]
QED

Theorem fix_phis_in_block_wf:
  bb_well_formed bb ==> bb_well_formed (fix_phis_in_block actual_preds bb)
Proof
  strip_tac >>
  `bb.bb_instructions <> [] /\
   is_terminator (LAST bb.bb_instructions).inst_opcode` by
    gvs[bb_well_formed_def] >>
  `EVERY (\inst. ~is_terminator inst.inst_opcode)
     (MAP (fix_phi_inst actual_preds) (FRONT bb.bb_instructions))` by
    simp[EVERY_MAP, fix_phi_inst_terminator, bb_well_formed_front_nonterminators] >>
  `(LAST bb.bb_instructions).inst_opcode <> PHI` by
    (strip_tac >> gvs[is_terminator_def]) >>
  `bb.bb_instructions = FRONT bb.bb_instructions ++ [LAST bb.bb_instructions]` by
    simp[APPEND_FRONT_LAST] >>
  simp[fix_phis_in_block_def] >>
  qpat_x_assum `bb.bb_instructions = _` (fn th => once_rewrite_tac [th]) >>
  simp[MAP_APPEND, FILTER_APPEND, fix_phi_inst_non_phi] >>
  irule bb_well_formed_partition >> simp[]
QED

Theorem fix_phis_in_block_last:
  bb_well_formed bb ==>
  LAST (fix_phis_in_block actual_preds bb).bb_instructions = LAST bb.bb_instructions
Proof
  strip_tac >>
  `bb.bb_instructions <> [] /\
   is_terminator (LAST bb.bb_instructions).inst_opcode` by
    gvs[bb_well_formed_def] >>
  `(LAST bb.bb_instructions).inst_opcode <> PHI` by
    (strip_tac >> gvs[is_terminator_def]) >>
  `bb.bb_instructions = FRONT bb.bb_instructions ++ [LAST bb.bb_instructions]` by
    simp[APPEND_FRONT_LAST] >>
  simp[fix_phis_in_block_def] >>
  qpat_x_assum `bb.bb_instructions = _` (fn th => once_rewrite_tac [th]) >>
  simp[MAP_APPEND, FILTER_APPEND, fix_phi_inst_non_phi]
QED

Theorem fix_phis_in_block_succs:
  bb_well_formed bb ==>
  bb_succs (fix_phis_in_block actual_preds bb) = bb_succs bb
Proof
  strip_tac >>
  `bb_well_formed (fix_phis_in_block actual_preds bb)` by
    simp[fix_phis_in_block_wf] >>
  `bb.bb_instructions <> [] /\
   (fix_phis_in_block actual_preds bb).bb_instructions <> []` by
    gvs[bb_well_formed_def] >>
  `LAST (fix_phis_in_block actual_preds bb).bb_instructions =
   LAST bb.bb_instructions` by simp[fix_phis_in_block_last] >>
  Cases_on `bb.bb_instructions` >>
  Cases_on `(fix_phis_in_block actual_preds bb).bb_instructions` >>
  gvs[bb_succs_def]
QED

Theorem fix_all_phis_entry:
  fn_entry_label (fix_all_phis func) = fn_entry_label func
Proof
  Cases_on `func.fn_blocks` >>
  simp[fix_all_phis_def, fn_entry_label_def, entry_block_def,
       bb_label_fix_phis_in_block]
QED

Theorem fix_all_phis_edge:
  (!bb. MEM bb func.fn_blocks ==> bb_well_formed bb) ==>
  (fn_cfg_edge (fix_all_phis func) src dst <=> fn_cfg_edge func src dst)
Proof
  strip_tac >>
  simp[fn_cfg_edge_def, fix_all_phis_def, MEM_MAP, PULL_EXISTS,
       bb_label_fix_phis_in_block] >>
  metis_tac[fix_phis_in_block_succs]
QED

Theorem fix_all_phis_reachable:
  (!bb. MEM bb func.fn_blocks ==> bb_well_formed bb) ==>
  (fn_reachable (fix_all_phis func) lbl <=> fn_reachable func lbl)
Proof
  strip_tac >>
  `fn_cfg_edge (fix_all_phis func) = fn_cfg_edge func` by
    simp[FUN_EQ_THM, fix_all_phis_edge] >>
  simp[fn_reachable_def, fix_all_phis_entry]
QED

Theorem fix_all_phis_all_reachable:
  wf_function func /\ all_reachable func ==> all_reachable (fix_all_phis func)
Proof
  strip_tac >>
  `!lbl. fn_reachable (fix_all_phis func) lbl <=> fn_reachable func lbl` by
    (gen_tac >> irule fix_all_phis_reachable >> gvs[wf_function_def]) >>
  simp[all_reachable_def] >>
  simp[fix_all_phis_def, MEM_MAP, PULL_EXISTS, bb_label_fix_phis_in_block] >>
  gvs[all_reachable_def]
QED

Theorem fix_all_phis_closed:
  wf_function func ==> fn_succs_closed (fix_all_phis func)
Proof
  strip_tac >>
  simp[fn_succs_closed_def, fn_labels_fix_all_phis] >>
  simp[fix_all_phis_def, MEM_MAP, PULL_EXISTS] >>
  metis_tac[wf_function_def, fn_succs_closed_def, fix_phis_in_block_succs]
QED

Theorem fix_all_phis_wf:
  wf_function func ==> wf_function (fix_all_phis func)
Proof
  strip_tac >>
  `fn_has_entry (fix_all_phis func)` by
    gvs[wf_function_def, fn_has_entry_def, fix_all_phis_def] >>
  `fn_inst_ids_distinct (fix_all_phis func)` by
    metis_tac[fix_all_phis_ids, wf_function_def] >>
  simp[wf_function_def, fn_labels_fix_all_phis, fix_all_phis_closed] >>
  conj_tac >- gvs[wf_function_def] >>
  simp[fix_all_phis_def, MEM_MAP, PULL_EXISTS] >>
  metis_tac[wf_function_def, fix_phis_in_block_wf]
QED

Theorem filter_phi_ops_well_formed:
  !actual_preds ops. phi_well_formed ops ==>
    phi_well_formed (filter_phi_ops actual_preds ops)
Proof
  gen_tac >> recInduct phi_well_formed_ind >>
  simp[filter_phi_ops_def, phi_well_formed_def] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[phi_well_formed_def]
QED

Theorem phi_well_formed_pairs_length:
  !ops. phi_well_formed ops ==> LENGTH ops = 2 * LENGTH (phi_pairs ops)
Proof
  recInduct phi_pairs_ind >> simp[phi_well_formed_def, phi_pairs_def]
QED

Theorem fix_phi_inst_phi_arity:
  phi_well_formed inst.inst_operands /\
  (fix_phi_inst actual_preds inst).inst_opcode = PHI ==>
  2 <= LENGTH (phi_pairs (fix_phi_inst actual_preds inst).inst_operands)
Proof
  strip_tac >>
  `phi_well_formed (filter_phi_ops actual_preds inst.inst_operands)` by
    simp[filter_phi_ops_well_formed] >>
  `LENGTH (filter_phi_ops actual_preds inst.inst_operands) =
   2 * LENGTH (phi_pairs (filter_phi_ops actual_preds inst.inst_operands))` by
    simp[phi_well_formed_pairs_length] >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[fix_phi_inst_def] >>
  Cases_on `filter_phi_ops actual_preds inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[phi_well_formed_def] >>
  Cases_on `t'` >> gvs[]
QED

Theorem fix_phis_in_block_mem:
  MEM inst (fix_phis_in_block actual_preds bb).bb_instructions <=>
  ?old_inst. MEM old_inst bb.bb_instructions /\
             inst = fix_phi_inst actual_preds old_inst
Proof
  simp[fix_phis_in_block_def, MEM_APPEND, MEM_FILTER, MEM_MAP] >>
  metis_tac[]
QED

Theorem fix_all_phis_phi_arity:
  fn_inst_wf func ==>
  !inst. MEM inst (fn_insts (fix_all_phis func)) /\ inst.inst_opcode = PHI ==>
         2 <= LENGTH (phi_pairs inst.inst_operands)
Proof
  simp[fn_insts_def, fn_insts_blocks_mem, fix_all_phis_def,
       MEM_MAP, PULL_EXISTS, fix_phis_in_block_mem] >>
  rpt strip_tac >> gvs[] >>
  `old_inst.inst_opcode = PHI` by
    (Cases_on `old_inst.inst_opcode = PHI` >>
     gvs[fix_phi_inst_non_phi]) >>
  `inst_wf old_inst` by metis_tac[fn_inst_wf_def] >>
  `phi_well_formed old_inst.inst_operands` by gvs[inst_wf_def] >>
  irule fix_phi_inst_phi_arity >> simp[]
QED

Theorem update_phi_bypass_shape:
  (update_phi_bypass a_label b_label inst).inst_opcode = inst.inst_opcode /\
  (update_phi_bypass a_label b_label inst).inst_id = inst.inst_id /\
  (update_phi_bypass a_label b_label inst).inst_outputs = inst.inst_outputs
Proof
  Cases_on `inst.inst_opcode = PHI` >>
  Cases_on `MEM (Label a_label) inst.inst_operands` >>
  simp[update_phi_bypass_def]
QED

Theorem subst_label_inst_shape:
  (subst_label_inst old_lbl new_lbl inst).inst_opcode = inst.inst_opcode /\
  (subst_label_inst old_lbl new_lbl inst).inst_id = inst.inst_id /\
  (subst_label_inst old_lbl new_lbl inst).inst_outputs = inst.inst_outputs
Proof
  simp[subst_label_inst_def]
QED

Theorem canon_jnz_inst_shape:
  is_terminator (canon_jnz_inst inst).inst_opcode = is_terminator inst.inst_opcode /\
  ((canon_jnz_inst inst).inst_opcode = PHI <=> inst.inst_opcode = PHI) /\
  (canon_jnz_inst inst).inst_id = inst.inst_id /\
  (canon_jnz_inst inst).inst_outputs = inst.inst_outputs
Proof
  simp[canon_jnz_inst_def] >>
  rpt CASE_TAC >> gvs[is_terminator_def]
QED

Theorem bb_well_formed_map_classification:
  bb_well_formed bb /\
  (!inst. is_terminator (f inst).inst_opcode = is_terminator inst.inst_opcode /\
          ((f inst).inst_opcode = PHI <=> inst.inst_opcode = PHI)) ==>
  bb_well_formed (bb with bb_instructions := MAP f bb.bb_instructions)
Proof
  strip_tac >> qpat_x_assum `bb_well_formed bb` mp_tac >>
  simp[bb_well_formed_def, LAST_MAP, EL_MAP] >>
  strip_tac >> conj_tac >> rpt strip_tac >> gvs[listTheory.EL_MAP] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem bb_well_formed_update_phi_bypass:
  bb_well_formed bb ==>
  bb_well_formed (bb with bb_instructions :=
    MAP (update_phi_bypass a_label b_label) bb.bb_instructions)
Proof
  strip_tac >> irule bb_well_formed_map_classification >>
  simp[update_phi_bypass_shape]
QED

Theorem bb_well_formed_bypass_source:
  bb_well_formed bb ==>
  bb_well_formed (bb with bb_instructions :=
    MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                else canon_jnz_inst (subst_label_inst old_lbl new_lbl inst))
        bb.bb_instructions)
Proof
  strip_tac >> irule bb_well_formed_map_classification >> simp[] >>
  gen_tac >> IF_CASES_TAC >> simp[canon_jnz_inst_shape, subst_label_inst_shape]
QED

Theorem bb_front_no_terminator:
  bb_well_formed bb /\ i < LENGTH (FRONT bb.bb_instructions) ==>
  ~is_terminator (EL i (FRONT bb.bb_instructions)).inst_opcode
Proof
  strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `i < LENGTH bb.bb_instructions` by
    (fs[LENGTH_FRONT, NULL_EQ] >> decide_tac) >>
  `EL i (FRONT bb.bb_instructions) = EL i bb.bb_instructions` by
    (irule EL_FRONT >> simp[NULL_EQ]) >>
  fs[bb_well_formed_def] >> strip_tac >>
  `i = PRE (LENGTH bb.bb_instructions)` by metis_tac[] >>
  fs[LENGTH_FRONT, NULL_EQ]
QED

Theorem bb_front_phi_prefix:
  bb_well_formed bb /\ i < j /\ j < LENGTH (FRONT bb.bb_instructions) /\
  (EL j (FRONT bb.bb_instructions)).inst_opcode = PHI ==>
  (EL i (FRONT bb.bb_instructions)).inst_opcode = PHI
Proof
  strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `i < LENGTH (FRONT bb.bb_instructions)` by decide_tac >>
  `j < LENGTH bb.bb_instructions` by
    (fs[LENGTH_FRONT, NULL_EQ] >> decide_tac) >>
  `EL i (FRONT bb.bb_instructions) = EL i bb.bb_instructions` by
    (irule EL_FRONT >> simp[NULL_EQ]) >>
  `EL j (FRONT bb.bb_instructions) = EL j bb.bb_instructions` by
    (irule EL_FRONT >> simp[NULL_EQ]) >>
  gvs[] >> fs[bb_well_formed_def] >> metis_tac[]
QED

Theorem bb_well_formed_merge_blocks:
  bb_well_formed a /\ bb_well_formed b /\ no_phis b ==>
  bb_well_formed (merge_blocks a b)
Proof
  strip_tac >>
  `b.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `0 < LENGTH b.bb_instructions` by (Cases_on `b.bb_instructions` >> gvs[]) >>
  `is_terminator (LAST b.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  simp[NoAsms, merge_blocks_def, bb_well_formed_def] >>
  conj_tac >- simp[] >>
  conj_tac >- (Cases_on `b.bb_instructions` >> gvs[LAST_APPEND_CONS]) >>
  conj_tac
  >- (rpt strip_tac >>
      Cases_on `i < LENGTH (FRONT a.bb_instructions)`
      >- (gvs[EL_APPEND_EQN] >> metis_tac[bb_front_no_terminator]) >>
      gvs[EL_APPEND_EQN] >>
      `i - LENGTH (FRONT a.bb_instructions) < LENGTH b.bb_instructions` by
        decide_tac >>
      qpat_x_assum `bb_well_formed b` mp_tac >>
      simp[NoAsms, bb_well_formed_def] >> strip_tac >>
      `i - LENGTH (FRONT a.bb_instructions) = PRE (LENGTH b.bb_instructions)` by
        metis_tac[] >>
      decide_tac) >>
  rpt strip_tac >>
  Cases_on `j < LENGTH (FRONT a.bb_instructions)`
  >- (`i < LENGTH (FRONT a.bb_instructions)` by decide_tac >>
      gvs[EL_APPEND_EQN] >> metis_tac[bb_front_phi_prefix]) >>
  gvs[EL_APPEND_EQN] >>
  `j - LENGTH (FRONT a.bb_instructions) < LENGTH b.bb_instructions` by
    decide_tac >>
  fs[no_phis_def, EVERY_EL] >>
  qpat_x_assum `!n. _` (qspec_then `j - LENGTH (FRONT a.bb_instructions)` mp_tac) >>
  simp[]
QED

Theorem bb_well_formed_subst_phi_labels:
  bb_well_formed bb ==>
  bb_well_formed (bb with bb_instructions :=
    MAP (\inst. if inst.inst_opcode <> PHI then inst
                else subst_label_inst old_lbl new_lbl inst) bb.bb_instructions)
Proof
  strip_tac >> irule bb_well_formed_map_classification >> simp[] >>
  gen_tac >> IF_CASES_TAC >> simp[subst_label_inst_shape]
QED

Theorem EVERY_replace_block:
  EVERY P bbs /\ P bb ==> EVERY P (replace_block lbl bb bbs)
Proof
  simp[replace_block_def, EVERY_MEM, MEM_MAP] >>
  rpt strip_tac >> gvs[] >> IF_CASES_TAC >> simp[]
QED

Theorem update_succ_phi_labels_bb_wf:
  !succs bbs. EVERY bb_well_formed bbs ==>
  EVERY bb_well_formed (update_succ_phi_labels old_lbl new_lbl bbs succs)
Proof
  Induct_on `succs` >> fs[update_succ_phi_labels_def] >>
  rpt strip_tac >> Cases_on `lookup_block h bbs` >> simp[] >>
  first_x_assum irule >> irule EVERY_replace_block >> simp[] >>
  irule bb_well_formed_subst_phi_labels >>
  drule lookup_block_member_label >> strip_tac >>
  fs[EVERY_MEM]
QED

Theorem chain_merge_base_bb_wf:
  wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b ==>
  EVERY bb_well_formed (replace_block a.bb_label (merge_blocks a b)
    (remove_block b.bb_label fn.fn_blocks))
Proof
  strip_tac >> irule EVERY_replace_block >> conj_tac
  >- (irule bb_well_formed_merge_blocks >>
      fs[wf_function_def, can_merge_blocks_def] >> metis_tac[]) >>
  fs[remove_block_def, EVERY_MEM, MEM_FILTER, wf_function_def] >>
  metis_tac[]
QED

Theorem chain_merge_bb_wf:
  wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b ==>
  EVERY bb_well_formed
    (update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b)))
Proof
  strip_tac >> irule update_succ_phi_labels_bb_wf >>
  irule chain_merge_base_bb_wf >> simp[]
QED

Theorem chain_merge_labels_entry:
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\
  can_merge_blocks fn a b /\ ALL_DISTINCT (fn_labels fn) /\
  fn' = fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b)) ==>
  ALL_DISTINCT (fn_labels fn') /\ fn_has_entry fn'
Proof
  strip_tac >>
  qspecl_then [`fn`, `a`, `b.bb_label`, `b`] mp_tac chain_merge_event_labels >>
  simp[] >> strip_tac >> simp[] >>
  fs[fn_has_entry_def, fn_labels_def] >>
  Cases_on `fn'.fn_blocks` >> gvs[]
QED

Theorem bb_succs_map_nonterminators:
  bb_well_formed bb /\
  (!inst. is_terminator inst.inst_opcode ==> f inst = inst) ==>
  bb_succs (bb with bb_instructions := MAP f bb.bb_instructions) = bb_succs bb
Proof
  strip_tac >>
  `bb.bb_instructions <> [] /\
   is_terminator (LAST bb.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  `f (LAST bb.bb_instructions) = LAST bb.bb_instructions` by simp[] >>
  Cases_on `bb.bb_instructions` >> gvs[bb_succs_def, LAST_MAP] >>
  once_rewrite_tac[GSYM MAP] >> simp[LAST_MAP]
QED

Theorem bb_succs_merge_blocks:
  b.bb_instructions <> [] ==> bb_succs (merge_blocks a b) = bb_succs b
Proof
  strip_tac >> Cases_on `FRONT a.bb_instructions` >>
  Cases_on `b.bb_instructions` >>
  gvs[merge_blocks_def, bb_succs_def, LAST_APPEND_CONS] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND, LAST_DEF,
                   APPEND_eq_NIL, LAST_APPEND_CONS] >> simp[]
QED

Theorem bb_succs_subst_phi_labels:
  bb_well_formed bb ==>
  bb_succs (bb with bb_instructions :=
    MAP (\inst. if inst.inst_opcode <> PHI then inst
                else subst_label_inst old_lbl new_lbl inst) bb.bb_instructions) =
  bb_succs bb
Proof
  strip_tac >> irule bb_succs_map_nonterminators >> simp[] >>
  rpt strip_tac >> `inst.inst_opcode <> PHI` by
    (strip_tac >> fs[is_terminator_def]) >> simp[]
QED

Theorem update_succ_phi_labels_cfg_property:
  !succs bbs. EVERY bb_well_formed bbs /\
  EVERY (\bb. P bb.bb_label (bb_succs bb)) bbs ==>
  EVERY (\bb. P bb.bb_label (bb_succs bb))
    (update_succ_phi_labels old_lbl new_lbl bbs succs)
Proof
  Induct_on `succs` >> fs[update_succ_phi_labels_def] >>
  rpt strip_tac >> Cases_on `lookup_block h bbs` >> simp[] >>
  first_x_assum irule >>
  `bb_well_formed x /\ P x.bb_label (bb_succs x)` by
    (drule lookup_block_member_label >> strip_tac >> fs[EVERY_MEM]) >>
  conj_tac
  >- (irule EVERY_replace_block >> simp[bb_well_formed_subst_phi_labels]) >>
  irule EVERY_replace_block >> simp[bb_succs_subst_phi_labels]
QED

Theorem num_preds_one_unique:
  num_preds fn lbl = 1 /\ MEM a fn.fn_blocks /\ MEM lbl (bb_succs a) /\
  MEM bb fn.fn_blocks /\ MEM lbl (bb_succs bb) ==> bb = a
Proof
  strip_tac >>
  `MEM a (block_preds fn lbl) /\ MEM bb (block_preds fn lbl)` by
    simp[block_preds_def, MEM_FILTER] >>
  fs[num_preds_def] >>
  Cases_on `block_preds fn lbl` >> gvs[] >>
  Cases_on `t` >> gvs[]
QED

Theorem can_merge_blocks_unique_pred:
  can_merge_blocks fn a b /\ MEM a fn.fn_blocks /\
  MEM bb fn.fn_blocks /\ MEM b.bb_label (bb_succs bb) ==> bb = a
Proof
  strip_tac >> irule num_preds_one_unique >>
  qexistsl [`fn`, `b.bb_label`] >> fs[can_merge_blocks_def]
QED

Theorem chain_merge_fn_labels:
  fn_labels (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b))) =
  FILTER (\lbl. lbl <> b.bb_label) (fn_labels fn)
Proof
  simp[fn_labels_def, fn_labels_update_succ_phi_labels, merge_blocks_def,
       cfgTransformPropsTheory.fn_labels_replace_block,
       cfgTransformPropsTheory.fn_labels_remove_block]
QED

Theorem chain_merge_base_closed:
  wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b ==>
  !bb succ.
    MEM bb (replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label fn.fn_blocks)) /\ MEM succ (bb_succs bb) ==>
    MEM succ (FILTER (\lbl. lbl <> b.bb_label) (fn_labels fn))
Proof
  strip_tac >> qx_gen_tac `bb` >> qx_gen_tac `succ` >> strip_tac >>
  qpat_x_assum `MEM bb (replace_block _ _ _)` mp_tac >>
  simp[replace_block_def, remove_block_def, MEM_MAP, MEM_FILTER] >>
  disch_then (qx_choose_then `orig` strip_assume_tac) >>
  Cases_on `orig.bb_label = a.bb_label` >> gvs[]
  >- (`b.bb_instructions <> []` by fs[wf_function_def, bb_well_formed_def] >>
      gvs[bb_succs_merge_blocks] >>
      `succ <> b.bb_label` by
        (strip_tac >> gvs[] >> drule_all can_merge_blocks_unique_pred >>
         strip_tac >> gvs[can_merge_blocks_def]) >>
      fs[MEM_FILTER, wf_function_def, fn_succs_closed_def] >> metis_tac[]) >>
  `succ <> b.bb_label` by
    (strip_tac >> gvs[] >> drule_all can_merge_blocks_unique_pred >> strip_tac >> gvs[]) >>
  fs[MEM_FILTER, wf_function_def, fn_succs_closed_def] >> metis_tac[]
QED

Theorem chain_merge_succs_closed:
  wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b ==>
  fn_succs_closed (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b)))
Proof
  strip_tac >>
  simp[fn_succs_closed_def, chain_merge_fn_labels] >>
  `EVERY (\bb. !succ. MEM succ (bb_succs bb) ==>
      MEM succ (FILTER (\lbl. lbl <> b.bb_label) (fn_labels fn)))
    (update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b)))` by
    (ho_match_mp_tac update_succ_phi_labels_cfg_property >> conj_tac
     >- (irule chain_merge_base_bb_wf >> simp[]) >>
     simp[EVERY_MEM] >> rpt strip_tac >>
     drule_all chain_merge_base_closed >> simp[]) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem blocks_extract_perm:
  !bbs. ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\ MEM a bbs ==>
  PERM (a::remove_block a.bb_label bbs) bbs
Proof
  Induct >- simp[] >> gen_tac >> disch_tac >>
  Cases_on `h = a`
  >- (qpat_x_assum `_ ==> _` kall_tac >>
      qpat_x_assum `h = a` SUBST_ALL_TAC >> fs[] >>
      `FILTER (\bb. bb.bb_label <> a.bb_label) bbs = bbs` by
        (simp[listTheory.FILTER_EQ_ID, EVERY_MEM] >> fs[MEM_MAP] >> metis_tac[]) >>
      simp[remove_block_def]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\ MEM a bbs /\
   ~MEM h.bb_label (MAP (\bb. bb.bb_label) bbs)` by fs[] >>
  `h.bb_label <> a.bb_label` by (fs[MEM_MAP] >> metis_tac[]) >>
  `PERM (a::remove_block a.bb_label bbs) bbs` by
    (first_x_assum irule >> fs[]) >>
  simp[remove_block_def] >>
  irule PERM_TRANS >>
  qexists `h::a::FILTER (\bb. bb.bb_label <> a.bb_label) bbs` >>
  simp[PERM_SWAP_AT_FRONT] >> fs[remove_block_def]
QED

Theorem flat_projection_extract_block:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\ MEM a bbs ==>
  PERM (project a ++ FLAT (MAP project (remove_block a.bb_label bbs)))
       (FLAT (MAP project bbs))
Proof
  strip_tac >> drule_all blocks_extract_perm >> strip_tac >>
  `PERM (FLAT (MAP project (a::remove_block a.bb_label bbs)))
        (FLAT (MAP project bbs))` by
    (irule PERM_FLAT >> irule PERM_MAP >> simp[]) >> fs[]
QED

Theorem blocks_extract_pair_perm:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\ MEM a bbs /\ MEM b bbs /\
  a.bb_label <> b.bb_label ==>
  PERM (a::b::remove_block b.bb_label (remove_block a.bb_label bbs)) bbs
Proof
  strip_tac >>
  `PERM (a::remove_block a.bb_label bbs) bbs` by
    (irule blocks_extract_perm >> simp[]) >>
  `PERM (b::remove_block b.bb_label (remove_block a.bb_label bbs))
        (remove_block a.bb_label bbs)` by
    (irule blocks_extract_perm >> simp[cfgTransformPropsTheory.ALL_DISTINCT_remove_block] >>
     simp[remove_block_def, MEM_FILTER]) >>
  irule PERM_TRANS >> qexists `a::remove_block a.bb_label bbs` >> simp[]
QED

Theorem chain_merge_base_perm:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\ MEM a bbs /\ MEM b bbs /\
  a.bb_label <> b.bb_label ==>
  PERM (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label bbs))
    (merge_blocks a b :: remove_block b.bb_label (remove_block a.bb_label bbs))
Proof
  strip_tac >> drule_all blocks_extract_pair_perm >> strip_tac >>
  `PERM
    (replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label
        (a::b::remove_block b.bb_label (remove_block a.bb_label bbs))))
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label bbs))` by
    (pure_rewrite_tac[replace_block_def, remove_block_def] >>
     irule PERM_MAP >> irule PERM_FILTER >> fs[remove_block_def]) >>
  `!bb. MEM bb (remove_block b.bb_label (remove_block a.bb_label bbs)) ==>
        bb.bb_label <> a.bb_label /\ bb.bb_label <> b.bb_label` by
    simp[remove_block_def, MEM_FILTER] >>
  `remove_block b.bb_label (remove_block b.bb_label (remove_block a.bb_label bbs)) =
   remove_block b.bb_label (remove_block a.bb_label bbs)` by
    (simp[remove_block_def, FILTER_FILTER, combinTheory.o_DEF, SF CONJ_ss]) >>
  `replace_block a.bb_label (merge_blocks a b)
     (remove_block b.bb_label (remove_block a.bb_label bbs)) =
   remove_block b.bb_label (remove_block a.bb_label bbs)` by
    (rewrite_tac[replace_block_def] >>
     GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM MAP_ID] >>
     irule MAP_CONG >> simp[] >> metis_tac[]) >>
  fs[remove_block_def, replace_block_def] >> gvs[] >> metis_tac[PERM_SYM]
QED

Theorem chain_merge_base_projection_distinct:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\ MEM a bbs /\ MEM b bbs /\
  a.bb_label <> b.bb_label /\ ALL_DISTINCT (FLAT (MAP project bbs)) /\
  sublist (project (merge_blocks a b)) (project a ++ project b) ==>
  ALL_DISTINCT (FLAT (MAP project
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label bbs))))
Proof
  strip_tac >> drule_all blocks_extract_pair_perm >> strip_tac >>
  drule_all chain_merge_base_perm >> strip_tac >>
  qmatch_asmsub_abbrev_tac `a::b::rest` >>
  `PERM (FLAT (MAP project (a::b::rest))) (FLAT (MAP project bbs))` by
    (irule PERM_FLAT >> irule PERM_MAP >> simp[]) >>
  `ALL_DISTINCT (FLAT (MAP project (a::b::rest)))` by
    metis_tac[ALL_DISTINCT_PERM] >>
  `sublist (project (merge_blocks a b) ++ FLAT (MAP project rest))
           (FLAT (MAP project (a::b::rest)))` by
    (simp[] >> pure_rewrite_tac[APPEND_ASSOC] >>
     irule sublist_append_pair >> simp[sublist_refl]) >>
  `ALL_DISTINCT (FLAT (MAP project (merge_blocks a b::rest)))` by
    (simp[] >> metis_tac[sublist_ALL_DISTINCT]) >>
  `PERM
    (FLAT (MAP project (replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label bbs))))
    (FLAT (MAP project (merge_blocks a b::rest)))` by
    (irule PERM_FLAT >> irule PERM_MAP >> simp[Abbr `rest`]) >>
  metis_tac[ALL_DISTINCT_PERM]
QED

Theorem flat_map_front_sublist:
  !xs. sublist (FLAT (MAP project (FRONT xs))) (FLAT (MAP project xs))
Proof
  Induct >- simp[sublist_refl] >> gen_tac >> Cases_on `xs` >>
  fs[FRONT_DEF, sublist_refl, sublist_nil] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule sublist_append_pair >> fs[sublist_refl]
QED

Theorem chain_merge_base_ssa:
  wf_function fn /\ ssa_form fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b ==>
  ssa_form (fn with fn_blocks :=
    replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
Proof
  strip_tac >>
  fs[ssa_form_def, fn_insts_def, fn_insts_projection_blocks] >>
  irule chain_merge_base_projection_distinct >>
  simp[merge_blocks_def, MAP_APPEND, FLAT_APPEND] >>
  conj_tac >- fs[wf_function_def, fn_labels_def] >>
  conj_tac >- fs[can_merge_blocks_def] >>
  irule sublist_append_pair >> simp[sublist_refl, flat_map_front_sublist]
QED

Theorem map_front_sublist:
  sublist (MAP f (FRONT xs)) (MAP f xs)
Proof
  `!ys. FLAT (MAP (\x. [f x]) ys) = MAP f ys` by (Induct >> simp[]) >>
  `sublist (FLAT (MAP (\x. [f x]) (FRONT xs)))
           (FLAT (MAP (\x. [f x]) xs))` suffices_by simp[] >>
  irule flat_map_front_sublist
QED

Theorem chain_merge_base_ids:
  wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b ==>
  fn_inst_ids_distinct (fn with fn_blocks :=
    replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
   ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks)) /\
   a.bb_label <> b.bb_label` by
    fs[wf_function_def, fn_labels_def, fn_inst_ids_distinct_def, can_merge_blocks_def] >>
  simp[fn_inst_ids_distinct_def] >>
  irule chain_merge_base_projection_distinct >>
  simp[merge_blocks_def, MAP_APPEND] >>
  irule sublist_append_pair >> simp[sublist_refl, map_front_sublist]
QED

Theorem replace_block_projection:
  !bbs. ALL_DISTINCT (MAP (\b. b.bb_label) bbs) /\
  lookup_block lbl bbs = SOME bb /\ project new_bb = project bb ==>
  MAP project (replace_block lbl new_bb bbs) = MAP project bbs
Proof
  Induct >- simp[lookup_block_def, FIND_thm] >> gen_tac >>
  pure_rewrite_tac[MAP, ALL_DISTINCT, lookup_block_def, FIND_thm] >>
  Cases_on `h.bb_label = lbl` >> simp[] >> strip_tac
  >- (gvs[] >> simp[replace_block_def, MAP_MAP_o, combinTheory.o_DEF] >>
      irule MAP_CONG >> simp[] >> fs[MEM_MAP] >> metis_tac[]) >>
  simp[replace_block_def] >>
  fs[lookup_block_def, replace_block_def]
QED

Theorem update_succ_phi_labels_projection:
  !succs bbs. ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  (!inst. project (subst_label_inst old_lbl new_lbl inst) = project inst) ==>
  MAP (\bb. MAP project bb.bb_instructions)
    (update_succ_phi_labels old_lbl new_lbl bbs succs) =
  MAP (\bb. MAP project bb.bb_instructions) bbs
Proof
  Induct_on `succs` >> fs[update_succ_phi_labels_def] >>
  rpt strip_tac >> Cases_on `lookup_block h bbs` >> simp[] >>
  rename1 `lookup_block h bbs = SOME bb` >>
  `MAP (\b. MAP project b.bb_instructions)
    (replace_block h (bb with bb_instructions :=
      MAP (\inst. if inst.inst_opcode <> PHI then inst
                  else subst_label_inst old_lbl new_lbl inst)
        bb.bb_instructions) bbs) =
   MAP (\b. MAP project b.bb_instructions) bbs` by
    (irule replace_block_projection >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
     irule MAP_CONG >> simp[] >> gen_tac >> strip_tac >>
     IF_CASES_TAC >> simp[]) >>
  `bb.bb_label = h` by metis_tac[lookup_block_member_label] >>
  qmatch_goalsub_abbrev_tac `FOLDL stepfn bs succs` >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) bs)` by
    simp[Abbr `bs`, cfgTransformPropsTheory.fn_labels_replace_block] >>
  qpat_x_assum `!bbs. _` (qspec_then `bs` mp_tac) >>
  simp[Abbr `stepfn`, Abbr `bs`]
QED

Theorem update_succ_phi_labels_ids:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  fn_inst_ids_distinct (fn with fn_blocks := bbs) ==>
  fn_inst_ids_distinct (fn with fn_blocks :=
    update_succ_phi_labels old_lbl new_lbl bbs succs)
Proof
  simp[fn_inst_ids_distinct_def] >> strip_tac >>
  `MAP (\bb. MAP (\inst. inst.inst_id) bb.bb_instructions)
      (update_succ_phi_labels old_lbl new_lbl bbs succs) =
   MAP (\bb. MAP (\inst. inst.inst_id) bb.bb_instructions) bbs` by
    (irule update_succ_phi_labels_projection >> simp[subst_label_inst_shape]) >>
  simp[]
QED

Theorem update_succ_phi_labels_ssa:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\ ssa_form (fn with fn_blocks := bbs) ==>
  ssa_form (fn with fn_blocks :=
    update_succ_phi_labels old_lbl new_lbl bbs succs)
Proof
  strip_tac >>
  `MAP (\bb. MAP (\inst. inst.inst_outputs) bb.bb_instructions)
      (update_succ_phi_labels old_lbl new_lbl bbs succs) =
   MAP (\bb. MAP (\inst. inst.inst_outputs) bb.bb_instructions) bbs` by
    (irule update_succ_phi_labels_projection >> simp[subst_label_inst_shape]) >>
  `MAP FLAT (MAP (\bb. MAP (\inst. inst.inst_outputs) bb.bb_instructions)
      (update_succ_phi_labels old_lbl new_lbl bbs succs)) =
   MAP FLAT (MAP (\bb. MAP (\inst. inst.inst_outputs) bb.bb_instructions) bbs)` by simp[] >>
  fs[ssa_form_def, fn_insts_def, fn_insts_projection_blocks,
     MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem chain_merge_base_labels:
  ALL_DISTINCT (fn_labels fn) ==>
  ALL_DISTINCT (MAP (\bb. bb.bb_label)
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks)))
Proof
  simp[cfgTransformPropsTheory.fn_labels_replace_block,
       cfgTransformPropsTheory.fn_labels_remove_block, merge_blocks_def] >>
  strip_tac >> irule FILTER_ALL_DISTINCT >> fs[fn_labels_def]
QED

Theorem chain_merge_ids:
  wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b ==>
  fn_inst_ids_distinct (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b)))
Proof
  strip_tac >> irule update_succ_phi_labels_ids >> conj_tac
  >- (irule chain_merge_base_labels >> fs[wf_function_def]) >>
  irule chain_merge_base_ids >> simp[]
QED

Theorem chain_merge_ssa:
  wf_function fn /\ ssa_form fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b ==>
  ssa_form (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b)))
Proof
  strip_tac >> irule update_succ_phi_labels_ssa >> conj_tac
  >- (irule chain_merge_base_labels >> fs[wf_function_def]) >>
  irule chain_merge_base_ssa >> simp[]
QED

Theorem chain_merge_wf:
  wf_function fn /\ lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_merge_blocks fn a b ==>
  wf_function (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b)))
Proof
  strip_tac >>
  `MEM a fn.fn_blocks /\ MEM b fn.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  qmatch_goalsub_abbrev_tac `wf_function result_fn` >>
  `ALL_DISTINCT (fn_labels result_fn) /\ fn_has_entry result_fn` by
    (irule chain_merge_labels_entry >> qexistsl [`a`, `b`, `fn`] >>
     simp[Abbr `result_fn`] >> fs[wf_function_def]) >>
  simp[wf_function_def] >> rpt conj_tac
  >- (simp[Abbr `result_fn`] >>
      drule_all chain_merge_bb_wf >> simp[EVERY_MEM])
  >- (simp[Abbr `result_fn`] >> irule chain_merge_succs_closed >> simp[]) >>
  simp[Abbr `result_fn`] >> irule chain_merge_ids >> simp[]
QED
