Theory simplifyCfgStruct
Ancestors
  simplifyCfgLabelProps simplifyCfgCompute simplifyCfgDefs cfgWf venomWf venomInst
  cfgTransform list rich_list sorting unitShapeDefs

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

Theorem update_succ_phi_labels_every_inst:
  !succs bbs. EVERY (\bb. EVERY P bb.bb_instructions) bbs /\
  (!inst. P inst /\ inst.inst_opcode = PHI ==>
    P (subst_label_inst old_lbl new_lbl inst)) ==>
  EVERY (\bb. EVERY P bb.bb_instructions)
    (update_succ_phi_labels old_lbl new_lbl bbs succs)
Proof
  Induct_on `succs` >> fs[update_succ_phi_labels_def] >>
  rpt strip_tac >> Cases_on `lookup_block h bbs` >> simp[] >>
  first_x_assum irule >> simp[] >> irule EVERY_replace_block >> simp[] >>
  drule lookup_block_member_label >> strip_tac >>
  fs[EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem chain_merge_base_every_inst:
  EVERY (\bb. EVERY P bb.bb_instructions) fn.fn_blocks /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks ==>
  EVERY (\bb. EVERY P bb.bb_instructions)
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
Proof
  strip_tac >> irule EVERY_replace_block >> conj_tac
  >- (`EVERY P a.bb_instructions /\ EVERY P b.bb_instructions` by
        (fs[EVERY_MEM] >> metis_tac[]) >>
      simp[merge_blocks_def] >>
      Cases_on `a.bb_instructions` >> fs[EVERY_MEM] >> metis_tac[MEM_FRONT]) >>
  fs[EVERY_MEM, remove_block_def, MEM_FILTER] >> metis_tac[]
QED

Theorem chain_merge_every_inst:
  EVERY (\bb. EVERY P bb.bb_instructions) fn.fn_blocks /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  (!inst. P inst /\ inst.inst_opcode = PHI ==>
    P (subst_label_inst b.bb_label a.bb_label inst)) ==>
  EVERY (\bb. EVERY P bb.bb_instructions)
    (update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b)))
Proof
  strip_tac >> irule update_succ_phi_labels_every_inst >> simp[] >>
  irule chain_merge_base_every_inst >> simp[]
QED

Theorem phi_well_formed_subst_label_ops:
  !ops. phi_well_formed ops ==>
    phi_well_formed (MAP (subst_label_op old_lbl new_lbl) ops)
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, subst_label_op_def] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[phi_well_formed_def]
QED

Theorem chain_merge_phi_operands:
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI ==>
    phi_well_formed inst.inst_operands) /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks ==>
  !inst. MEM inst (fn_insts (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b)))) /\
    inst.inst_opcode = PHI ==> phi_well_formed inst.inst_operands
Proof
  strip_tac >>
  `EVERY (\bb. EVERY (\inst. inst.inst_opcode = PHI ==>
      phi_well_formed inst.inst_operands) bb.bb_instructions)
    (update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b)))` by
    (ho_match_mp_tac chain_merge_every_inst >> simp[] >> conj_tac
     >- (simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum irule >>
         simp[fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]) >>
     simp[subst_label_inst_def, phi_well_formed_subst_label_ops]) >>
  fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]
QED

Theorem chain_merge_jnz_distinct:
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = JNZ ==>
    ?c t f. inst.inst_operands = [c; Label t; Label f] /\ t <> f) /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks ==>
  !inst. MEM inst (fn_insts (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b)))) /\
    inst.inst_opcode = JNZ ==>
    ?c t f. inst.inst_operands = [c; Label t; Label f] /\ t <> f
Proof
  strip_tac >>
  `EVERY (\bb. EVERY (\inst. inst.inst_opcode = JNZ ==>
      ?c t f. inst.inst_operands = [c; Label t; Label f] /\ t <> f) bb.bb_instructions)
    (update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b)))` by
    (ho_match_mp_tac chain_merge_every_inst >> simp[] >>
     simp[subst_label_inst_shape, EVERY_MEM] >> rpt strip_tac >>
     first_x_assum irule >> simp[fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]) >>
  fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]
QED

Theorem chain_merge_entry_label:
  wf_function fn /\ first_block_no_preds fn /\ MEM a fn.fn_blocks /\
  can_merge_blocks fn a b ==>
  (HD (update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b)))).bb_label =
  (HD fn.fn_blocks).bb_label
Proof
  strip_tac >>
  `fn.fn_blocks <> []` by fs[wf_function_def, fn_has_entry_def] >>
  `(HD fn.fn_blocks).bb_label <> b.bb_label` by
    (fs[first_block_no_preds_def, EVERY_MEM, can_merge_blocks_def] >>
     qpat_x_assum `!bb. _` (qspec_then `a` mp_tac) >> simp[]) >>
  qmatch_goalsub_abbrev_tac `HD result_blocks` >>
  `MAP (\bb. bb.bb_label) result_blocks =
   FILTER (\lbl. lbl <> b.bb_label) (fn_labels fn)` by
    (mp_tac chain_merge_fn_labels >>
     simp[fn_labels_def, Abbr `result_blocks`]) >>
  Cases_on `fn.fn_blocks` >> Cases_on `result_blocks` >>
  gvs[fn_labels_def]
QED

Theorem chain_merge_first_block_no_preds:
  wf_function fn /\ first_block_no_preds fn /\ MEM a fn.fn_blocks /\
  MEM b fn.fn_blocks /\ can_merge_blocks fn a b ==>
  first_block_no_preds (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b)))
Proof
  strip_tac >> simp[first_block_no_preds_def, chain_merge_entry_label] >>
  ho_match_mp_tac update_succ_phi_labels_cfg_property >> conj_tac
  >- (irule chain_merge_base_bb_wf >> simp[]) >>
  irule EVERY_replace_block >> conj_tac
  >- (`b.bb_instructions <> []` by fs[wf_function_def, bb_well_formed_def] >>
      simp[merge_blocks_def, bb_succs_merge_blocks] >>
      fs[first_block_no_preds_def, EVERY_MEM] >> metis_tac[]) >>
  fs[first_block_no_preds_def, remove_block_def, EVERY_MEM, MEM_FILTER] >> metis_tac[]
QED

Theorem do_merge_jump_bb_wf:
  wf_function fn /\ MEM a fn.fn_blocks /\
  do_merge_jump fn a b lm = SOME (fn', lm') ==>
  EVERY bb_well_formed fn'.fn_blocks
Proof
  strip_tac >>
  `EVERY bb_well_formed fn.fn_blocks` by fs[wf_function_def, EVERY_MEM] >>
  `bb_well_formed a` by fs[EVERY_MEM] >>
  fs[do_merge_jump_def, AllCaseEqs()] >>
  drule lookup_block_member_label >> strip_tac >>
  `bb_well_formed target` by fs[EVERY_MEM] >> gvs[] >>
  irule EVERY_replace_block >> conj_tac
  >- (IF_CASES_TAC >> simp[bb_well_formed_bypass_source] >>
      rewrite_tac[MAP_MAP_o] >> irule bb_well_formed_map_classification >>
      simp[combinTheory.o_DEF, update_phi_bypass_shape] >>
      gen_tac >> IF_CASES_TAC >> simp[canon_jnz_inst_shape, subst_label_inst_shape]) >>
  irule EVERY_replace_block >> simp[bb_well_formed_update_phi_bypass,
    remove_block_def, EVERY_FILTER] >> fs[EVERY_MEM]
QED

Theorem replace_block_projection_members:
  (!bb. MEM bb bbs /\ bb.bb_label = lbl ==> project new_bb = project bb) ==>
  MAP project (replace_block lbl new_bb bbs) = MAP project bbs
Proof
  strip_tac >> simp[replace_block_def, MAP_MAP_o, combinTheory.o_DEF] >>
  irule MAP_CONG >> simp[] >> rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

Theorem do_merge_jump_fn_labels:
  do_merge_jump fn a b lm = SOME (fn', lm') ==>
  fn_labels fn' = FILTER (\lbl. lbl <> b.bb_label) (fn_labels fn)
Proof
  simp[do_merge_jump_def, AllCaseEqs()] >> rpt strip_tac >>
  drule lookup_block_member_label >> strip_tac >> gvs[] >>
  simp[fn_labels_def, cfgTransformPropsTheory.fn_labels_replace_block,
       cfgTransformPropsTheory.fn_labels_remove_block]
QED

Theorem do_merge_jump_labels_entry:
  wf_function fn /\ lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn', lm') ==>
  ALL_DISTINCT (fn_labels fn') /\ fn_has_entry fn'
Proof
  strip_tac >> fs[wf_function_def] >>
  drule_all do_merge_jump_event_labels >> strip_tac >> simp[] >>
  Cases_on `fn'.fn_blocks` >> fs[fn_labels_def, fn_has_entry_def]
QED

Theorem do_merge_jump_entry_label:
  wf_function fn /\ first_block_no_preds fn /\ MEM a fn.fn_blocks /\
  can_bypass_jump fn a b /\ do_merge_jump fn a b lm = SOME (fn', lm') ==>
  (HD fn'.fn_blocks).bb_label = (HD fn.fn_blocks).bb_label
Proof
  strip_tac >>
  `fn.fn_blocks <> []` by fs[wf_function_def, fn_has_entry_def] >>
  `(HD fn.fn_blocks).bb_label <> b.bb_label` by
    (fs[first_block_no_preds_def, EVERY_MEM, can_bypass_jump_def] >>
     qpat_x_assum `!bb. _` (qspec_then `a` mp_tac) >> simp[] >> metis_tac[]) >>
  drule do_merge_jump_fn_labels >>
  Cases_on `fn.fn_blocks` >> Cases_on `fn'.fn_blocks` >>
  gvs[fn_labels_def]
QED

Theorem do_merge_jump_projection:
  ALL_DISTINCT (fn_labels fn) /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  (!inst. project (update_phi_bypass a.bb_label b.bb_label inst) = project inst) /\
  (!inst lbl. project (canon_jnz_inst (subst_label_inst b.bb_label lbl inst)) = project inst) /\
  do_merge_jump fn a b lm = SOME (fn', lm') ==>
  MAP (\bb. MAP project bb.bb_instructions) fn'.fn_blocks =
  MAP (\bb. MAP project bb.bb_instructions) (remove_block b.bb_label fn.fn_blocks)
Proof
  strip_tac >> fs[do_merge_jump_def, AllCaseEqs()] >>
  drule lookup_block_member_label >> strip_tac >> gvs[] >>
  simp[replace_block_def, MAP_MAP_o, combinTheory.o_DEF] >>
  irule MAP_CONG >> simp[remove_block_def, MEM_FILTER] >>
  qx_gen_tac `bb` >> strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >> fs[fn_labels_def]) >>
  Cases_on `bb.bb_label = target.bb_label` >>
  Cases_on `bb.bb_label = a.bb_label` >> gvs[] >>
  simp[MAP_MAP_o, combinTheory.o_DEF] >>
  irule MAP_CONG >> simp[] >> gen_tac >> strip_tac >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem do_merge_jump_ids:
  wf_function fn /\ lookup_block a.bb_label fn.fn_blocks = SOME a /\
  do_merge_jump fn a b lm = SOME (fn', lm') ==>
  fn_inst_ids_distinct fn'
Proof
  strip_tac >>
  `MAP (\bb. MAP (\inst. inst.inst_id) bb.bb_instructions) fn'.fn_blocks =
   MAP (\bb. MAP (\inst. inst.inst_id) bb.bb_instructions)
     (remove_block b.bb_label fn.fn_blocks)` by
    (irule do_merge_jump_projection >>
     fs[wf_function_def, update_phi_bypass_shape, canon_jnz_inst_shape,
        subst_label_inst_shape] >> metis_tac[]) >>
  fs[wf_function_def, fn_inst_ids_distinct_def] >>
  irule sublist_ALL_DISTINCT >> goal_assum (drule_at Any) >>
  simp[remove_block_def, sublist_flat_map_filter]
QED

Theorem do_merge_jump_ssa:
  wf_function fn /\ ssa_form fn /\ lookup_block a.bb_label fn.fn_blocks = SOME a /\
  do_merge_jump fn a b lm = SOME (fn', lm') ==>
  ssa_form fn'
Proof
  strip_tac >>
  `MAP (\bb. MAP (\inst. inst.inst_outputs) bb.bb_instructions) fn'.fn_blocks =
   MAP (\bb. MAP (\inst. inst.inst_outputs) bb.bb_instructions)
     (remove_block b.bb_label fn.fn_blocks)` by
    (irule do_merge_jump_projection >>
     fs[wf_function_def, update_phi_bypass_shape, canon_jnz_inst_shape,
        subst_label_inst_shape] >> metis_tac[]) >>
  `MAP FLAT (MAP (\bb. MAP (\inst. inst.inst_outputs) bb.bb_instructions) fn'.fn_blocks) =
   MAP FLAT (MAP (\bb. MAP (\inst. inst.inst_outputs) bb.bb_instructions)
     (remove_block b.bb_label fn.fn_blocks))` by simp[] >>
  fs[ssa_form_def, fn_insts_def, fn_insts_projection_blocks, MAP_MAP_o, combinTheory.o_DEF] >>
  irule sublist_ALL_DISTINCT >> goal_assum (drule_at Any) >>
  simp[remove_block_def, sublist_flat_map_filter]
QED

Theorem get_successors_mem_label:
  MEM lbl (get_successors inst) <=>
  is_terminator inst.inst_opcode /\ MEM (Label lbl) inst.inst_operands
Proof
  simp[get_successors_def, MEM_MAP, MEM_FILTER] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[MEM_MAP, MEM_FILTER] >>
  eq_tac >> rpt strip_tac >> gvs[]
  >- (rename1 `IS_SOME (get_label op)` >> Cases_on `op` >>
      gvs[venomStateTheory.get_label_def]) >>
  qexists `SOME lbl` >> simp[] >> qexists `Label lbl` >> simp[venomStateTheory.get_label_def]
QED

Theorem canon_jnz_inst_successor_subset:
  MEM lbl (get_successors (canon_jnz_inst inst)) ==>
  MEM lbl (get_successors inst)
Proof
  simp[canon_jnz_inst_def] >> rpt CASE_TAC >>
  gvs[get_successors_mem_label, is_terminator_def] >> metis_tac[]
QED

Theorem bypass_source_successor:
  old_lbl <> new_lbl /\ MEM lbl (get_successors
    (if ~is_terminator inst.inst_opcode then inst
     else canon_jnz_inst (subst_label_inst old_lbl new_lbl inst))) ==>
  lbl <> old_lbl /\
  (MEM lbl (get_successors inst) \/ lbl = new_lbl)
Proof
  IF_CASES_TAC >- simp[get_successors_mem_label] >>
  strip_tac >> drule canon_jnz_inst_successor_subset >>
  simp[get_successors_mem_label, subst_label_inst_def, MEM_MAP] >>
  strip_tac >> rename1 `MEM op inst.inst_operands` >>
  Cases_on `op` >> gvs[subst_label_op_def] >>
  rpt IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem bb_succs_update_phi_bypass:
  bb_well_formed bb ==>
  bb_succs (bb with bb_instructions :=
    MAP (update_phi_bypass a_label b_label) bb.bb_instructions) = bb_succs bb
Proof
  strip_tac >> irule bb_succs_map_nonterminators >> simp[] >>
  rpt strip_tac >> `inst.inst_opcode <> PHI` by
    (strip_tac >> fs[is_terminator_def]) >> simp[update_phi_bypass_def]
QED

Theorem bb_bypass_source_successor:
  bb_well_formed bb /\ old_lbl <> new_lbl /\
  MEM lbl (bb_succs (bb with bb_instructions :=
    MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                else canon_jnz_inst (subst_label_inst old_lbl new_lbl inst))
        bb.bb_instructions)) ==>
  lbl <> old_lbl /\ (MEM lbl (bb_succs bb) \/ lbl = new_lbl)
Proof
  strip_tac >> `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >> gvs[bb_succs_def] >>
  qpat_x_assum `MEM lbl _` mp_tac >>
  Cases_on `t` >> simp[LAST_MAP, LAST_DEF] >>
  metis_tac[bypass_source_successor]
QED

Theorem EVERY_replace_block_except:
  P new_bb /\ EVERY (\bb. bb.bb_label <> lbl ==> P bb) bbs ==>
  EVERY P (replace_block lbl new_bb bbs)
Proof
  rewrite_tac[replace_block_def, EVERY_MAP] >>
  simp[EVERY_MEM] >> rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

Theorem can_bypass_jump_unique_pred:
  can_bypass_jump fn a b /\ MEM a fn.fn_blocks /\
  MEM bb fn.fn_blocks /\ MEM b.bb_label (bb_succs bb) ==> bb = a
Proof
  strip_tac >> irule num_preds_one_unique >>
  qexistsl [`fn`, `b.bb_label`] >> fs[can_bypass_jump_def]
QED

Theorem bb_succs_bypass_source_phi:
  bb_well_formed bb ==>
  bb_succs (bb with bb_instructions :=
    MAP (update_phi_bypass a_label b_label)
      (MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                  else canon_jnz_inst (subst_label_inst old_lbl new_lbl inst))
        bb.bb_instructions)) =
  bb_succs (bb with bb_instructions :=
    MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                else canon_jnz_inst (subst_label_inst old_lbl new_lbl inst))
        bb.bb_instructions)
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `MAP (update_phi_bypass a_label b_label) insts` >>
  qabbrev_tac `redirected = bb with bb_instructions := insts` >>
  `bb_well_formed redirected` by
    simp[Abbr `redirected`, Abbr `insts`, bb_well_formed_bypass_source] >>
  mp_tac (Q.INST [`bb` |-> `redirected`] bb_succs_update_phi_bypass) >>
  simp[Abbr `redirected`, Abbr `insts`]
QED

Theorem bb_bypass_source_phi_successor:
  bb_well_formed bb /\ old_lbl <> new_lbl /\
  MEM lbl (bb_succs (bb with bb_instructions :=
    MAP (update_phi_bypass a_label b_label)
      (MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                  else canon_jnz_inst (subst_label_inst old_lbl new_lbl inst))
        bb.bb_instructions))) ==>
  lbl <> old_lbl /\ (MEM lbl (bb_succs bb) \/ lbl = new_lbl)
Proof
  strip_tac >> drule bb_succs_bypass_source_phi >>
  disch_then (qspecl_then [`old_lbl`, `new_lbl`, `b_label`, `a_label`] assume_tac) >>
  fs[] >> metis_tac[bb_bypass_source_successor]
QED

Theorem do_merge_jump_closed:
  wf_function fn /\ lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn', lm') ==>
  fn_succs_closed fn'
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels fn) /\ bb_well_formed a /\ MEM a fn.fn_blocks` by
    (fs[wf_function_def] >> metis_tac[lookup_block_member_label]) >>
  `!bb lbl. MEM bb fn.fn_blocks /\ MEM lbl (bb_succs bb) ==> MEM lbl (fn_labels fn)` by
    fs[wf_function_def, fn_succs_closed_def] >>
  `fn_labels fn' = FILTER (\lbl. lbl <> b.bb_label) (fn_labels fn)` by
    (irule do_merge_jump_fn_labels >> metis_tac[]) >>
  fs[do_merge_jump_def, AllCaseEqs()] >>
  drule lookup_block_member_label >> strip_tac >>
  `bb_well_formed target` by fs[wf_function_def] >>
  `b.bb_label <> target_lbl` by metis_tac[can_bypass_jump_target_distinct] >>
  gvs[] >>
  simp[fn_succs_closed_def] >>
  qmatch_goalsub_abbrev_tac `replace_block a.bb_label newa rest_blocks` >>
  qabbrev_tac `out_blocks = replace_block a.bb_label newa rest_blocks` >>
  `EVERY (\bb. !succ. MEM succ (bb_succs bb) ==>
    MEM succ (FILTER (\lbl. lbl <> b.bb_label) (fn_labels fn))) out_blocks`
    suffices_by (simp[EVERY_MEM] >> metis_tac[]) >>
  unabbrev_all_tac >> irule EVERY_replace_block_except >> conj_tac
  >- (IF_CASES_TAC >> gvs[] >> rpt strip_tac
      >- (drule_all bb_bypass_source_phi_successor >> strip_tac >>
          simp[MEM_FILTER] >> metis_tac[fn_labels_def, MEM_MAP]) >>
      drule_all bb_bypass_source_successor >> strip_tac >>
      simp[MEM_FILTER] >> metis_tac[fn_labels_def, MEM_MAP]) >>
  irule EVERY_replace_block_except >> conj_tac
  >- (simp[bb_succs_update_phi_bypass] >> rpt strip_tac >>
      simp[MEM_FILTER] >> metis_tac[can_bypass_jump_unique_pred]) >>
  simp[remove_block_def, EVERY_MEM, MEM_FILTER] >> rpt strip_tac >>
  simp[MEM_FILTER] >> metis_tac[can_bypass_jump_unique_pred]
QED

Theorem do_merge_jump_wf:
  wf_function fn /\ lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn', lm') ==>
  wf_function fn'
Proof
  strip_tac >>
  `MEM a fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `ALL_DISTINCT (fn_labels fn') /\ fn_has_entry fn'` by
    (irule do_merge_jump_labels_entry >> metis_tac[]) >>
  `EVERY bb_well_formed fn'.fn_blocks` by
    (irule do_merge_jump_bb_wf >> metis_tac[]) >>
  `fn_succs_closed fn'` by (irule do_merge_jump_closed >> metis_tac[]) >>
  `fn_inst_ids_distinct fn'` by (irule do_merge_jump_ids >> metis_tac[]) >>
  fs[wf_function_def, EVERY_MEM]
QED

Theorem do_merge_jump_first_block_no_preds:
  wf_function fn /\ first_block_no_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn', lm') ==>
  first_block_no_preds fn'
Proof
  strip_tac >>
  `MEM a fn.fn_blocks /\ MEM b fn.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  `(HD fn'.fn_blocks).bb_label = (HD fn.fn_blocks).bb_label` by
    (irule do_merge_jump_entry_label >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels fn) /\ bb_well_formed a` by fs[wf_function_def] >>
  `EVERY (\bb. ~MEM (HD fn.fn_blocks).bb_label (bb_succs bb)) fn.fn_blocks` by
    fs[first_block_no_preds_def] >>
  fs[do_merge_jump_def, AllCaseEqs()] >>
  drule lookup_block_member_label >> strip_tac >>
  `bb_well_formed target` by fs[wf_function_def] >>
  `b.bb_label <> target_lbl` by metis_tac[can_bypass_jump_target_distinct] >>
  `target_lbl <> (HD fn.fn_blocks).bb_label` by
    (fs[EVERY_MEM] >> qpat_x_assum `!bb. _` (qspec_then `b` mp_tac) >> simp[]) >>
  gvs[] >> simp[first_block_no_preds_def] >>
  irule EVERY_replace_block >> conj_tac
  >- (IF_CASES_TAC >> gvs[]
      >- (strip_tac >> drule_all bb_bypass_source_phi_successor >>
          strip_tac >> fs[EVERY_MEM] >> metis_tac[]) >>
      strip_tac >> drule_all bb_bypass_source_successor >>
      strip_tac >> fs[EVERY_MEM] >> metis_tac[]) >>
  irule EVERY_replace_block >> simp[bb_succs_update_phi_bypass] >>
  conj_tac >- fs[EVERY_MEM] >>
  simp[remove_block_def, EVERY_FILTER] >> fs[EVERY_MEM]
QED

Theorem try_bypass_property:
  !succs fn' lm' changed.
  P fn /\
  (!b out out_lm. lookup_block b.bb_label fn.fn_blocks = SOME b /\
    can_bypass_jump fn a b /\ do_merge_jump fn a b lm = SOME (out, out_lm) ==> P out) /\
  try_bypass fn lm a succs = (fn', lm', changed) ==> P fn'
Proof
  Induct_on `succs` >- simp[try_bypass_def] >>
  rpt strip_tac >> gvs[Once try_bypass_def, AllCaseEqs()] >>
  metis_tac[lookup_block_member_label]
QED

Theorem try_bypass_wf:
  wf_function fn /\ lookup_block a.bb_label fn.fn_blocks = SOME a /\
  try_bypass fn lm a succs = (fn', lm', changed) ==> wf_function fn'
Proof
  strip_tac >> irule try_bypass_property >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[do_merge_jump_wf]
QED

Theorem try_bypass_ssa:
  wf_function fn /\ ssa_form fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  try_bypass fn lm a succs = (fn', lm', changed) ==> ssa_form fn'
Proof
  strip_tac >> irule try_bypass_property >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[do_merge_jump_ssa]
QED

Theorem try_bypass_first_block_no_preds:
  wf_function fn /\ first_block_no_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  try_bypass fn lm a succs = (fn', lm', changed) ==> first_block_no_preds fn'
Proof
  strip_tac >> irule try_bypass_property >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[do_merge_jump_first_block_no_preds]
QED

Theorem do_merge_jump_every_inst:
  EVERY (\bb. EVERY P bb.bb_instructions) fn.fn_blocks /\ MEM a fn.fn_blocks /\
  (!inst. P inst ==> P (update_phi_bypass a.bb_label b.bb_label inst)) /\
  (!inst lbl. P inst ==> P
    (if ~is_terminator inst.inst_opcode then inst
     else canon_jnz_inst (subst_label_inst b.bb_label lbl inst))) /\
  do_merge_jump fn a b lm = SOME (fn', lm') ==>
  EVERY (\bb. EVERY P bb.bb_instructions) fn'.fn_blocks
Proof
  strip_tac >>
  `EVERY P a.bb_instructions` by (fs[EVERY_MEM] >> metis_tac[]) >>
  fs[do_merge_jump_def, AllCaseEqs()] >>
  drule lookup_block_member_label >> strip_tac >>
  `EVERY P target.bb_instructions` by (fs[EVERY_MEM] >> metis_tac[]) >> gvs[] >>
  irule EVERY_replace_block >> conj_tac
  >- (IF_CASES_TAC >> simp[EVERY_MAP] >> fs[EVERY_MEM] >> metis_tac[]) >>
  irule EVERY_replace_block >> simp[EVERY_MAP, remove_block_def, EVERY_FILTER] >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem phi_well_formed_remove_phi_label:
  !ops. phi_well_formed ops ==> phi_well_formed (remove_phi_label lbl ops)
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, remove_phi_label_def] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[phi_well_formed_def]
QED

Theorem update_phi_bypass_phi_operands:
  (inst.inst_opcode = PHI ==> phi_well_formed inst.inst_operands) ==>
  ((update_phi_bypass a_lbl b_lbl inst).inst_opcode = PHI ==>
    phi_well_formed (update_phi_bypass a_lbl b_lbl inst).inst_operands)
Proof
  Cases_on `inst.inst_opcode = PHI` >> simp[update_phi_bypass_def] >>
  Cases_on `MEM (Label a_lbl) inst.inst_operands` >>
  simp[phi_well_formed_remove_phi_label] >> strip_tac >>
  `phi_well_formed (MAP (subst_label_op b_lbl a_lbl) inst.inst_operands)` by
    simp[phi_well_formed_subst_label_ops] >>
  qmatch_goalsub_abbrev_tac `MAP f _` >>
  `f = subst_label_op b_lbl a_lbl` by
    (simp[FUN_EQ_THM, Abbr `f`] >> Cases >> simp[subst_label_op_def]) >>
  gvs[]
QED

Theorem do_merge_jump_phi_operands:
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI ==>
    phi_well_formed inst.inst_operands) /\ MEM a fn.fn_blocks /\
  do_merge_jump fn a b lm = SOME (fn', lm') ==>
  !inst. MEM inst (fn_insts fn') /\ inst.inst_opcode = PHI ==>
    phi_well_formed inst.inst_operands
Proof
  strip_tac >>
  `EVERY (\bb. EVERY (\inst. inst.inst_opcode = PHI ==>
    phi_well_formed inst.inst_operands) bb.bb_instructions) fn'.fn_blocks` by
    (irule do_merge_jump_every_inst >> goal_assum (drule_at Any) >>
     simp[update_phi_bypass_phi_operands] >> conj_tac
     >- (rpt gen_tac >> IF_CASES_TAC >> simp[canon_jnz_inst_shape,
           subst_label_inst_shape, is_terminator_def] >>
         rpt strip_tac >> gvs[is_terminator_def]) >>
     fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]) >>
  fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]
QED

Theorem canon_subst_jnz_distinct:
  (inst.inst_opcode = JNZ ==>
    ?c t f. inst.inst_operands = [c; Label t; Label f] /\ t <> f) ==>
  (canon_jnz_inst (subst_label_inst old_lbl new_lbl inst)).inst_opcode = JNZ ==>
  ?c t f. (canon_jnz_inst (subst_label_inst old_lbl new_lbl inst)).inst_operands =
    [c; Label t; Label f] /\ t <> f
Proof
  Cases_on `inst.inst_opcode = JNZ`
  >- (simp[] >> strip_tac >> gvs[subst_label_inst_def, subst_label_op_def] >>
      rpt IF_CASES_TAC >> gvs[canon_jnz_inst_def] >>
      rpt IF_CASES_TAC >> gvs[]) >>
  simp[canon_jnz_inst_def, subst_label_inst_def] >> rpt CASE_TAC >> simp[]
QED

Theorem do_merge_jump_jnz_distinct:
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = JNZ ==>
    ?c t f. inst.inst_operands = [c; Label t; Label f] /\ t <> f) /\
  MEM a fn.fn_blocks /\ do_merge_jump fn a b lm = SOME (fn', lm') ==>
  !inst. MEM inst (fn_insts fn') /\ inst.inst_opcode = JNZ ==>
    ?c t f. inst.inst_operands = [c; Label t; Label f] /\ t <> f
Proof
  strip_tac >>
  `EVERY (\bb. EVERY (\inst. inst.inst_opcode = JNZ ==>
    ?c t f. inst.inst_operands = [c; Label t; Label f] /\ t <> f)
      bb.bb_instructions) fn'.fn_blocks` by
    (irule do_merge_jump_every_inst >> goal_assum (drule_at Any) >> simp[] >>
     rpt conj_tac
     >- (rpt gen_tac >> IF_CASES_TAC >> simp[canon_subst_jnz_distinct])
     >- (gen_tac >> Cases_on `inst.inst_opcode = PHI` >>
         simp[update_phi_bypass_def] >> rpt IF_CASES_TAC >> simp[]) >>
     fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]) >>
  fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]
QED

Theorem try_bypass_phi_operands:
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI ==>
    phi_well_formed inst.inst_operands) /\ MEM a fn.fn_blocks /\
  try_bypass fn lm a succs = (fn', lm', changed) ==>
  !inst. MEM inst (fn_insts fn') /\ inst.inst_opcode = PHI ==>
    phi_well_formed inst.inst_operands
Proof
  qid_spec_tac `succs` >> Induct >- simp[try_bypass_def] >>
  rpt strip_tac >> gvs[Once try_bypass_def, AllCaseEqs()] >>
  metis_tac[do_merge_jump_phi_operands]
QED

Theorem try_bypass_jnz_distinct:
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = JNZ ==>
    ?c t f. inst.inst_operands = [c; Label t; Label f] /\ t <> f) /\
  MEM a fn.fn_blocks /\ try_bypass fn lm a succs = (fn', lm', changed) ==>
  !inst. MEM inst (fn_insts fn') /\ inst.inst_opcode = JNZ ==>
    ?c t f. inst.inst_operands = [c; Label t; Label f] /\ t <> f
Proof
  qid_spec_tac `succs` >> Induct >- simp[try_bypass_def] >>
  rpt strip_tac >> gvs[Once try_bypass_def, AllCaseEqs()] >>
  metis_tac[do_merge_jump_jnz_distinct]
QED

Theorem collapse_property_joint:
  !P.
  (!func a b. P func /\
     lookup_block a.bb_label func.fn_blocks = SOME a /\
     lookup_block b.bb_label func.fn_blocks = SOME b /\
     can_merge_blocks func a b ==>
     P (func with fn_blocks :=
       update_succ_phi_labels b.bb_label a.bb_label
         (replace_block a.bb_label (merge_blocks a b)
           (remove_block b.bb_label func.fn_blocks))
         (bb_succs (merge_blocks a b)))) /\
  (!func lm a succs func' lm'. P func /\
     lookup_block a.bb_label func.fn_blocks = SOME a /\
     try_bypass func lm a succs = (func',lm',T) ==> P func') ==>
  ((!func lm visited lbl. P func ==>
      P (FST (collapse_dfs func lm visited lbl))) /\
   (!func lm visited succs. P func ==>
      P (FST (collapse_dfs_succs func lm visited succs))))
Proof
  gen_tac >> strip_tac >> ho_match_mp_tac collapse_dfs_ind >> rpt conj_tac
  >- suspend "dfs"
  >- simp[collapse_dfs_def]
  >> suspend "succs"
QED

Resume collapse_property_joint[dfs]:
  rpt strip_tac >> simp[NoAsms, Once collapse_dfs_def] >>
  Cases_on `lookup_block lbl func.fn_blocks` >- simp[] >>
  rename1 `lookup_block lbl func.fn_blocks = SOME bb` >>
  Cases_on `bb_succs bb` >- (Cases_on `MEM lbl visited` >> gvs[try_bypass_def]) >>
  Cases_on `t`
  >- (Cases_on `lookup_block h func.fn_blocks`
      >- (Cases_on `MEM lbl visited` >> gvs[]) >>
      rename1 `lookup_block h func.fn_blocks = SOME next_bb` >>
      Cases_on `can_merge_blocks func bb next_bb`
      >- (gvs[] >> first_x_assum irule >>
          `bb.bb_label = lbl /\ next_bb.bb_label = h` by
            metis_tac[lookup_block_member_label] >> metis_tac[]) >>
      Cases_on `MEM lbl visited` >> gvs[]) >>
  Cases_on `try_bypass func lm bb (h::h'::t')` >> PairCases_on `r` >>
  `lookup_block bb.bb_label func.fn_blocks = SOME bb` by
    metis_tac[lookup_block_member_label] >>
  Cases_on `r1`
  >- (gvs[] >> `P q` by metis_tac[] >> gvs[]) >>
  drule_all try_bypass_failed_unchanged >> strip_tac >>
  gvs[] >> Cases_on `MEM lbl visited` >> gvs[]
QED

Resume collapse_property_joint[succs]:
  rpt strip_tac >> simp[NoAsms, Once collapse_dfs_def] >>
  Cases_on `collapse_dfs func lm visited lbl` >> PairCases_on `r` >> gvs[]
QED

Finalise collapse_property_joint

Theorem collapse_wf_joint:
  (!func lm visited lbl. wf_function func ==>
    wf_function (FST (collapse_dfs func lm visited lbl))) /\
  (!func lm visited succs. wf_function func ==>
    wf_function (FST (collapse_dfs_succs func lm visited succs)))
Proof
  ho_match_mp_tac collapse_dfs_ind >> rpt conj_tac
  >- suspend "dfs"
  >- simp[collapse_dfs_def]
  >> suspend "succs"
QED

Resume collapse_wf_joint[dfs]:
  rpt strip_tac >> simp[NoAsms, Once collapse_dfs_def] >>
  Cases_on `lookup_block lbl func.fn_blocks` >- simp[] >>
  rename1 `lookup_block lbl func.fn_blocks = SOME bb` >>
  Cases_on `bb_succs bb` >- (Cases_on `MEM lbl visited` >> gvs[try_bypass_def]) >>
  Cases_on `t`
  >- (Cases_on `lookup_block h func.fn_blocks`
      >- (Cases_on `MEM lbl visited` >> gvs[]) >>
      rename1 `lookup_block h func.fn_blocks = SOME next_bb` >>
      Cases_on `can_merge_blocks func bb next_bb`
      >- (gvs[] >> first_x_assum irule >>
          `bb.bb_label = lbl /\ next_bb.bb_label = h` by
            metis_tac[lookup_block_member_label] >>
          metis_tac[chain_merge_wf]) >>
      Cases_on `MEM lbl visited` >> gvs[]) >>
  Cases_on `try_bypass func lm bb (h::h'::t')` >> PairCases_on `r` >>
  `lookup_block bb.bb_label func.fn_blocks = SOME bb` by
    metis_tac[lookup_block_member_label] >>
  `wf_function q` by metis_tac[try_bypass_wf] >>
  Cases_on `r1` >> gvs[] >> Cases_on `MEM lbl visited` >> gvs[]
QED

Resume collapse_wf_joint[succs]:
  rpt strip_tac >> simp[Once collapse_dfs_def] >>
  Cases_on `collapse_dfs func lm visited lbl` >> PairCases_on `r` >> gvs[]
QED

Finalise collapse_wf_joint
