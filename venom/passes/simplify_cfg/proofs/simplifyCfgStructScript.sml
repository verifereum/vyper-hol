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
