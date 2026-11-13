Theory simplifyCfgRetpc
Ancestors
  unitShapeDefs simplifyCfgDefs simplifyCfgShape simplifyCfgLabelProps rich_list
  simplifyCfgStruct cfgTransform venomWf venomInst list
  cfgNormBase simplifyCfgBypassPhi simplifyCfgPhiSemantics venomWfProps
  venomExecSemantics alist option
  simplifyCfgRepairDataflow simplifyCfgCollapseShape simplifyCfgPhiShape
  simplifyCfgChainDataflow simplifyCfgBypassShape venomInstIdsProps mmWfProofs simplifyCfgWfssa
  simplifyCfgBypassDataflow simplifyCfgBypassClosure
  simplifyCfgFixupShape simplifyCfgFixupClosure

(* Removing dead blocks computes precisely the predecessor set used by
   reachable_fn.  Use membership: order is irrelevant to PHI filtering. *)
Theorem retpc_initial_pred_mem:
  wf_function f ==>
  (MEM l (pred_labels (remove_unreachable_blocks f) lbl) <=>
   MEM l (reachable_preds f lbl))
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels f)` by gvs[wf_function_def] >>
  Cases_on `fn_entry_label f` >-
    gvs[wf_function_def, fn_has_entry_def, fn_entry_label_def, entry_block_def,
        AllCaseEqs(), NULL_EQ] >>
  simp[pred_labels_def, block_preds_def, remove_unreachable_blocks_def,
       reachable_preds_def, MEM_MAP, MEM_FILTER,
       GSYM fn_reachable_iff_reachable] >>
  simp[fn_cfg_edge_def] >> metis_tac[]
QED

(* An empty PHI has no variable edge; a singleton retains exactly its
   variable edge as an ASSIGN.  This also checks malformed singleton lists
   are excluded by the instruction well-formedness hypothesis. *)
Theorem retpc_fix_phi_edge_iff:
  inst_wf i /\ i.inst_opcode = PHI ==>
  ((MEM x (fix_phi_inst ps i).inst_outputs /\
    (((fix_phi_inst ps i).inst_opcode = ASSIGN /\
      (fix_phi_inst ps i).inst_operands = [Var y]) \/
     ((fix_phi_inst ps i).inst_opcode = PHI /\
      MEM (Var y) (fix_phi_inst ps i).inst_operands))) <=>
   (MEM x i.inst_outputs /\
    MEM (Var y) (filter_phi_ops ps i.inst_operands)))
Proof
  strip_tac >>
  `phi_well_formed (filter_phi_ops ps i.inst_operands)` by
    (irule filter_phi_ops_well_formed >> gvs[inst_wf_def]) >>
  simp[fix_phi_inst_def] >>
  Cases_on `filter_phi_ops ps i.inst_operands` >> gvs[] >>
  rename1 `h::rest` >> Cases_on `rest` >> gvs[phi_well_formed_def] >>
  rename1 `h::v::rest` >> Cases_on `rest` >> gvs[] >>
  Cases_on `h` >> Cases_on `v` >> gvs[phi_well_formed_def] >> metis_tac[]
QED

Theorem retpc_filter_phi_ops_cong:
  !ps ops. (!l. MEM l ps <=> MEM l qs) ==>
  filter_phi_ops ps ops = filter_phi_ops qs ops
Proof
  recInduct filter_phi_ops_ind >> rpt strip_tac >>
  simp[filter_phi_ops_def]
QED

Theorem retpc_initial_inst_mem:
  wf_function f ==>
  (MEM j (fn_insts (fix_all_phis (remove_unreachable_blocks f))) <=>
   ?bb i. MEM bb f.fn_blocks /\ fn_reachable f bb.bb_label /\
          MEM i bb.bb_instructions /\
          j = fix_phi_inst (reachable_preds f bb.bb_label) i)
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels f)` by gvs[wf_function_def] >>
  `!lbl ops. filter_phi_ops
      (pred_labels (remove_unreachable_blocks f) lbl) ops =
      filter_phi_ops (reachable_preds f lbl) ops` by
    (rpt gen_tac >> irule retpc_filter_phi_ops_cong >>
     simp[retpc_initial_pred_mem]) >>
  Cases_on `fn_entry_label f` >-
    gvs[wf_function_def, fn_has_entry_def, fn_entry_label_def,
        entry_block_def, AllCaseEqs(), NULL_EQ] >>
  simp[fn_insts_def, MEM_fn_insts_blocks_iff, fix_all_phis_def,
       MEM_MAP, PULL_EXISTS, fix_phis_in_block_mem,
       remove_unreachable_blocks_def, MEM_FILTER,
       GSYM fn_reachable_iff_reachable] >>
  qpat_x_assum `!lbl ops. _` mp_tac >>
  simp[remove_unreachable_blocks_def, GSYM fn_reachable_iff_reachable] >>
  strip_tac >> simp[fix_phi_inst_def] >> metis_tac[]
QED

Theorem retpc_initial_seed_fields:
  (MEM x (fix_phi_inst (reachable_preds f lbl) i).inst_outputs /\
   (fix_phi_inst (reachable_preds f lbl) i).inst_opcode = RETPC_PARAM) <=>
  (MEM x (reachable_inst f lbl i).inst_outputs /\
   (reachable_inst f lbl i).inst_opcode = RETPC_PARAM)
Proof
  Cases_on `i.inst_opcode = PHI` >-
    (simp[reachable_inst_fields] >> strip_tac >>
     drule_at Any fix_phi_inst_opcode_source >> simp[]) >>
  simp[fix_phi_inst_def, reachable_inst_def]
QED

Theorem retpc_initial_edge_fields:
  inst_wf i ==>
  ((MEM x (fix_phi_inst (reachable_preds f lbl) i).inst_outputs /\
    (((fix_phi_inst (reachable_preds f lbl) i).inst_opcode = ASSIGN /\
      (fix_phi_inst (reachable_preds f lbl) i).inst_operands = [Var y]) \/
     ((fix_phi_inst (reachable_preds f lbl) i).inst_opcode = PHI /\
      MEM (Var y) (fix_phi_inst (reachable_preds f lbl) i).inst_operands))) <=>
   (MEM x (reachable_inst f lbl i).inst_outputs /\
    (((reachable_inst f lbl i).inst_opcode = ASSIGN /\
      (reachable_inst f lbl i).inst_operands = [Var y]) \/
     ((reachable_inst f lbl i).inst_opcode = PHI /\
      MEM (Var y) (reachable_inst f lbl i).inst_operands))))
Proof
  strip_tac >> Cases_on `i.inst_opcode = PHI` >-
    (drule_all retpc_fix_phi_edge_iff >>
     disch_then (qspecl_then [`y`, `x`, `reachable_preds f lbl`] mp_tac) >>
     simp[reachable_inst_def]) >>
  simp[reachable_inst_def, fix_phi_inst_def]
QED

Theorem retpc_initial_seed_iff:
  wf_function f ==>
  ((?j. MEM j (fn_insts (fix_all_phis (remove_unreachable_blocks f))) /\
        j.inst_opcode = RETPC_PARAM /\ MEM x j.inst_outputs) <=>
   (?j. MEM j (fn_insts (reachable_fn f)) /\
        j.inst_opcode = RETPC_PARAM /\ MEM x j.inst_outputs))
Proof
  strip_tac >>
  simp[retpc_initial_inst_mem, MEM_reachable_fn_insts, PULL_EXISTS] >>
  metis_tac[retpc_initial_seed_fields]
QED

Theorem retpc_initial_edge_iff:
  wf_function f /\ fn_inst_wf f ==>
  ((?j. MEM j (fn_insts (fix_all_phis (remove_unreachable_blocks f))) /\
        MEM x j.inst_outputs /\
        ((j.inst_opcode = ASSIGN /\ j.inst_operands = [Var y]) \/
         (j.inst_opcode = PHI /\ MEM (Var y) j.inst_operands))) <=>
   (?j. MEM j (fn_insts (reachable_fn f)) /\ MEM x j.inst_outputs /\
        ((j.inst_opcode = ASSIGN /\ j.inst_operands = [Var y]) \/
         (j.inst_opcode = PHI /\ MEM (Var y) j.inst_operands))))
Proof
  strip_tac >>
  `!bb i. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions ==> inst_wf i` by
    gvs[fn_inst_wf_def, fn_insts_def, MEM_fn_insts_blocks_iff] >>
  simp[retpc_initial_inst_mem, MEM_reachable_fn_insts, PULL_EXISTS] >>
  metis_tac[retpc_initial_edge_fields]
QED

Theorem retpc_initial_closure_iff:
  wf_function f /\ fn_inst_wf f ==>
  (retpc_var (fix_all_phis (remove_unreachable_blocks f)) x <=>
   retpc_var (reachable_fn f) x)
Proof
  strip_tac >> simp[retpc_var_def] >> eq_tac
  >- (strip_tac >> drule copy_phi_var_transport >> disch_then irule >>
      conj_tac
      >- metis_tac[retpc_initial_edge_iff]
      >> metis_tac[retpc_initial_seed_iff]) >>
  strip_tac >> drule copy_phi_var_transport >> disch_then irule >>
  conj_tac
  >- (rpt strip_tac >> drule_all retpc_initial_edge_iff >>
      disch_then (qspecl_then [`w`, `v`] mp_tac) >> metis_tac[]) >>
  metis_tac[retpc_initial_seed_iff]
QED

Theorem retpc_initial_return_mem:
  wf_function f /\ MEM j.inst_opcode [RET; RETFMP; DRET] ==>
  (MEM j (fn_insts (fix_all_phis (remove_unreachable_blocks f))) <=>
   MEM j (fn_insts (reachable_fn f)))
Proof
  strip_tac >>
  simp[retpc_initial_inst_mem, MEM_reachable_fn_insts] >> eq_tac
  >- (strip_tac >>
      `i.inst_opcode = j.inst_opcode` by
        (irule fix_phi_inst_opcode_source >> gvs[] >>
         qexists_tac `reachable_preds f bb.bb_label` >> simp[]) >>
      `i.inst_opcode <> PHI` by (fs[] >> gvs[]) >>
      `i = j` by
        (qpat_x_assum `j = _` mp_tac >> simp[fix_phi_inst_def]) >>
      qpat_x_assum `j = fix_phi_inst _ _` kall_tac >>
      gvs[] >> qexistsl_tac [`bb`, `i`] >> simp[reachable_inst_def]) >>
  strip_tac >>
  `i.inst_opcode = j.inst_opcode` by gvs[reachable_inst_fields] >>
  `i.inst_opcode <> PHI` by (fs[] >> gvs[]) >>
  `i = j` by
    (qpat_x_assum `j = _` mp_tac >> simp[reachable_inst_def]) >>
  qpat_x_assum `j = reachable_inst _ _ _` kall_tac >>
  gvs[] >> qexistsl_tac [`bb`, `i`] >> simp[fix_phi_inst_def]
QED

Theorem retpc_phi_var_pair:
  !ops. phi_well_formed ops ==>
  (MEM (Var y) ops <=> ?l. MEM (l,y) (phi_pairs ops))
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, phi_pairs_def] >> metis_tac[]
QED

Theorem retpc_phi_pair_selected:
  phi_well_formed ops /\ ALL_DISTINCT (MAP FST (phi_pairs ops)) /\
  MEM (p,y) (phi_pairs ops) ==>
  resolve_phi p ops = SOME (Var y)
Proof
  strip_tac >> simp[resolve_phi_phi_pairs] >>
  `ALOOKUP (phi_pairs ops) p = SOME y` by
    (irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]) >> simp[]
QED

Theorem retpc_bypass_var_iff:
  bb_well_formed bb /\ phi_values_agree a b bb.bb_instructions /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
  phi_well_formed i.inst_operands /\
  ALL_DISTINCT (MAP FST (phi_pairs i.inst_operands)) /\ a <> b ==>
  (MEM (Var y) (update_phi_bypass a b i).inst_operands <=>
   MEM (Var y) i.inst_operands)
Proof
  strip_tac >> eq_tac
  >- metis_tac[update_phi_bypass_var_subset] >>
  strip_tac >>
  `?p. MEM (p,y) (phi_pairs i.inst_operands)` by
    metis_tac[retpc_phi_var_pair] >>
  `resolve_phi p i.inst_operands = SOME (Var y)` by
    (irule retpc_phi_pair_selected >> simp[]) >>
  drule_all scfg_update_phi_bypass_selected >> strip_tac >>
  drule resolve_phi_pair >> strip_tac >>
  metis_tac[phi_pairs_mem_var]
QED

Theorem retpc_reachable_unique_writer:
  wf_function f /\ retpc_shape_ok f /\ retpc_var (reachable_fn f) x /\
  MEM i (fn_insts (reachable_fn f)) /\
  MEM j (fn_insts (reachable_fn f)) /\
  MEM x i.inst_outputs /\ MEM x j.inst_outputs ==> i = j
Proof
  strip_tac >>
  `retpc_var f x` by metis_tac[reachable_retpc_var] >>
  qpat_x_assum `MEM i _` mp_tac >>
  qpat_x_assum `MEM j _` mp_tac >>
  simp[MEM_reachable_fn_insts] >> rpt strip_tac >> gvs[] >>
  `i' = i''` by
    (qpat_x_assum `retpc_shape_ok f` mp_tac >>
     simp[retpc_shape_ok_def] >>
     gvs[reachable_inst_fields, fn_insts_def, MEM_fn_insts_blocks_iff] >>
     metis_tac[]) >>
  `bb = bb'` by
    (irule scfg_instruction_block_unique >>
     gvs[wf_function_def] >> metis_tac[]) >> simp[]
QED

Theorem retpc_reachable_writer:
  wf_function f /\ retpc_shape_ok f /\
  MEM i (fn_insts (reachable_fn f)) /\ MEM x i.inst_outputs /\
  retpc_var (reachable_fn f) x ==>
  i.inst_opcode = RETPC_PARAM \/
  (i.inst_opcode = ASSIGN /\ ?y. i.inst_operands = [Var y] /\
                                  retpc_var (reachable_fn f) y) \/
  (i.inst_opcode = PHI /\
   (?y. MEM (Var y) i.inst_operands /\ retpc_var (reachable_fn f) y) /\
   (!y. MEM (Var y) i.inst_operands ==> retpc_var (reachable_fn f) y))
Proof
  strip_tac >>
  qpat_assum `retpc_var _ x`
    (strip_assume_tac o ONCE_REWRITE_RULE[copy_phi_var_cases] o
     REWRITE_RULE[retpc_var_def]) >>
  rename1 `MEM inst (fn_insts (reachable_fn f))` >>
  `inst = i` by (irule retpc_reachable_unique_writer >> metis_tac[]) >>
  gvs[GSYM retpc_var_def] >>
  qpat_x_assum `retpc_shape_ok f` mp_tac >>
  simp[retpc_shape_ok_def] >> metis_tac[]
QED

Theorem retpc_initial_unique_writer:
  wf_function f /\ fn_inst_wf f /\ retpc_shape_ok f /\
  retpc_var (fix_all_phis (remove_unreachable_blocks f)) x /\
  MEM i (fn_insts (fix_all_phis (remove_unreachable_blocks f))) /\
  MEM j (fn_insts (fix_all_phis (remove_unreachable_blocks f))) /\
  MEM x i.inst_outputs /\ MEM x j.inst_outputs ==> i = j
Proof
  strip_tac >>
  `retpc_var f x` by
    metis_tac[retpc_initial_closure_iff, reachable_retpc_var] >>
  qpat_x_assum `MEM i _` mp_tac >>
  qpat_x_assum `MEM j _` mp_tac >>
  simp[retpc_initial_inst_mem] >> rpt strip_tac >> gvs[] >>
  `i' = i''` by
    (qpat_x_assum `retpc_shape_ok f` mp_tac >>
     simp[retpc_shape_ok_def] >>
     `MEM x i'.inst_outputs /\ MEM x i''.inst_outputs` by
       metis_tac[fix_phi_inst_outputs_subset] >>
     simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `bb = bb'` by
    (irule scfg_instruction_block_unique >>
     gvs[wf_function_def] >> metis_tac[]) >> simp[]
QED

Theorem retpc_initial_phi_fields:
  (fix_phi_inst (reachable_preds f lbl) i).inst_opcode = PHI ==>
  fix_phi_inst (reachable_preds f lbl) i = reachable_inst f lbl i
Proof
  Cases_on `i.inst_opcode = PHI` >> simp[fix_phi_inst_def, reachable_inst_def] >>
  Cases_on `filter_phi_ops (reachable_preds f lbl) i.inst_operands` >> gvs[] >>
  rename1 `h::rest` >> Cases_on `rest` >> gvs[] >>
  rename1 `h::v::rest` >> Cases_on `rest` >> gvs[]
QED

Theorem retpc_initial_phi_uniform:
  wf_function f /\ fn_inst_wf f /\ retpc_shape_ok f /\
  MEM i (fn_insts (fix_all_phis (remove_unreachable_blocks f))) /\
  i.inst_opcode = PHI /\ MEM (Var x) i.inst_operands /\
  MEM (Var y) i.inst_operands /\
  retpc_var (fix_all_phis (remove_unreachable_blocks f)) x ==>
  retpc_var (fix_all_phis (remove_unreachable_blocks f)) y
Proof
  strip_tac >>
  `MEM i (fn_insts (reachable_fn f))` by
    (qpat_x_assum `MEM i _` mp_tac >> simp[retpc_initial_inst_mem] >>
     strip_tac >>
     `fix_phi_inst (reachable_preds f bb.bb_label) i' =
      reachable_inst f bb.bb_label i'` by
       (irule retpc_initial_phi_fields >> metis_tac[]) >>
     simp[MEM_reachable_fn_insts] >> metis_tac[]) >>
  `retpc_var (reachable_fn f) x` by metis_tac[retpc_initial_closure_iff] >>
  `retpc_var (reachable_fn f) y` by
    (qpat_x_assum `retpc_shape_ok f` mp_tac >>
     simp[retpc_shape_ok_def] >> metis_tac[]) >>
  metis_tac[retpc_initial_closure_iff]
QED

Theorem retpc_initial_writer:
  wf_function f /\ fn_inst_wf f /\ retpc_shape_ok f /\
  MEM i (fn_insts (fix_all_phis (remove_unreachable_blocks f))) /\
  MEM x i.inst_outputs /\
  retpc_var (fix_all_phis (remove_unreachable_blocks f)) x ==>
  i.inst_opcode = RETPC_PARAM \/
  (i.inst_opcode = ASSIGN /\ ?y. i.inst_operands = [Var y] /\
    retpc_var (fix_all_phis (remove_unreachable_blocks f)) y) \/
  (i.inst_opcode = PHI /\
   (?y. MEM (Var y) i.inst_operands /\
        retpc_var (fix_all_phis (remove_unreachable_blocks f)) y) /\
   (!y. MEM (Var y) i.inst_operands ==>
        retpc_var (fix_all_phis (remove_unreachable_blocks f)) y))
Proof
  strip_tac >>
  qpat_assum `retpc_var _ x`
    (strip_assume_tac o ONCE_REWRITE_RULE[copy_phi_var_cases] o
     REWRITE_RULE[retpc_var_def]) >>
  rename1 `MEM inst (fn_insts (fix_all_phis (remove_unreachable_blocks f)))` >>
  `inst = i` by (irule retpc_initial_unique_writer >> metis_tac[]) >>
  gvs[GSYM retpc_var_def] >> metis_tac[retpc_initial_phi_uniform]
QED

Theorem retpc_all_reachable_pred_mem:
  (!bb. MEM bb f.fn_blocks ==> fn_reachable f bb.bb_label) ==>
  (MEM l (reachable_preds f lbl) <=> MEM l (pred_labels f lbl))
Proof
  simp[reachable_preds_def, pred_labels_def, block_preds_def,
       MEM_FILTER, MEM_MAP, fn_cfg_edge_def] >> metis_tac[]
QED

Theorem retpc_normalized_reachable_identity:
  fn_inst_wf f /\
  (!bb. MEM bb f.fn_blocks ==> fn_reachable f bb.bb_label) /\
  (!bb i l. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions /\
     i.inst_opcode = PHI /\ MEM (Label l) i.inst_operands ==>
     MEM l (pred_labels f bb.bb_label)) ==>
  reachable_fn f = f
Proof
  strip_tac >>
  `!bb i. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions ==>
     reachable_inst f bb.bb_label i = i` by
    (rpt strip_tac >> Cases_on `i.inst_opcode = PHI` >>
     simp[reachable_inst_def] >>
     `inst_wf i` by
       (fs[fn_inst_wf_def, fn_insts_def, MEM_fn_insts_blocks_iff] >>
        metis_tac[]) >>
     `filter_phi_ops (reachable_preds f bb.bb_label) i.inst_operands =
      i.inst_operands` suffices_by simp[] >>
     irule filter_phi_ops_all_preds >>
     gvs[inst_wf_def] >> rpt strip_tac >>
     simp[retpc_all_reachable_pred_mem] >>
     metis_tac[phi_pairs_mem_label]) >>
  simp[reachable_fn_def, ir_function_component_equality] >>
  `FILTER (\bb. fn_reachable f bb.bb_label) f.fn_blocks = f.fn_blocks` by
    (simp[FILTER_EQ_ID, EVERY_MEM]) >>
  simp[] >> irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
  simp[basic_block_component_equality] >>
  irule LIST_EQ >> simp[EL_MAP] >> metis_tac[EL_MEM]
QED

Theorem retpc_initial_reachable_identity:
  wf_function f /\ fn_inst_wf f ==>
  reachable_fn (fix_all_phis (remove_unreachable_blocks f)) =
  fix_all_phis (remove_unreachable_blocks f)
Proof
  strip_tac >>
  `wf_function (remove_unreachable_blocks f)` by
    simp[remove_unreachable_blocks_wf] >>
  `fn_inst_wf (remove_unreachable_blocks f)` by
    simp[simplifyCfgDefsTheory.remove_unreachable_blocks_fn_inst_wf] >>
  irule retpc_normalized_reachable_identity >> conj_tac
  >- (rpt strip_tac >>
      irule simplifyCfgPhiShapeTheory.fix_all_phis_phi_preds >>
      gvs[wf_function_def, fn_inst_wf_def, EVERY_MEM,
          fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  conj_tac
  >- (`cfgWf$all_reachable (remove_unreachable_blocks f)` by
        simp[cfgWfTheory.all_reachable_def, remove_unreachable_blocks_reachable] >>
      drule_all fix_all_phis_all_reachable >>
      simp[cfgWfTheory.all_reachable_def]) >>
  simp[simplifyCfgReachusesTheory.fix_all_phis_fn_inst_wf]
QED

Theorem retpc_initial_shape:
  wf_function f /\ fn_inst_wf f /\ retpc_shape_ok f ==>
  retpc_shape_ok (fix_all_phis (remove_unreachable_blocks f))
Proof
  strip_tac >>
  simp[retpc_shape_ok_def, retpc_initial_reachable_identity] >>
  conj_tac
  >- (rpt strip_tac >>
      `MEM inst (fn_insts (reachable_fn f))` by
        metis_tac[retpc_initial_return_mem, MEM] >>
      `?front x. inst.inst_operands = front ++ [Var x] /\
                 retpc_var (reachable_fn f) x` by
        (qpat_x_assum `retpc_shape_ok f` mp_tac >>
         simp[retpc_shape_ok_def] >> metis_tac[]) >>
      metis_tac[retpc_initial_closure_iff]) >>
  conj_tac >- metis_tac[retpc_initial_phi_uniform] >>
  conj_tac >- metis_tac[retpc_initial_writer] >>
  metis_tac[retpc_initial_unique_writer]
QED

Theorem retpc_initial_phi_distinct:
  wf_function f /\ fn_inst_wf f /\ fn_shape_ok f /\
  MEM j (fn_insts (fix_all_phis (remove_unreachable_blocks f))) /\
  j.inst_opcode = PHI ==>
  ALL_DISTINCT (MAP FST (phi_pairs j.inst_operands))
Proof
  strip_tac >> drule retpc_initial_inst_mem >>
  disch_then (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  `i.inst_opcode = PHI` by
    (Cases_on `i.inst_opcode = PHI` >> gvs[fix_phi_inst_def]) >>
  `inst_wf i` by
    (fs[fn_inst_wf_def] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP FST (phi_pairs i.inst_operands))` by
    (fs[fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def,
        fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `phi_well_formed i.inst_operands` by gvs[inst_wf_def] >>
  gvs[] >>
  drule_all simplifyCfgPhiRepairTheory.fix_phi_inst_surviving_pairs >>
  disch_then SUBST1_TAC >>
  `MAP FST (FILTER (\p. MEM (FST p) (reachable_preds f bb.bb_label))
      (phi_pairs i.inst_operands)) =
   FILTER (\l. MEM l (reachable_preds f bb.bb_label))
      (MAP FST (phi_pairs i.inst_operands))` by
    simp[rich_listTheory.FILTER_MAP, combinTheory.o_DEF] >>
  simp[FILTER_ALL_DISTINCT]
QED

val retpc_structural = ``\e f.
  ALL_DISTINCT (fn_labels f) /\ f.fn_blocks <> [] /\
  EVERY bb_well_formed f.fn_blocks /\
  EVERY inst_wf (fn_insts f) /\ EVERY label_positions_ok (fn_insts f) /\
  first_block_no_preds f /\ fn_succs_closed f /\
  (HD f.fn_blocks).bb_label = e``;

Theorem retpc_initial_structural:
  wf_function f /\ fn_inst_wf f /\ fn_shape_ok f /\ first_block_no_preds f ==>
  ^retpc_structural (HD f.fn_blocks).bb_label
    (fix_all_phis (remove_unreachable_blocks f))
Proof
  strip_tac >>
  irule fix_all_phis_structural_shape >>
  irule remove_unreachable_blocks_structural_shape >>
  gvs[wf_function_def, fn_inst_wf_def, fn_shape_ok_def,
      fn_has_entry_def, fn_entry_label_def, entry_block_def,
      EVERY_MEM, inst_shape_ok_def, fn_insts_def, MEM_fn_insts_blocks_iff,
      AllCaseEqs()] >> metis_tac[]
QED

Theorem retpc_update_succ_exists:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bs) /\
  (!i. i.inst_opcode = PHI ==> (P (subst_label_inst old new i) <=> P i)) ==>
  ((?i. (?bb. MEM bb (update_succ_phi_labels old new bs succs) /\
           MEM i bb.bb_instructions) /\ P i) <=>
   (?i. (?bb. MEM bb bs /\ MEM i bb.bb_instructions) /\ P i))
Proof
  strip_tac >>
  `MAP (\bb. (bb.bb_label, MAP P bb.bb_instructions))
     (update_succ_phi_labels old new bs succs) =
   MAP (\bb. (bb.bb_label, MAP P bb.bb_instructions)) bs` by
    (irule update_succ_phi_labels_block_projection >> simp[]) >>
  pop_assum (mp_tac o Q.AP_TERM `MEM T o FLAT o MAP SND`) >>
  simp[MAP_MAP_o, combinTheory.o_DEF, MEM_FLAT, MEM_MAP,
       PULL_EXISTS] >> metis_tac[]
QED

Theorem retpc_chain_exists:
  wf_function f /\ fn_inst_wf f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\
  can_merge_blocks f a b /\
  (!i. P i ==> i.inst_outputs <> []) /\
  (!i. i.inst_opcode = PHI ==> (P (subst_label_inst b.bb_label a.bb_label i) <=> P i)) ==>
  ((?i. MEM i (fn_insts (f with fn_blocks :=
      update_succ_phi_labels b.bb_label a.bb_label
        (replace_block a.bb_label (merge_blocks a b)
          (remove_block b.bb_label f.fn_blocks)) (bb_succs (merge_blocks a b)))) /\ P i) <=>
   (?i. MEM i (fn_insts f) /\ P i))
Proof
  strip_tac >>
  `MEM a f.fn_blocks /\ MEM b f.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  `a.bb_label <> b.bb_label` by gvs[can_merge_blocks_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label)
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label f.fn_blocks)))` by
    (irule chain_merge_base_labels >> gvs[wf_function_def]) >>
  simp[fn_insts_def, MEM_fn_insts_blocks_iff] >>
  drule_all retpc_update_succ_exists >>
  disch_then (qspec_then `bb_succs (merge_blocks a b)` SUBST1_TAC) >>
  eq_tac
  >- (simp[replace_block_def, remove_block_def, MEM_MAP, MEM_FILTER,
           merge_blocks_def, MEM_APPEND] >>
      rpt strip_tac >> gvs[] >>
      rename1 `MEM i (if src.bb_label = a.bb_label then _ else _).bb_instructions` >>
      qexists_tac `i` >> simp[] >>
      Cases_on `src.bb_label = a.bb_label`
      >- (gvs[]
          >- (qexists_tac `a` >> simp[] >>
              Cases_on `a.bb_instructions` >> fs[] >> drule MEM_FRONT >> simp[]) >>
          qexists_tac `b` >> simp[]) >>
      qexists_tac `src` >> gvs[]) >>
  rpt strip_tac >>
  `?v. MEM v i.inst_outputs` by
    (Cases_on `i.inst_outputs` >> gvs[] >> metis_tac[]) >>
  drule_all chain_merge_base_output_witness >> metis_tac[]
QED

val retpc_chain = ``\f a b. f with fn_blocks :=
  update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label f.fn_blocks)) (bb_succs (merge_blocks a b))``;

Theorem retpc_chain_seed_iff:
  wf_function f /\ fn_inst_wf f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_merge_blocks f a b ==>
  ((?i. MEM i (fn_insts (^retpc_chain f a b)) /\
        i.inst_opcode = RETPC_PARAM /\ MEM v i.inst_outputs) <=>
   (?i. MEM i (fn_insts f) /\ i.inst_opcode = RETPC_PARAM /\ MEM v i.inst_outputs))
Proof
  strip_tac >> BETA_TAC >> ho_match_mp_tac retpc_chain_exists >> simp[] >>
  rpt strip_tac >> Cases_on `i.inst_outputs` >> gvs[]
QED

Theorem retpc_chain_edge_iff:
  wf_function f /\ fn_inst_wf f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_merge_blocks f a b ==>
  ((?i. MEM i (fn_insts (^retpc_chain f a b)) /\ MEM v i.inst_outputs /\
        ((i.inst_opcode = ASSIGN /\ i.inst_operands = [Var w]) \/
         (i.inst_opcode = PHI /\ MEM (Var w) i.inst_operands))) <=>
   (?i. MEM i (fn_insts f) /\ MEM v i.inst_outputs /\
        ((i.inst_opcode = ASSIGN /\ i.inst_operands = [Var w]) \/
         (i.inst_opcode = PHI /\ MEM (Var w) i.inst_operands))))
Proof
  strip_tac >> BETA_TAC >> ho_match_mp_tac retpc_chain_exists >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `i.inst_outputs` >> gvs[]) >>
  simp[subst_label_inst_def, MEM_MAP, subst_label_op_var]
QED

Theorem retpc_chain_closure_iff:
  wf_function f /\ fn_inst_wf f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_merge_blocks f a b ==>
  (retpc_var (^retpc_chain f a b) x <=> retpc_var f x)
Proof
  strip_tac >> simp[retpc_var_def] >> eq_tac
  >- (strip_tac >> drule copy_phi_var_transport >> disch_then irule >>
      conj_tac
      >- metis_tac[retpc_chain_edge_iff] >>
      metis_tac[retpc_chain_seed_iff]) >>
  strip_tac >> drule copy_phi_var_transport >> disch_then irule >>
  conj_tac
  >- (rpt strip_tac >> drule_all retpc_chain_edge_iff >>
      disch_then (qspecl_then [`w`, `v`] mp_tac) >> simp[] >> metis_tac[]) >>
  metis_tac[retpc_chain_seed_iff]
QED

Theorem retpc_normalized_transport:
  reachable_fn f = f /\ reachable_fn g = g /\ retpc_shape_ok f /\
  fn_inst_ids_distinct g /\
  (!x. retpc_var g x <=> retpc_var f x) /\
  (!j. MEM j (fn_insts g) /\ MEM j.inst_opcode [RET; RETFMP; DRET] ==>
       ?i. MEM i (fn_insts f) /\ i.inst_opcode = j.inst_opcode /\
           i.inst_operands = j.inst_operands) /\
  (!j. MEM j (fn_insts g) /\ (j.inst_outputs <> [] \/ j.inst_opcode = PHI) ==>
       ?i. MEM i (fn_insts f) /\ j.inst_id = i.inst_id /\
           j.inst_outputs = i.inst_outputs /\ j.inst_opcode = i.inst_opcode /\
           (i.inst_opcode = ASSIGN ==> j.inst_operands = i.inst_operands) /\
           (i.inst_opcode = PHI ==>
              !v. MEM (Var v) j.inst_operands <=> MEM (Var v) i.inst_operands)) ==>
  retpc_shape_ok g
Proof
  strip_tac >>
  qpat_x_assum `!j. _ /\ (_ \/ _) ==> _` (mk_asm "data") >>
  qpat_x_assum `!j. _ /\ MEM _ _ ==> _` (mk_asm "returns") >>
  simp[retpc_shape_ok_def] >>
  conj_tac >- suspend "returns" >>
  conj_tac >- suspend "phis" >>
  conj_tac >- suspend "writers" >>
  suspend "unique"
QED

Resume retpc_normalized_transport[returns]:
  rpt strip_tac >> asm "returns" drule >> simp[] >> strip_tac >>
  fs[retpc_shape_ok_def] >> metis_tac[]
QED

Resume retpc_normalized_transport[phis]:
  rpt strip_tac >> asm "data" drule >> simp[] >> strip_tac >>
  fs[retpc_shape_ok_def] >> metis_tac[]
QED

Resume retpc_normalized_transport[writers]:
  rpt strip_tac >>
  `inst.inst_outputs <> []` by (Cases_on `inst.inst_outputs` >> gvs[]) >>
  asm "data" drule >> simp[] >> strip_tac >>
  fs[retpc_shape_ok_def] >> metis_tac[]
QED

Resume retpc_normalized_transport[unique]:
  rpt strip_tac >>
  `i.inst_outputs <> [] /\ j.inst_outputs <> []` by
    (Cases_on `i.inst_outputs` >> Cases_on `j.inst_outputs` >> gvs[]) >>
  asm "data" (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  asm "data" (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  `i.inst_id = j.inst_id` by
    (fs[retpc_shape_ok_def] >> metis_tac[]) >>
  metis_tac[fn_inst_ids_distinct_inj]
QED

Finalise retpc_normalized_transport

val retpc_normalized_structure = ``\e f.
  ^retpc_structural e f /\ wf_function f /\ all_reachable f /\
  (!bb i l. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI /\ MEM (Label l) i.inst_operands ==>
    MEM l (pred_labels f bb.bb_label))``;

Theorem retpc_chain_normalized_structure:
  ^retpc_normalized_structure e f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_merge_blocks f a b /\
  g = f with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label f.fn_blocks))
    (bb_succs (merge_blocks a b)) ==>
  ^retpc_normalized_structure e g /\ fn_inst_wf g /\ reachable_fn g = g
Proof
  BETA_TAC >> strip_tac >>
  `MEM a f.fn_blocks /\ MEM b f.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  drule_all (BETA_RULE chain_merge_collapse_shape) >> strip_tac >>
  `wf_function g` by (gvs[] >> irule chain_merge_wf >> simp[]) >>
  `all_reachable g` by
    (irule chain_merge_all_reachable >> metis_tac[]) >>
  `fn_inst_wf g` by
    (fs[fn_inst_wf_def, EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `reachable_fn g = g` by
    (irule retpc_normalized_reachable_identity >>
     fs[cfgWfTheory.all_reachable_def] >> metis_tac[]) >>
  fs[] >> metis_tac[]
QED

Theorem retpc_bypass_normalized_structure:
  ^retpc_normalized_structure e f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_bypass_jump f a b /\
  do_merge_jump f a b lm = SOME (g,lm') ==>
  ^retpc_normalized_structure e g /\ fn_inst_wf g /\ reachable_fn g = g
Proof
  BETA_TAC >> strip_tac >>
  drule_all (BETA_RULE do_merge_jump_collapse_shape) >> strip_tac >>
  `wf_function g` by (irule do_merge_jump_wf >> metis_tac[]) >>
  `all_reachable g` by
    (irule do_merge_jump_all_reachable >> metis_tac[]) >>
  `fn_inst_wf g` by
    (fs[fn_inst_wf_def, EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `reachable_fn g = g` by
    (irule retpc_normalized_reachable_identity >>
     fs[cfgWfTheory.all_reachable_def] >> metis_tac[]) >>
  fs[] >> metis_tac[]
QED

val retpc_phi_distinct = ``\f.
  !bb i. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
    ALL_DISTINCT (MAP FST (phi_pairs i.inst_operands))``;

Theorem retpc_chain_normalized:
  ^retpc_normalized_structure e f /\ ^retpc_phi_distinct f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_merge_blocks f a b /\
  g = f with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label f.fn_blocks))
    (bb_succs (merge_blocks a b)) ==>
  (^retpc_normalized_structure e g /\ fn_inst_wf g /\ reachable_fn g = g) /\
  fn_inst_ids_distinct g /\ ^retpc_phi_distinct g
Proof
  BETA_TAC >> strip_tac >>
  conj_tac >- suspend "structure" >>
  conj_tac >- suspend "ids" >>
  suspend "phis"
QED

Resume retpc_chain_normalized[structure]:
  irule (BETA_RULE retpc_chain_normalized_structure) >> metis_tac[]
QED

Resume retpc_chain_normalized[ids]:
  gvs[] >> irule chain_merge_ids >>
  metis_tac[lookup_block_member_label]
QED

Resume retpc_chain_normalized[phis]:
  rpt gen_tac >> strip_tac >>
  `MEM a f.fn_blocks /\ MEM b f.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  `bb.bb_label <> b.bb_label` by
    (`MEM bb.bb_label (fn_labels g)` by
       (simp[fn_labels_def, MEM_MAP] >> qexists_tac `bb` >> gvs[]) >>
     gvs[chain_merge_fn_labels, MEM_FILTER]) >>
  qpat_x_assum `g = _` SUBST_ALL_TAC >> fs[] >>
  drule_all chain_merge_phi_source_exact >> strip_tac >>
  rename1 `MEM src f.fn_blocks` >>
  `inst_wf inst /\ ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands))` by
    (fs[EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `phi_well_formed inst.inst_operands` by gvs[inst_wf_def] >>
  `~MEM a.bb_label (MAP FST (phi_pairs inst.inst_operands))` by
    (simp[GSYM phi_pair_label_mem] >> strip_tac >>
     `MEM a.bb_label (pred_labels f src.bb_label)` by metis_tac[] >>
     drule_all pred_labels_lookup_edge >>
     gvs[can_merge_blocks_def]) >>
  drule_all phi_subst_label_distinct >>
  disch_then (qspec_then `b.bb_label` assume_tac) >>
  Cases_on `MEM bb.bb_label (bb_succs (merge_blocks a b))` >> gvs[]
QED

Finalise retpc_chain_normalized

Theorem retpc_bypass_normalized:
  ^retpc_normalized_structure e f /\ ^retpc_phi_distinct f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_bypass_jump f a b /\
  do_merge_jump f a b lm = SOME (g,lm') ==>
  (^retpc_normalized_structure e g /\ fn_inst_wf g /\ reachable_fn g = g) /\
  fn_inst_ids_distinct g /\ ^retpc_phi_distinct g
Proof
  BETA_TAC >> strip_tac >>
  conj_tac >- suspend "structure" >>
  conj_tac >- suspend "ids" >>
  suspend "phis"
QED

Resume retpc_bypass_normalized[structure]:
  irule (BETA_RULE retpc_bypass_normalized_structure) >> metis_tac[]
QED

Resume retpc_bypass_normalized[ids]:
  irule do_merge_jump_ids >> metis_tac[]
QED

Resume retpc_bypass_normalized[phis]:
  rpt gen_tac >> strip_tac >>
  drule_all do_merge_jump_phi_source_exact >> strip_tac >>
  `inst_wf inst /\ ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands))` by
    (fs[EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `phi_well_formed inst.inst_operands` by gvs[inst_wf_def] >>
  Cases_on `bb'.bb_label = target` >> gvs[] >>
  irule update_phi_bypass_distinct >> simp[]
QED

Finalise retpc_bypass_normalized

Theorem retpc_chain_return_provenance:
  wf_function f /\ first_block_no_preds f /\ all_reachable g /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_merge_blocks f a b /\
  g = ^retpc_chain f a b ==>
  !j. MEM j (fn_insts g) /\ MEM j.inst_opcode [RET; RETFMP; DRET] ==>
    ?i. MEM i (fn_insts f) /\ i.inst_opcode = j.inst_opcode /\
        i.inst_operands = j.inst_operands
Proof
  BETA_TAC >> strip_tac >> rpt gen_tac >> strip_tac >>
  `MEM a f.fn_blocks /\ MEM b f.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  `?bb. MEM bb g.fn_blocks /\ MEM j bb.bb_instructions` by
    (gvs[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `fn_reachable g bb.bb_label` by
    (qpat_x_assum `all_reachable g` mp_tac >>
     pure_rewrite_tac[cfgWfTheory.all_reachable_def] >>
     disch_then drule >> simp[]) >>
  drule_all simplifyCfgReachusesTheory.chain_merge_reachable_inst_origin >> strip_tac >>
  `inst.inst_opcode <> PHI` by gvs[] >>
  qexists_tac `inst` >>
  gvs[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]
QED

Theorem retpc_chain_data_provenance:
  wf_function f /\ first_block_no_preds f /\ all_reachable g /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_merge_blocks f a b /\
  g = ^retpc_chain f a b ==>
  !j. MEM j (fn_insts g) /\ (j.inst_outputs <> [] \/ j.inst_opcode = PHI) ==>
    ?i. MEM i (fn_insts f) /\ j.inst_id = i.inst_id /\
        j.inst_outputs = i.inst_outputs /\ j.inst_opcode = i.inst_opcode /\
        (i.inst_opcode = ASSIGN ==> j.inst_operands = i.inst_operands) /\
        (i.inst_opcode = PHI ==>
           !v. MEM (Var v) j.inst_operands <=> MEM (Var v) i.inst_operands)
Proof
  BETA_TAC >> strip_tac >> rpt gen_tac >> strip_tac >>
  `MEM a f.fn_blocks /\ MEM b f.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  `?bb. MEM bb g.fn_blocks /\ MEM j bb.bb_instructions` by
    (gvs[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `fn_reachable g bb.bb_label` by
    (qpat_x_assum `all_reachable g` mp_tac >>
     pure_rewrite_tac[cfgWfTheory.all_reachable_def] >>
     disch_then drule >> simp[]) >>
  drule_all simplifyCfgReachusesTheory.chain_merge_reachable_inst_origin >> strip_tac >>
  qexists_tac `inst` >>
  `MEM inst (fn_insts f)` by
    (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  Cases_on `MEM bb.bb_label (bb_succs (merge_blocks a b)) /\ inst.inst_opcode = PHI` >>
  gvs[subst_label_inst_def, MEM_MAP, subst_label_op_var] >>
  metis_tac[subst_label_op_var]
QED

Theorem retpc_chain_shape:
  ^retpc_normalized_structure e f /\ retpc_shape_ok f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_merge_blocks f a b /\
  g = ^retpc_chain f a b ==>
  retpc_shape_ok g
Proof
  BETA_TAC >> strip_tac >>
  drule_all (BETA_RULE retpc_chain_normalized_structure) >> strip_tac >>
  `fn_inst_wf f` by
    (fs[fn_inst_wf_def, EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `reachable_fn f = f` by
    (irule retpc_normalized_reachable_identity >>
     fs[cfgWfTheory.all_reachable_def] >> metis_tac[]) >>
  `fn_inst_ids_distinct g` by
    (gvs[] >> irule chain_merge_ids >> metis_tac[lookup_block_member_label]) >>
  `!x. retpc_var g x <=> retpc_var f x` by
    (gvs[] >> irule (BETA_RULE retpc_chain_closure_iff) >> simp[]) >>
  drule_at (Pat `g = _`) (BETA_RULE retpc_chain_return_provenance) >>
  disch_then assume_tac >>
  drule_at (Pat `g = _`) (BETA_RULE retpc_chain_data_provenance) >>
  disch_then assume_tac >>
  qpat_x_assum `g = _` kall_tac >>
  irule retpc_normalized_transport >> simp[] >> qexists_tac `f` >>
  fs[] >> metis_tac[]
QED

val retpc_bypass_inst = ``\a b t bb i.
  if bb.bb_label = a.bb_label then
    (if t = a.bb_label then update_phi_bypass a.bb_label b.bb_label else I)
      (if ~is_terminator i.inst_opcode then i
       else canon_jnz_inst (subst_label_inst b.bb_label t i))
  else if bb.bb_label = t then update_phi_bypass a.bb_label b.bb_label i
  else i``;

Theorem retpc_bypass_exists:
  wf_function f /\ fn_inst_wf f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_bypass_jump f a b /\
  bb_succs b = [t] /\ do_merge_jump f a b lm = SOME (g,lm') /\
  (!i. P i ==> i.inst_outputs <> []) /\
  (!bb i. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions ==>
     (P (^retpc_bypass_inst a b t bb i) <=> P i)) ==>
  ((?i. MEM i (fn_insts g) /\ P i) <=>
   (?i. MEM i (fn_insts f) /\ P i))
Proof
  BETA_TAC >> strip_tac >>
  simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> eq_tac
  >- (rpt strip_tac >> drule_all do_merge_jump_block_map >> strip_tac >>
      gvs[] >> fs[MEM_MAP] >> metis_tac[]) >>
  rpt strip_tac >>
  `?v. MEM v i.inst_outputs` by
    (Cases_on `i.inst_outputs` >> gvs[] >> metis_tac[]) >>
  drule_all do_merge_jump_output_witness >> strip_tac >>
  drule_all do_merge_jump_block_map >> strip_tac >>
  rename1 `MEM src f.fn_blocks` >>
  `src = bb` by
    ( `lookup_block src.bb_label f.fn_blocks = SOME src /\
       lookup_block bb.bb_label f.fn_blocks = SOME bb` by
        (conj_tac >> irule venomExecPropsTheory.MEM_lookup_block >>
         fs[wf_function_def, fn_labels_def]) >>
      metis_tac[optionTheory.SOME_11]) >>
  gvs[] >> qexists_tac `^retpc_bypass_inst a b t bb i` >> BETA_TAC >>
  conj_tac >- (qexists_tac `bb'` >> simp[MEM_MAP] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem retpc_bypass_data_fields:
  wf_function f /\ fn_inst_wf f /\ ^retpc_phi_distinct f /\
  lookup_block t f.fn_blocks = SOME target /\
  phi_values_agree a.bb_label b.bb_label target.bb_instructions /\
  a.bb_label <> b.bb_label /\ MEM bb f.fn_blocks /\ MEM i bb.bb_instructions /\
  ~is_terminator i.inst_opcode ==>
  (^retpc_bypass_inst a b t bb i).inst_id = i.inst_id /\
  (^retpc_bypass_inst a b t bb i).inst_outputs = i.inst_outputs /\
  (^retpc_bypass_inst a b t bb i).inst_opcode = i.inst_opcode /\
  (i.inst_opcode <> PHI ==> ^retpc_bypass_inst a b t bb i = i) /\
  (i.inst_opcode = PHI ==> !v.
    MEM (Var v) (^retpc_bypass_inst a b t bb i).inst_operands <=>
    MEM (Var v) i.inst_operands)
Proof
  BETA_TAC >> strip_tac >>
  `(^retpc_bypass_inst a b t bb i) =
    if bb.bb_label = t then update_phi_bypass a.bb_label b.bb_label i else i` by
    (BETA_TAC >> Cases_on `bb.bb_label = a.bb_label` >>
     Cases_on `bb.bb_label = t` >> gvs[]) >>
  pop_assum SUBST1_TAC >>
  Cases_on `bb.bb_label = t` >- (
    `bb = target` by
      (`lookup_block bb.bb_label f.fn_blocks = SOME bb` by
         (irule venomExecPropsTheory.MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
       metis_tac[optionTheory.SOME_11]) >>
    simp[update_phi_bypass_shape, update_phi_bypass_non_phi] >>
    strip_tac >> gen_tac >>
    `inst_wf i` by
      (fs[fn_inst_wf_def, fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
    `phi_well_formed i.inst_operands` by gvs[inst_wf_def] >>
    irule retpc_bypass_var_iff >>
    fs[wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  Cases_on `bb.bb_label = a.bb_label` >> gvs[]
QED

Theorem retpc_bypass_output_fields:
  (^retpc_bypass_inst a b t bb i).inst_id = i.inst_id /\
  (^retpc_bypass_inst a b t bb i).inst_outputs = i.inst_outputs
Proof
  BETA_TAC >> Cases_on `bb.bb_label = a.bb_label` >>
  Cases_on `t = a.bb_label` >> Cases_on `bb.bb_label = t` >>
  Cases_on `is_terminator i.inst_opcode` >>
  simp[update_phi_bypass_shape, canon_jnz_inst_shape, subst_label_inst_shape]
QED

Theorem retpc_bypass_seed_iff:
  wf_function f /\ fn_inst_wf f /\ ^retpc_phi_distinct f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_bypass_jump f a b /\
  bb_succs b = [t] /\ lookup_block t f.fn_blocks = SOME target /\
  phi_values_agree a.bb_label b.bb_label target.bb_instructions /\
  do_merge_jump f a b lm = SOME (g,lm') ==>
  ((?i. MEM i (fn_insts g) /\ i.inst_opcode = RETPC_PARAM /\ MEM v i.inst_outputs) <=>
   (?i. MEM i (fn_insts f) /\ i.inst_opcode = RETPC_PARAM /\ MEM v i.inst_outputs))
Proof
  BETA_TAC >> strip_tac >>
  ho_match_mp_tac (BETA_RULE retpc_bypass_exists) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> Cases_on `i.inst_outputs` >> gvs[]) >>
  rpt strip_tac >>
  Cases_on `i.inst_outputs = []`
  >- simp[BETA_RULE retpc_bypass_output_fields] >>
  `inst_wf i` by
    (fs[fn_inst_wf_def, fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `~is_terminator i.inst_opcode` by metis_tac[venomExecProofsTheory.terminator_no_outputs] >>
  `a.bb_label <> b.bb_label` by metis_tac[can_bypass_jump_source_distinct] >>
  drule_all (BETA_RULE retpc_bypass_data_fields) >> strip_tac >> simp[]
QED

Theorem retpc_bypass_edge_iff:
  wf_function f /\ fn_inst_wf f /\ ^retpc_phi_distinct f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_bypass_jump f a b /\
  bb_succs b = [t] /\ lookup_block t f.fn_blocks = SOME target /\
  phi_values_agree a.bb_label b.bb_label target.bb_instructions /\
  do_merge_jump f a b lm = SOME (g,lm') ==>
  ((?i. MEM i (fn_insts g) /\ MEM v i.inst_outputs /\
        ((i.inst_opcode = ASSIGN /\ i.inst_operands = [Var w]) \/
         (i.inst_opcode = PHI /\ MEM (Var w) i.inst_operands))) <=>
   (?i. MEM i (fn_insts f) /\ MEM v i.inst_outputs /\
        ((i.inst_opcode = ASSIGN /\ i.inst_operands = [Var w]) \/
         (i.inst_opcode = PHI /\ MEM (Var w) i.inst_operands))))
Proof
  BETA_TAC >> strip_tac >>
  ho_match_mp_tac (BETA_RULE retpc_bypass_exists) >> simp[] >> conj_tac
  >- (rpt strip_tac >> Cases_on `i.inst_outputs` >> gvs[]) >>
  rpt strip_tac >> Cases_on `i.inst_outputs = []`
  >- simp[BETA_RULE retpc_bypass_output_fields] >>
  `inst_wf i` by
    (fs[fn_inst_wf_def, fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `~is_terminator i.inst_opcode` by metis_tac[venomExecProofsTheory.terminator_no_outputs] >>
  `a.bb_label <> b.bb_label` by metis_tac[can_bypass_jump_source_distinct] >>
  drule_all (BETA_RULE retpc_bypass_data_fields) >> strip_tac >>
  Cases_on `i.inst_opcode = PHI` >> gvs[]
QED

Theorem retpc_bypass_closure_iff:
  wf_function f /\ fn_inst_wf f /\ ^retpc_phi_distinct f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_bypass_jump f a b /\
  bb_succs b = [t] /\ lookup_block t f.fn_blocks = SOME target /\
  phi_values_agree a.bb_label b.bb_label target.bb_instructions /\
  do_merge_jump f a b lm = SOME (g,lm') ==>
  (retpc_var g x <=> retpc_var f x)
Proof
  BETA_TAC >> strip_tac >>
  drule_all (BETA_RULE retpc_bypass_seed_iff) >> disch_then (mk_asm "seeds") >>
  drule_all (BETA_RULE retpc_bypass_edge_iff) >> disch_then (mk_asm "edges") >>
  simp[retpc_var_def] >> eq_tac
  >- (strip_tac >> drule copy_phi_var_transport >> disch_then irule >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          asm_x "edges" (qspecl_then [`w`, `v`] (fn th => rewrite_tac[GSYM th])) >>
          qexists_tac `inst` >> simp[]) >>
      rpt gen_tac >> strip_tac >>
      asm_x "seeds" (qspec_then `v` (fn th => rewrite_tac[GSYM th])) >>
      qexists_tac `inst` >> simp[]) >>
  strip_tac >> drule copy_phi_var_transport >> disch_then irule >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      asm_x "edges" (qspecl_then [`w`, `v`] (fn th => rewrite_tac[th])) >>
      qexists_tac `inst` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  asm_x "seeds" (qspec_then `v` (fn th => rewrite_tac[th])) >>
  qexists_tac `inst` >> simp[]
QED

Theorem retpc_bypass_return_provenance:
  wf_function f /\ EVERY label_positions_ok (fn_insts f) /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  do_merge_jump f a b lm = SOME (g,lm') ==>
  !j. MEM j (fn_insts g) /\ MEM j.inst_opcode [RET; RETFMP; DRET] ==>
    ?i. MEM i (fn_insts f) /\ i.inst_opcode = j.inst_opcode /\
        i.inst_operands = j.inst_operands
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `?out. MEM out g.fn_blocks /\ MEM j out.bb_instructions` by
    (fs[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  drule_all do_merge_jump_block_map >> strip_tac >>
  qpat_x_assum `MEM j out.bb_instructions` mp_tac >> simp[MEM_MAP] >>
  disch_then (qx_choose_then `i` strip_assume_tac) >>
  `i.inst_opcode = j.inst_opcode` by
    (Cases_on `bb.bb_label = a.bb_label` >>
     Cases_on `target = a.bb_label` >> Cases_on `bb.bb_label = target` >>
     Cases_on `is_terminator i.inst_opcode` >>
     gvs[update_phi_bypass_shape] >>
     qmatch_asmsub_abbrev_tac `(canon_jnz_inst k).inst_opcode` >>
     qspec_then `k` mp_tac scfg_canon_opcode >>
     simp[Abbr `k`, subst_label_inst_shape]) >>
  `MEM i (fn_insts f)` by
    (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `EVERY (\op. ~is_label_operand op) i.inst_operands` by
    (`label_positions_ok i` by (fs[EVERY_MEM] >> metis_tac[]) >>
     qpat_x_assum `label_positions_ok i` mp_tac >>
     fs[] >> gvs[label_positions_ok_def]) >>
  `subst_label_inst b.bb_label target i = i` by
    simp[subst_label_inst_no_label_operands] >>
  `i.inst_opcode <> PHI /\ i.inst_opcode <> JNZ` by (fs[] >> metis_tac[]) >>
  `j = i` by
    (qpat_x_assum `j = _` mp_tac >>
     simp[scfg_canon_non_jnz, update_phi_bypass_non_phi] >>
     rpt IF_CASES_TAC >> simp[update_phi_bypass_non_phi]) >>
  qexists_tac `i` >> metis_tac[]
QED

Theorem retpc_bypass_data_provenance:
  wf_function f /\ fn_inst_wf f /\ ^retpc_phi_distinct f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_bypass_jump f a b /\
  bb_succs b = [t] /\ lookup_block t f.fn_blocks = SOME target /\
  phi_values_agree a.bb_label b.bb_label target.bb_instructions /\
  do_merge_jump f a b lm = SOME (g,lm') ==>
  !j. MEM j (fn_insts g) /\ (j.inst_outputs <> [] \/ j.inst_opcode = PHI) ==>
    ?i. MEM i (fn_insts f) /\ j.inst_id = i.inst_id /\
        j.inst_outputs = i.inst_outputs /\ j.inst_opcode = i.inst_opcode /\
        (i.inst_opcode = ASSIGN ==> j.inst_operands = i.inst_operands) /\
        (i.inst_opcode = PHI ==>
           !v. MEM (Var v) j.inst_operands <=> MEM (Var v) i.inst_operands)
Proof
  BETA_TAC >> strip_tac >> rpt gen_tac >> strip_tac >>
  `?out. MEM out g.fn_blocks /\ MEM j out.bb_instructions` by
    (fs[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  drule_all do_merge_jump_block_map >> strip_tac >>
  `target' = t` by gvs[] >> qpat_x_assum `target' = t` SUBST_ALL_TAC >>
  qpat_x_assum `MEM j out.bb_instructions` mp_tac >> simp[MEM_MAP] >>
  disch_then (qx_choose_then `i` strip_assume_tac) >>
  `inst_wf i /\ MEM i (fn_insts f)` by
    (fs[fn_inst_wf_def, fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `j.inst_outputs = i.inst_outputs /\ (j.inst_opcode = PHI <=> i.inst_opcode = PHI)` by
    (Cases_on `bb.bb_label = a.bb_label` >>
     Cases_on `t = a.bb_label` >> Cases_on `bb.bb_label = t` >>
     Cases_on `is_terminator i.inst_opcode` >>
     gvs[update_phi_bypass_shape, canon_jnz_inst_shape, subst_label_inst_shape]) >>
  `~is_terminator i.inst_opcode` by
    metis_tac[venomExecProofsTheory.terminator_no_outputs, is_terminator_def] >>
  `a.bb_label <> b.bb_label` by metis_tac[can_bypass_jump_source_distinct] >>
  drule_all (BETA_RULE retpc_bypass_data_fields) >> strip_tac >>
  qpat_x_assum `j = if _ then _ else _`
    (fn th => RULE_ASSUM_TAC (PURE_ONCE_REWRITE_RULE [GSYM th])) >>
  qexists_tac `i` >> Cases_on `i.inst_opcode = PHI` >> gvs[]
QED

Theorem retpc_bypass_shape:
  ^retpc_normalized_structure e f /\ ^retpc_phi_distinct f /\ retpc_shape_ok f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_bypass_jump f a b /\
  bb_succs b = [t] /\ lookup_block t f.fn_blocks = SOME target /\
  phi_values_agree a.bb_label b.bb_label target.bb_instructions /\
  do_merge_jump f a b lm = SOME (g,lm') ==>
  retpc_shape_ok g
Proof
  BETA_TAC >> strip_tac >>
  `fn_inst_wf f` by
    (fs[fn_inst_wf_def, EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `reachable_fn f = f` by
    (irule retpc_normalized_reachable_identity >>
     fs[cfgWfTheory.all_reachable_def] >> metis_tac[]) >>
  `!x. retpc_var g x <=> retpc_var f x` by
    (gen_tac >> irule (BETA_RULE retpc_bypass_closure_iff) >> metis_tac[]) >>
  drule_at (Pat `do_merge_jump _ _ _ _ = _`) retpc_bypass_return_provenance >>
  disch_then assume_tac >>
  drule_at (Pat `do_merge_jump _ _ _ _ = _`) (BETA_RULE retpc_bypass_data_provenance) >>
  disch_then assume_tac >>
  drule_all (BETA_RULE retpc_bypass_normalized) >> strip_tac >>
  irule retpc_normalized_transport >> simp[] >> qexists_tac `f` >>
  fs[] >> metis_tac[]
QED

val retpc_collapse_inv = ``\e f.
  ^retpc_normalized_structure e f /\ ^retpc_phi_distinct f /\ retpc_shape_ok f``;

Theorem retpc_checked_bypass_inv:
  ^retpc_collapse_inv e f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_bypass_jump f a b /\
  lookup_block (HD (bb_succs b)) f.fn_blocks = SOME target /\
  phi_values_agree a.bb_label b.bb_label target.bb_instructions /\
  do_merge_jump f a b lm = SOME (g,lm') ==>
  ^retpc_collapse_inv e g
Proof
  BETA_TAC >> strip_tac >>
  `bb_succs b = [HD (bb_succs b)]` by
    (fs[can_bypass_jump_def, num_succs_def] >>
     Cases_on `bb_succs b` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  drule_at (Pat `do_merge_jump _ _ _ _ = _`) (BETA_RULE retpc_bypass_shape) >>
  disch_then (qspecl_then [`target`, `HD (bb_succs b)`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all (BETA_RULE retpc_bypass_normalized) >> strip_tac >>
  fs[] >> metis_tac[]
QED

Theorem retpc_try_bypass_inv:
  !succs f lm a.
    ^retpc_collapse_inv e f /\ lookup_block a.bb_label f.fn_blocks = SOME a ==>
    ^retpc_collapse_inv e (FST (try_bypass f lm a succs))
Proof
  BETA_TAC >> Induct_on `succs` >- (simp[try_bypass_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> simp[try_bypass_def] >>
  Cases_on `lookup_block h f.fn_blocks` >> simp[]
  >- (first_x_assum irule >> simp[] >> metis_tac[]) >>
  rename1 `lookup_block h f.fn_blocks = SOME b` >>
  `lookup_block b.bb_label f.fn_blocks = SOME b` by
    metis_tac[lookup_block_member_label] >>
  Cases_on `can_bypass_jump f a b` >> simp[]
  >- (Cases_on `lookup_block (HD (bb_succs b)) f.fn_blocks` >> simp[]
      >- (first_x_assum irule >> simp[] >> metis_tac[]) >>
      rename1 `lookup_block (HD (bb_succs b)) f.fn_blocks = SOME target` >>
      Cases_on `phi_values_agree a.bb_label b.bb_label target.bb_instructions` >> simp[]
      >- (Cases_on `do_merge_jump f a b lm` >> simp[]
          >- (first_x_assum irule >> simp[] >> metis_tac[]) >>
          PairCases_on `x` >> simp[] >>
          qpat_x_assum `!f lm a. _ /\ lookup_block _ _ = _ ==> _` kall_tac >>
          drule_at (Pat `do_merge_jump _ _ _ _ = _`)
            (BETA_RULE retpc_checked_bypass_inv) >> simp[] >>
          impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
      first_x_assum irule >> simp[] >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem retpc_chain_inv:
  ^retpc_collapse_inv e f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_merge_blocks f a b /\
  g = ^retpc_chain f a b ==>
  ^retpc_collapse_inv e g
Proof
  BETA_TAC >> strip_tac >>
  drule_at (Pat `g = _`) (BETA_RULE retpc_chain_shape) >>
  disch_then (qspec_then `e` assume_tac) >>
  drule_at (Pat `g = _`) (BETA_RULE retpc_chain_normalized) >>
  disch_then (qspec_then `e` assume_tac) >>
  qpat_x_assum `g = _` kall_tac >> metis_tac[]
QED

Theorem retpc_collapse_inv_joint:
  (!f lm vis lbl. ^retpc_collapse_inv e f ==>
     ^retpc_collapse_inv e (FST (collapse_dfs f lm vis lbl))) /\
  (!f lm vis succs. ^retpc_collapse_inv e f ==>
     ^retpc_collapse_inv e (FST (collapse_dfs_succs f lm vis succs)))
Proof
  qabbrev_tac `Q = ^retpc_collapse_inv e` >>
  `!f lm a succs. Q f /\ lookup_block a.bb_label f.fn_blocks = SOME a ==>
     Q (FST (try_bypass f lm a succs))` by
    (simp[Abbr `Q`] >> metis_tac[BETA_RULE retpc_try_bypass_inv]) >>
  `!f lbl next a b. Q f /\ lookup_block lbl f.fn_blocks = SOME a /\
     lookup_block next f.fn_blocks = SOME b /\ can_merge_blocks f a b ==>
     Q (f with fn_blocks := update_succ_phi_labels next lbl
       (replace_block lbl (merge_blocks a b) (remove_block next f.fn_blocks))
       (bb_succs (merge_blocks a b)))` by
    (rpt strip_tac >>
     `a.bb_label = lbl /\ b.bb_label = next` by metis_tac[lookup_block_member_label] >>
     gvs[] >> qunabbrev_tac `Q` >> BETA_TAC >>
     qpat_x_assum `!f lm a succs. _` kall_tac >>
     irule (BETA_RULE retpc_chain_inv) >>
     qexistsl_tac [`a`, `b`, `f`] >>
     RULE_ASSUM_TAC BETA_RULE >> simp[] >> metis_tac[lookup_block_member_label]) >>
  ho_match_mp_tac collapse_dfs_ind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      simp[NoAsms, Once collapse_dfs_def] >>
      Cases_on `lookup_block lbl f.fn_blocks` >> simp[] >>
      rename1 `lookup_block lbl f.fn_blocks = SOME bb` >>
      Cases_on `bb_succs bb`
      >- (gvs[try_bypass_def] >> Cases_on `MEM lbl vis` >> simp[] >> metis_tac[]) >>
      rename1 `bb_succs bb = next::rest` >> Cases_on `rest`
      >- (simp[] >> Cases_on `lookup_block next f.fn_blocks` >> simp[]
          >- (Cases_on `MEM lbl vis` >> simp[]) >>
          rename1 `lookup_block next f.fn_blocks = SOME b` >>
          Cases_on `can_merge_blocks f bb b`
          >- (gvs[] >> first_x_assum irule >> simp[] >>
              first_x_assum irule >> simp[] >> metis_tac[]) >>
          Cases_on `MEM lbl vis` >> simp[] >> gvs[]) >>
      `lookup_block bb.bb_label f.fn_blocks = SOME bb` by
        metis_tac[lookup_block_member_label] >>
      `Q (FST (try_bypass f lm bb (next::h::t)))` by metis_tac[] >>
      Cases_on `try_bypass f lm bb (next::h::t)` >>
      PairCases_on `r` >> Cases_on `r1` >> gvs[] >>
      Cases_on `MEM lbl vis` >> simp[] >> gvs[]) >>
  conj_tac >- simp[NoAsms, Once collapse_dfs_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[NoAsms, Once collapse_dfs_def] >>
  Cases_on `collapse_dfs f lm vis lbl` >> PairCases_on `r` >> gvs[]
QED

Theorem retpc_remove_normalized_identity:
  ALL_DISTINCT (fn_labels f) /\ all_reachable f ==> remove_unreachable_blocks f = f
Proof
  strip_tac >> simp[remove_unreachable_blocks_def] >>
  Cases_on `fn_entry_label f` >> simp[] >>
  `FILTER (\bb. reachable f bb.bb_label) f.fn_blocks = f.fn_blocks` by
    (simp[FILTER_EQ_ID, EVERY_MEM] >>
     fs[cfgWfTheory.all_reachable_def] >> metis_tac[fn_reachable_iff_reachable]) >>
  simp[]
QED

Theorem retpc_fix_phi_distinct:
  inst_wf i /\ ALL_DISTINCT (MAP FST (phi_pairs i.inst_operands)) /\
  (fix_phi_inst ps i).inst_opcode = PHI ==>
  ALL_DISTINCT (MAP FST (phi_pairs (fix_phi_inst ps i).inst_operands))
Proof
  strip_tac >>
  `i.inst_opcode = PHI` by metis_tac[scfg_fix_phi_retained_opcode] >>
  `phi_well_formed i.inst_operands` by gvs[inst_wf_def] >>
  drule_all simplifyCfgPhiRepairTheory.fix_phi_inst_surviving_pairs >>
  disch_then SUBST1_TAC >>
  `MAP FST (FILTER (\p. MEM (FST p) ps) (phi_pairs i.inst_operands)) =
   FILTER (\l. MEM l ps) (MAP FST (phi_pairs i.inst_operands))` by
    simp[rich_listTheory.FILTER_MAP, combinTheory.o_DEF] >>
  simp[FILTER_ALL_DISTINCT]
QED

Theorem retpc_fix_all_phis_inv:
  ^retpc_collapse_inv e f ==> ^retpc_collapse_inv e (fix_all_phis f)
Proof
  BETA_TAC >> strip_tac >>
  `fn_inst_wf f` by
    (fs[fn_inst_wf_def, EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `remove_unreachable_blocks f = f` by metis_tac[retpc_remove_normalized_identity] >>
  `retpc_shape_ok (fix_all_phis f)` by metis_tac[retpc_initial_shape] >>
  drule_all (BETA_RULE fix_all_phis_structural_shape) >> strip_tac >>
  `wf_function (fix_all_phis f) /\ all_reachable (fix_all_phis f)` by
    metis_tac[fix_all_phis_wf, fix_all_phis_all_reachable] >>
  `!bb i l. MEM bb (fix_all_phis f).fn_blocks /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI /\ MEM (Label l) i.inst_operands ==>
    MEM l (pred_labels (fix_all_phis f) bb.bb_label)` by
    (rpt strip_tac >> irule simplifyCfgPhiShapeTheory.fix_all_phis_phi_preds >>
     metis_tac[]) >>
  simp[] >> conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `MEM i (fn_insts (fix_all_phis f))` by
    (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  drule scfg_fix_all_phis_inst_mem >> strip_tac >> gvs[] >>
  `inst.inst_opcode = PHI` by metis_tac[scfg_fix_phi_retained_opcode] >>
  irule retpc_fix_phi_distinct >>
  fs[fn_inst_wf_def, EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]
QED

Theorem retpc_collapse_empty_log:
  ^retpc_collapse_inv e f /\ collapse_dfs f [] vis lbl = (g,lm,vis') ==>
  ^retpc_collapse_inv e g /\ subst_block_labels_fn lm g = g
Proof
  strip_tac >>
  `^retpc_collapse_inv e g` by
    (mp_tac (CONJUNCT1 retpc_collapse_inv_joint) >>
     disch_then drule >>
     disch_then (qspecl_then [`[]`, `vis`, `lbl`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule (BETA_RULE collapse_dfs_empty_log_subst_identity) >>
  BETA_TAC >> metis_tac[]
QED

Theorem retpc_round_inv:
  ^retpc_collapse_inv e f ==> ^retpc_collapse_inv e (simplify_cfg_round f)
Proof
  strip_tac >>
  `remove_unreachable_blocks f = f` by
    (irule retpc_remove_normalized_identity >> fs[]) >>
  `^retpc_collapse_inv e (fix_all_phis f)` by metis_tac[retpc_fix_all_phis_inv] >>
  simp[simplify_cfg_round_def, simplify_cfg_round_with_labels_def] >>
  Cases_on `fn_entry_label f` >> simp[]
  >- (RULE_ASSUM_TAC BETA_RULE >> first_assum ACCEPT_TAC) >>
  Cases_on `collapse_dfs (fix_all_phis f) [] [] x` >> PairCases_on `r` >> simp[] >>
  drule_all retpc_collapse_empty_log >> strip_tac >> simp[] >>
  `remove_unreachable_blocks q = q` by
    (irule retpc_remove_normalized_identity >> fs[]) >>
  simp[] >> irule (BETA_RULE retpc_fix_all_phis_inv) >>
  RULE_ASSUM_TAC BETA_RULE >> fs[] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem retpc_iter_inv:
  !n f. ^retpc_collapse_inv e f ==>
    ^retpc_collapse_inv e (FST (simplify_cfg_iter_with_labels n f))
Proof
  qabbrev_tac `Q = ^retpc_collapse_inv e` >>
  `!f. Q f ==> Q (simplify_cfg_round f)` by
    (qunabbrev_tac `Q` >> metis_tac[retpc_round_inv]) >>
  Induct_on `n` >- simp[simplify_cfg_iter_with_labels_def] >>
  rpt gen_tac >> strip_tac >>
  `Q (simplify_cfg_round f)` by metis_tac[] >>
  Cases_on `simplify_cfg_round_with_labels f` >>
  fs[simplify_cfg_round_def] >>
  pure_once_rewrite_tac[simplify_cfg_iter_with_labels_def] >> simp[] >>
  Cases_on `q.fn_blocks = f.fn_blocks` >- simp[] >>
  first_x_assum drule >>
  Cases_on `simplify_cfg_iter_with_labels n q` >> simp[]
QED

Theorem retpc_initial_inv:
  wf_function f /\ fn_inst_wf f /\ fn_shape_ok f /\ first_block_no_preds f ==>
  ^retpc_collapse_inv (HD f.fn_blocks).bb_label
    (fix_all_phis (remove_unreachable_blocks f))
Proof
  strip_tac >>
  drule_all retpc_initial_structural >>
  disch_then (assume_tac o BETA_RULE) >>
  `wf_function (fix_all_phis (remove_unreachable_blocks f)) /\
   all_reachable (fix_all_phis (remove_unreachable_blocks f))` by
    metis_tac[fix_all_phis_wf, remove_unreachable_blocks_wf,
      fix_all_phis_all_reachable, remove_unreachable_blocks_reachable] >>
  `retpc_shape_ok (fix_all_phis (remove_unreachable_blocks f))` by
    (irule retpc_initial_shape >> fs[fn_shape_ok_def]) >>
  BETA_TAC >> simp[] >> conj_tac
  >- (rpt strip_tac >> irule simplifyCfgPhiShapeTheory.fix_all_phis_phi_preds >>
      `wf_function (remove_unreachable_blocks f)` by
        metis_tac[remove_unreachable_blocks_wf] >>
      `fn_inst_wf (remove_unreachable_blocks f)` by
        metis_tac[simplifyCfgDefsTheory.remove_unreachable_blocks_fn_inst_wf] >>
      fs[wf_function_def, fn_inst_wf_def, EVERY_MEM,
         fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  rpt strip_tac >> irule retpc_initial_phi_distinct >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `f` >> simp[] >>
  fs[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]
QED

Theorem retpc_initial_round_inv:
  wf_function f /\ fn_inst_wf f /\ fn_shape_ok f /\ first_block_no_preds f ==>
  ^retpc_collapse_inv (HD f.fn_blocks).bb_label (simplify_cfg_round f)
Proof
  strip_tac >> drule_all retpc_initial_inv >> strip_tac >>
  Cases_on `fn_entry_label f`
  >- (fs[fn_shape_ok_def, fn_has_entry_def]) >>
  simp[simplify_cfg_round_def, simplify_cfg_round_with_labels_def] >>
  Cases_on `collapse_dfs (fix_all_phis (remove_unreachable_blocks f)) [] [] x` >>
  PairCases_on `r` >> simp[] >>
  drule_all retpc_collapse_empty_log >> strip_tac >> simp[] >>
  `remove_unreachable_blocks q = q` by
    (irule retpc_remove_normalized_identity >> fs[]) >>
  simp[] >> irule (BETA_RULE retpc_fix_all_phis_inv) >>
  RULE_ASSUM_TAC BETA_RULE >> fs[] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem simplify_cfg_preserves_retpc_shape:
  wf_function f /\ fn_inst_wf f /\ fn_shape_ok f /\ first_block_no_preds f ==>
  retpc_shape_ok (simplify_cfg_fn f)
Proof
  strip_tac >>
  `retpc_shape_ok f` by fs[fn_shape_ok_def] >>
  drule_all retpc_initial_round_inv >>
  Cases_on `simplify_cfg_round_with_labels f` >>
  simp[simplify_cfg_round_def] >> strip_tac >>
  simp[simplify_cfg_fn_def, simplify_cfg_fn_with_labels_def] >>
  Cases_on `LENGTH f.fn_blocks` >- simp[simplify_cfg_iter_with_labels_def] >>
  pure_once_rewrite_tac[simplify_cfg_iter_with_labels_def] >> simp[] >>
  Cases_on `q.fn_blocks = f.fn_blocks` >- simp[] >>
  `^retpc_collapse_inv (HD f.fn_blocks).bb_label
     (FST (simplify_cfg_iter_with_labels n q))` by
    (BETA_TAC >> irule (BETA_RULE retpc_iter_inv) >> simp[] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `simplify_cfg_iter_with_labels n q` >> fs[]
QED
