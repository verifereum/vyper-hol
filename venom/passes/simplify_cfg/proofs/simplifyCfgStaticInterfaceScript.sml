(* Proof-only packages for repeated SimplifyCFG transformations. *)
Theory simplifyCfgStaticInterface
Ancestors
  simplifyCfgShapeCore
  simplifyCfgCleanup simplifyCfgRestriction simplifyCfgFixupClosure
  simplifyCfgFixupShape simplifyCfgFixupStatic
  simplifyCfgDefs simplifyCfgLabelProps venomWf unitShapeDefs cfgTransform list
  simplifyCfgStruct

Definition scfg_static_def:
  scfg_static fn <=>
    wf_function fn /\ fn_inst_wf fn /\ scfg_shape fn /\
    first_block_no_preds fn /\ simplify_cfg_fn_ok fn
End

Definition scfg_normalized_def:
  scfg_normalized fn <=> scfg_static fn /\
    (!bb. MEM bb fn.fn_blocks ==> fn_reachable fn bb.bb_label) /\
    (!bb i l. MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\
      i.inst_opcode = PHI /\ MEM (Label l) i.inst_operands ==>
      MEM l (pred_labels fn bb.bb_label))
End

Theorem scfg_static_cleanup:
  scfg_static fn ==> scfg_static (fix_all_phis (remove_unreachable_blocks fn))
Proof
  simp[scfg_static_def] >> rpt strip_tac >>
  metis_tac[scfg_restriction_fix_phis_wf, scfg_restriction_fix_phis_inst_wf,
    scfg_restriction_fix_phis_shape, scfg_restriction_fix_phis_ok,
    remove_unreachable_blocks_first_block_no_preds, fix_all_phis_first_block_no_preds,
    remove_unreachable_blocks_wf]
QED

Theorem scfg_filter_phi_support:
  !ops. !ps l. phi_well_formed ops /\ MEM (Label l) (filter_phi_ops ps ops) ==>
    MEM l ps
Proof
  recInduct phi_well_formed_ind >>
  rw[phi_well_formed_def, filter_phi_ops_def] >>
  Cases_on `MEM lbl ps` >> gvs[] >> metis_tac[]
QED

Theorem scfg_fix_phi_support:
  inst_wf i /\ (fix_phi_inst ps i).inst_opcode = PHI /\
  MEM (Label l) (fix_phi_inst ps i).inst_operands ==> MEM l ps
Proof
  strip_tac >> Cases_on `i.inst_opcode = PHI`
  >- (fs[fix_phi_inst_def] >>
      namedCases_on `filter_phi_ops ps i.inst_operands` ["", "o1 r1"] >> gvs[] >>
      namedCases_on `r1` ["", "o2 r2"] >> gvs[]
      >- (irule scfg_filter_phi_support >> qexists_tac `i.inst_operands` >>
          fs[inst_wf_def]) >>
      Cases_on `r2` >> gvs[] >>
      irule scfg_filter_phi_support >> qexists_tac `i.inst_operands` >>
      fs[inst_wf_def]) >>
  fs[fix_phi_inst_def]
QED

Theorem scfg_fix_block_support:
  EVERY inst_wf bb.bb_instructions /\
  MEM i (fix_phis_in_block ps bb).bb_instructions /\ i.inst_opcode = PHI /\
  MEM (Label l) i.inst_operands ==> MEM l ps
Proof
  simp[fix_phis_in_block_def, MEM_FILTER, MEM_MAP, EVERY_MEM] >>
  rpt strip_tac >> gvs[] >> metis_tac[scfg_fix_phi_support]
QED

Theorem scfg_fix_all_phis_support:
  wf_function fn /\ fn_inst_wf fn /\ MEM bb (fix_all_phis fn).fn_blocks /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\ MEM (Label l) i.inst_operands ==>
  MEM l (pred_labels (fix_all_phis fn) bb.bb_label)
Proof
  simp[scfg_fix_all_phis_mem] >> rpt strip_tac >>
  rename1 `bb = fix_phis_in_block _ ob` >> gvs[] >>
  simp[bb_label_fix_phis_in_block, scfg_fix_all_phis_preds] >>
  irule scfg_fix_block_support >>
  qexistsl_tac [`ob`, `i`] >> simp[] >>
  fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]
QED

Theorem scfg_normalized_static:
  scfg_normalized fn ==> scfg_static fn
Proof
  simp[scfg_normalized_def]
QED

Theorem scfg_static_cleanup_entry:
  scfg_static fn ==>
  fn_entry_label (fix_all_phis (remove_unreachable_blocks fn)) = fn_entry_label fn
Proof
  simp[fix_all_phis_entry, remove_unreachable_blocks_entry]
QED

Theorem scfg_normalized_cleanup:
  scfg_static fn ==> scfg_normalized (fix_all_phis (remove_unreachable_blocks fn))
Proof
  strip_tac >> rewrite_tac[scfg_normalized_def] >>
  conj_tac >- metis_tac[scfg_static_cleanup] >> conj_tac
  >- (simp[scfg_fix_all_phis_mem] >> rpt strip_tac >> gvs[] >>
      `wf_function (remove_unreachable_blocks fn)` by
        metis_tac[scfg_static_def, remove_unreachable_blocks_wf] >>
      `fn_cfg_edge (fix_all_phis (remove_unreachable_blocks fn)) =
       fn_cfg_edge (remove_unreachable_blocks fn)` by
        simp[FUN_EQ_THM, scfg_fix_all_phis_edge] >>
      simp[bb_label_fix_phis_in_block, fn_reachable_def,
        fix_all_phis_entry] >>
      rewrite_tac[GSYM fn_reachable_def] >>
      irule scfg_restriction_blocks_reachable >>
      Cases_on `fn.fn_blocks` >>
      fs[scfg_static_def, wf_function_def, fn_has_entry_def,
        venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def] >> metis_tac[]) >>
  rpt strip_tac >> irule scfg_fix_all_phis_support >>
  fs[scfg_static_def] >> metis_tac[remove_unreachable_blocks_wf, simplifyCfgDefsTheory.remove_unreachable_blocks_fn_inst_wf]
QED

Theorem scfg_static_wf:
  scfg_static fn ==> wf_function fn
Proof
  simp[scfg_static_def]
QED

Theorem scfg_static_inst_wf:
  scfg_static fn ==> fn_inst_wf fn
Proof
  simp[scfg_static_def]
QED

Theorem scfg_static_shape:
  scfg_static fn ==> scfg_shape fn
Proof
  simp[scfg_static_def]
QED

Theorem scfg_static_first_no_preds:
  scfg_static fn ==> first_block_no_preds fn
Proof
  simp[scfg_static_def]
QED

Theorem scfg_static_ok:
  scfg_static fn ==> simplify_cfg_fn_ok fn
Proof
  simp[scfg_static_def]
QED

Theorem scfg_normalized_reachable:
  scfg_normalized fn /\ MEM bb fn.fn_blocks ==> fn_reachable fn bb.bb_label
Proof
  simp[scfg_normalized_def]
QED

Theorem scfg_normalized_phi_support:
  scfg_normalized fn /\ MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\
  i.inst_opcode = PHI /\ MEM (Label l) i.inst_operands ==>
  MEM l (pred_labels fn bb.bb_label)
Proof
  simp[scfg_normalized_def] >> metis_tac[]
QED
