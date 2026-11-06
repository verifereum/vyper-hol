(*
 * SimplifyCFG against the O1 pass contract: the step part.
 *
 * The dispatched transform is simplify_cfg_fn_with_labels, which keeps the
 * supply and makes no new labels or instruction ids: it deletes blocks,
 * merges a block into its single predecessor, bypasses jump-only blocks,
 * and rewrites PHIs and jumps in place.  So one run keeps the O1 function
 * shape, its names are fresh trivially, and its label map sends only
 * merged or bypassed blocks, never the entry (which has no predecessors),
 * to labels that remain.
 *)
Theory o1ContractSimplifyCfgStep
Ancestors
  o1PassContract simplifyCfgCorrectness simplifyCfgCallChecks simplifyCfgLabelProps
  simplifyCfgDefs simplifyCfgInvariant simplifyCfgCollapseShape simplifyCfgRetpc
  simplifyCfgOpaque unitShapeDefs cfgTransform venomPassDispatcher venomWf
  venomInst list

Theorem simplify_cfg_entry_no_return:
  entry_fn_no_return f ==>
  entry_fn_no_return (FST (simplify_cfg_fn_with_labels f))
Proof
  rewrite_tac[entry_fn_no_return_def] >> strip_tac >>
  ho_match_mp_tac simplify_cfg_fn_with_labels_opcodes >> simp[]
QED

Theorem simplify_cfg_entry_no_params:
  entry_fn_no_params f ==>
  entry_fn_no_params (FST (simplify_cfg_fn_with_labels f))
Proof
  rewrite_tac[entry_fn_no_params_def] >> strip_tac >>
  ho_match_mp_tac simplify_cfg_fn_with_labels_opcodes >> simp[venomInstTheory.is_param_opcode_def]
QED

Theorem fix_phi_inst_read0[local]:
  (is_read0_opcode i.inst_opcode ==> i.inst_operands = []) ==>
  (is_read0_opcode (fix_phi_inst ps i).inst_opcode ==>
    (fix_phi_inst ps i).inst_operands = [])
Proof
  Cases_on `i.inst_opcode = PHI`
  >- (simp[fix_phi_inst_def] >>
      Cases_on `filter_phi_ops ps i.inst_operands` >>
      simp[is_read0_opcode_def] >>
      rename1 `h::t` >> Cases_on `t` >> simp[is_read0_opcode_def] >>
      rename1 `h::k::rest` >> Cases_on `rest` >> simp[is_read0_opcode_def]) >>
  simp[fix_phi_inst_def]
QED

Theorem canon_jnz_inst_read0[local]:
  (is_read0_opcode i.inst_opcode ==> i.inst_operands = []) ==>
  (is_read0_opcode (canon_jnz_inst i).inst_opcode ==>
    (canon_jnz_inst i).inst_operands = [])
Proof
  Cases_on `canon_jnz_inst i = i` >- simp[] >>
  drule simplifyCfgShapeTheory.canon_jnz_inst_changed >> strip_tac >>
  simp[is_read0_opcode_def]
QED

Theorem simplify_cfg_read0_operands:
  EVERY (\i. is_read0_opcode i.inst_opcode ==> i.inst_operands = []) (fn_insts f) ==>
  EVERY (\i. is_read0_opcode i.inst_opcode ==> i.inst_operands = [])
    (fn_insts (FST (simplify_cfg_fn_with_labels f)))
Proof
  strip_tac >> irule simplify_cfg_fn_with_labels_every >> BETA_TAC >>
  rpt conj_tac
  >- metis_tac[canon_jnz_inst_read0]
  >- (simp[subst_label_inst_def] >> rpt strip_tac >> simp[])
  >- (rpt gen_tac >>
      simp[simplifyCfgShapeTheory.update_phi_bypass_opcode] >>
      Cases_on `i.inst_opcode = PHI`
      >- simp[is_read0_opcode_def] >>
      simp[update_phi_bypass_def])
  >- metis_tac[fix_phi_inst_read0]
  >- (rpt gen_tac >> Cases_on `is_block_label_opcode i.inst_opcode` >>
      simp[subst_block_labels_inst_def, subst_label_map_inst_def] >>
      rpt strip_tac >> simp[]) >> simp[]
QED

Theorem simplify_cfg_structural_shape:
  o1_fn_shape ctx f ==>
  EVERY inst_wf (fn_insts (FST (simplify_cfg_fn_with_labels f))) /\
  EVERY label_positions_ok (fn_insts (FST (simplify_cfg_fn_with_labels f))) /\
  first_block_no_preds (FST (simplify_cfg_fn_with_labels f)) /\
  first_block_no_phi (FST (simplify_cfg_fn_with_labels f)) /\
  fn_label_refs_ok (FST (simplify_cfg_fn_with_labels f)) /\
  (FST (simplify_cfg_fn_with_labels f)).fn_blocks <> [] /\
  (HD (FST (simplify_cfg_fn_with_labels f)).fn_blocks).bb_label =
    (HD f.fn_blocks).bb_label
Proof
  strip_tac >>
  mp_tac (Q.INST [`e` |-> `(HD f.fn_blocks).bb_label`]
    (BETA_RULE simplify_cfg_fn_structural_shape)) >>
  (impl_tac
   >- (gvs[o1_fn_shape_def, wf_function_def, fn_has_entry_def,
         fn_inst_wf_def, fn_shape_ok_def, inst_shape_ok_def,
         first_block_no_phi_def, EVERY_MEM, fn_insts_def,
         fn_insts_blocks_MEM] >> metis_tac[])) >>
  simp[first_block_no_phi_def]
QED

Theorem simplify_cfg_inst_shape:
  o1_fn_shape ctx f ==>
  EVERY inst_shape_ok (fn_insts (FST (simplify_cfg_fn_with_labels f)))
Proof
  strip_tac >>
  `EVERY (\i. ~MEM i.inst_opcode [DJMP; OFFSET])
    (fn_insts (FST (simplify_cfg_fn_with_labels f)))` by
    (ho_match_mp_tac simplify_cfg_fn_with_labels_opcodes >>
     gvs[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def]) >>
  `EVERY (\i. is_read0_opcode i.inst_opcode ==> i.inst_operands = [])
    (fn_insts (FST (simplify_cfg_fn_with_labels f)))` by
    (irule simplify_cfg_read0_operands >>
     gvs[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def]) >>
  drule simplify_cfg_structural_shape >> strip_tac >>
  `wf_function f /\ fn_inst_wf f` by gvs[o1_fn_shape_def] >>
  mp_tac (Q.INST [`fn` |-> `f`] simplify_cfg_phi_two_pairs) >>
  simp[simplify_cfg_fn_def] >> strip_tac >>
  mp_tac (Q.INST [`fn` |-> `f`] simplify_cfg_phi_labels_distinct) >>
  impl_tac >- gvs[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def] >>
  simp[simplify_cfg_fn_def] >> strip_tac >>
  gvs[EVERY_MEM, inst_shape_ok_def] >> metis_tac[]
QED

(* SimplifyCFG keeps the return-PC shape: RET's return PC, and every
   copy of it, still flows from RETPC_PARAM through ASSIGNs and PHIs.
   Admitted for now. *)
Theorem simplify_cfg_retpc_shape_ok:
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\ first_block_no_preds fn ==>
  retpc_shape_ok (simplify_cfg_fn fn)
Proof
  MATCH_ACCEPT_TAC simplify_cfg_preserves_retpc_shape
QED

Theorem simplify_cfg_fn_shape:
  o1_fn_shape ctx f ==> fn_shape_ok (FST (simplify_cfg_fn_with_labels f))
Proof
  strip_tac >> drule simplify_cfg_structural_shape >> strip_tac >>
  drule simplify_cfg_inst_shape >> strip_tac >>
  `opaque_use_ok f` by gvs[o1_fn_shape_def, fn_shape_ok_def] >>
  drule simplify_cfg_opaque_use_ok >> strip_tac >>
  `ALL_DISTINCT (fn_labels f)` by gvs[o1_fn_shape_def, wf_function_def] >>
  drule simplify_cfg_fn_with_labels_transition >> strip_tac >>
  `fn_identity_metadata_eq (FST (simplify_cfg_fn_with_labels f)) f` by
    (irule (cj 1 simplify_cfg_fn_with_labels_metadata) >>
     qexists_tac `SND (simplify_cfg_fn_with_labels f)` >> simp[]) >>
  gvs[fn_shape_ok_def] >> conj_tac
  >- (gvs[o1_fn_shape_def, fn_shape_ok_def, fn_entry_label_def,
          entry_block_def, fn_identity_metadata_eq_def, NULL_EQ] >>
      Cases_on `f.fn_blocks` >> gvs[]) >>
  `EVERY (\bb. ~reserved_label bb.bb_label) f.fn_blocks` by
    gvs[o1_fn_shape_def, fn_shape_ok_def] >>
  `call_checks_ok (FST (simplify_cfg_fn_with_labels f))` by
    (rewrite_tac[GSYM simplify_cfg_fn_def] >>
     irule simplify_cfg_call_checks_ok >> gvs[o1_fn_shape_def]) >>
  `retpc_shape_ok (FST (simplify_cfg_fn_with_labels f))` by
    (rewrite_tac[GSYM simplify_cfg_fn_def] >>
     irule simplify_cfg_retpc_shape_ok >> gvs[o1_fn_shape_def]) >>
  gvs[label_map_transition_def, EVERY_MEM, fn_labels_def, MEM_MAP] >>
  metis_tac[]
QED

Theorem simplify_cfg_o1_fn_shape:
  o1_fn_shape ctx f ==> o1_fn_shape ctx (FST (simplify_cfg_fn_with_labels f))
Proof
  strip_tac >>
  drule simplify_cfg_structural_shape >> strip_tac >>
  drule simplify_cfg_fn_shape >> strip_tac >>
  `wf_function (FST (simplify_cfg_fn_with_labels f))` by
    (rewrite_tac[GSYM simplify_cfg_fn_def] >>
     irule simplify_cfg_preserves_wf_function >> gvs[o1_fn_shape_def]) >>
  `fn_identity_metadata_eq (FST (simplify_cfg_fn_with_labels f)) f` by
    (irule (cj 1 simplify_cfg_fn_with_labels_metadata) >>
     qexists_tac `SND (simplify_cfg_fn_with_labels f)` >> simp[]) >>
  `fn_inst_wf (FST (simplify_cfg_fn_with_labels f))` by
    (gvs[fn_inst_wf_def, EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> DRET)
     (fn_insts (FST (simplify_cfg_fn_with_labels f)))` by
    (ho_match_mp_tac simplify_cfg_fn_with_labels_opcodes >>
     gvs[o1_fn_shape_def, dretDesugarDefsTheory.no_dret_def, EVERY_MEM]) >>
  `no_dret (FST (simplify_cfg_fn_with_labels f))` by
    gvs[dretDesugarDefsTheory.no_dret_def, EVERY_MEM] >>
  simp[o1_fn_shape_def] >> rpt conj_tac
  >- (rewrite_tac[fn_invoke_ok_def] >> rpt strip_tac >>
      `inst_wf inst` by gvs[EVERY_MEM] >>
      `?lbl rest. inst.inst_operands = Label lbl :: rest` by
        gvs[inst_wf_def] >>
      qexistsl_tac [`lbl`, `rest`] >> simp[] >>
      `MEM lbl (simplify_cfg_fn_invoke_labels
          (FST (simplify_cfg_fn_with_labels f)))` by
        (gvs[simplify_cfg_fn_invoke_labels_mem, fn_insts_def,
             fn_insts_blocks_MEM] >> metis_tac[]) >>
      drule simplify_cfg_fn_with_labels_no_new_call_edges >>
      simp[simplify_cfg_fn_invoke_labels_mem] >> strip_tac >>
      gvs[o1_fn_shape_def, fn_invoke_ok_def, fn_insts_def,
          fn_insts_blocks_MEM] >>
      qpat_x_assum `!i. (?bb. MEM bb f.fn_blocks /\ _) /\ _ ==> _`
        (qspec_then `inst'` mp_tac) >> simp[] >>
      (impl_tac >- metis_tac[]) >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      `?old. MEM old (fn_insts f) /\ old.inst_opcode = DALLOCA /\
             MEM x old.inst_outputs` by
        (mp_tac (Q.INST [`origin` |-> `DALLOCA`] simplify_cfg_seed_source) >>
         simp[] >> disch_then irule >> metis_tac[]) >>
      `~gas_var f x /\ ~retpc_var f x` by
        (gvs[o1_fn_shape_def] >> metis_tac[]) >>
      metis_tac[simplify_cfg_gas_var, simplify_cfg_retpc_var])
  >- (gvs[fn_identity_metadata_eq_def] >> strip_tac >>
      conj_tac
      >- (irule simplify_cfg_entry_no_return >> gvs[o1_fn_shape_def]) >>
      irule simplify_cfg_entry_no_params >> gvs[o1_fn_shape_def]) >>
  gvs[fn_identity_metadata_eq_def] >> strip_tac >>
  ho_match_mp_tac simplify_cfg_fn_with_labels_opcodes >> gvs[o1_fn_shape_def]
QED

Theorem simplify_cfg_step_contract:
  o1_step_contract rpolicy (CFP_Simple VP_SimplifyCFG)
Proof
  rewrite_tac[o1_step_contract_def] >> rpt gen_tac >> strip_tac >>
  `MEM fn observed.cu_context.ctx_functions` by
    (gvs[fn_pass_step_def] >>
     metis_tac[venomFnScheduleRunnerPropsTheory.lookup_unique_function_member]) >>
  `o1_fn_shape observed.cu_context fn` by
    gvs[o1_ctx_shape_def, EVERY_MEM] >>
  qpat_x_assum `fn_pass_step _ _ _ _ _ _` mp_tac >>
  simp[fn_pass_step_def, pairTheory.FORALL_PROD] >>
  Cases_on `simplify_cfg_fn_with_labels fn` >> simp[] >> strip_tac >>
  gvs[] >>
  drule simplify_cfg_o1_fn_shape >> simp[] >> strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[o1_fn_shape_def, wf_function_def] >>
  drule simplify_cfg_fn_with_labels_transition >> simp[] >> strip_tac >>
  conj_tac
  >- (simp[fresh_names_ok_def] >> conj_tac
      >- (gvs[label_map_transition_def, EVERY_MEM] >> metis_tac[]) >>
      rpt strip_tac >> disj1_tac >>
      mp_tac (Q.INST [`f` |-> `fn`] simplify_cfg_fn_with_labels_ids) >>
      gvs[irSupplyTheory.fn_ir_inst_ids_def, MEM_FLAT, MEM_MAP,
          irSupplyTheory.block_ir_inst_ids_def, fn_insts_def,
          fn_insts_blocks_MEM] >>
      (impl_tac >- metis_tac[]) >> strip_tac >>
      qexists_tac `MAP (\i. i.inst_id) bb.bb_instructions` >>
      simp[MEM_MAP] >> metis_tac[]) >>
  `MEM fn.fn_name (fn_labels q)` by
    (gvs[o1_fn_shape_def, fn_shape_ok_def, fn_entry_label_def,
         entry_block_def, fn_labels_def, NULL_EQ] >>
     Cases_on `q.fn_blocks` >> gvs[]) >>
  gvs[label_map_sources_ok_def, label_map_transition_def, EVERY_MEM] >>
  metis_tac[]
QED
