Theory acRuntimePhiProofs
Ancestors
  acRuntimeInvariantDefs acChainProofs venomWf venomWfProps venomExecProofs
  venomExecProps venomExecSemantics venomState venomInst dfgDefs
  dfgAnalysisProps list finite_map

(* Batch PHIs cannot overwrite an output of a strict dominator. *)
Theorem ac_phi_entry_output_frame[local]:
  wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  ac_def_before fn bb 0 inst /\ MEM v inst.inst_outputs /\
  eval_phis s bb.bb_instructions = OK t ==>
  lookup_var v t = lookup_var v s
Proof
  rpt strip_tac >> irule eval_phis_lookup_frame >>
  qexists `bb.bb_instructions` >> simp[] >> rpt strip_tac >>
  `MEM i bb.bb_instructions` by metis_tac[phi_prefix_mem] >>
  gvs[ac_def_before_def] >>
  `ssa_form fn` by gvs[wf_ssa_def] >>
  `db = bb` by metis_tac[ssa_unique_output_block] >> gvs[]
QED

(* Inputs supporting an entry equation also have strict-dominator definitions. *)
Theorem ac_phi_entry_operand_frame[local]:
  wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  ac_def_before fn bb 0 inst /\ inst.inst_opcode <> PHI /\
  MEM op inst.inst_operands /\ eval_phis s bb.bb_instructions = OK t ==>
  eval_operand op t = eval_operand op s
Proof
  rpt strip_tac >> Cases_on `op` >> simp[eval_operand_def]
  >- (rename1 `MEM (Var v) inst.inst_operands` >>
      `?db j. MEM db fn.fn_blocks /\ j < LENGTH db.bb_instructions /\
              EL j db.bb_instructions = inst` by
        (gvs[ac_def_before_def, MEM_EL] >> metis_tac[]) >>
      `def_available_at fn db (SOME (EL j db.bb_instructions)) v` by
        (fs[wf_ssa_def, def_dominates_uses_def] >>
         first_x_assum drule >>
         disch_then (qspec_then `EL j db.bb_instructions` mp_tac) >>
         simp[EL_MEM]) >>
      drule_all ac_available_before_cursor >> strip_tac >>
      `ac_def_before fn bb 0 inst'` by
        (irule ac_def_before_trans >> metis_tac[]) >>
      irule ac_phi_entry_output_frame >> metis_tac[]) >>
  drule eval_phis_preserves_labels >> simp[]
QED

Theorem ac_cursor_inv_phis:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  ac_cursor_inv fn bb 0 s /\ eval_phis s bb.bb_instructions = OK t ==>
  ac_cursor_inv fn bb (phi_prefix_length bb.bb_instructions)
    (t with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  rpt strip_tac >>
  `MEM bb fn.fn_blocks` by gvs[ac_cursor_inv_def] >>
  `t.vs_current_bb = s.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `EVERY (\i. i.inst_opcode = PHI)
      (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` by
    (simp[EVERY_MEM] >> metis_tac[phi_prefix_mem]) >>
  `!inst. inst.inst_opcode <> PHI ==>
      (ac_def_before fn bb (phi_prefix_length bb.bb_instructions) inst <=>
       ac_def_before fn bb 0 inst)` by
    metis_tac[ac_def_before_phi_prefix] >>
  gvs[ac_cursor_inv_def] >>
  simp[ac_cursor_inv_def, phi_prefix_length_le] >> conj_tac
  >- (simp[ac_dfg_inv_local_def] >> conj_tac >> rpt strip_tac >>
      `ac_def_before fn bb 0 inst` by gvs[] >>
      `MEM v inst.inst_outputs` by metis_tac[dfg_build_function_correct] >>
      `lookup_var v t = lookup_var v s` by
        (irule ac_phi_entry_output_frame >> metis_tac[]) >>
      rename1 `inst.inst_operands = [op]` >>
      `eval_operand op t = eval_operand op s` by
        (irule ac_phi_entry_operand_frame >>
         qexistsl [`bb`, `fn`, `inst`] >> simp[]) >>
      `!a. eval_operand a (t with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
           eval_operand a t` by
        (Cases >> simp[eval_operand_def, lookup_var_def]) >>
      fs[ac_dfg_inv_local_def, lookup_var_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `v IN FDOM t.vs_vars` suffices_by
    simp[lookup_var_def, FLOOKUP_DEF] >>
  qpat_x_assum `ac_def_before _ _ _ _` mp_tac >>
  simp[ac_def_before_def] >> strip_tac
  >- (irule eval_phis_outputs_in_fdom_idx >> metis_tac[]) >>
  `ac_def_before fn bb 0 inst` by
    (simp[ac_def_before_def] >> metis_tac[]) >>
  `v IN FDOM s.vs_vars` by
    (`IS_SOME (lookup_var v s)` by metis_tac[] >>
     Cases_on `v IN FDOM s.vs_vars` >>
     gvs[lookup_var_def, FLOOKUP_DEF]) >>
  drule eval_phis_vars_grow >> simp[pred_setTheory.SUBSET_DEF]
QED
