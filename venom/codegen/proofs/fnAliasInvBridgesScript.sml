Theory fnAliasInvBridges
Ancestors
  fnAliasInvPrefix fnFrameBoundaryEntryParams fnBlockPlanStaticBodyPrefix
  fnBlockPlanStaticOffsetLive fnPlanPrefix fnLineageStatic
  venomExecProps venomExecSemantics venomInst venomWf livenessTransferProofs arithmetic list rich_list

(* Success supplies actual PARAM outcomes; no entry value shape is needed. *)
Theorem exec_block_param_prefix_success:
  !n j bb s fuel ctx t.
    j + n <= LENGTH bb.bb_instructions /\ s.vs_inst_idx = j /\
    (!k. k < n ==> is_param_opcode (EL (j+k) bb.bb_instructions).inst_opcode) /\
    exec_block fuel ctx bb s = OK t ==>
    ?u. u.vs_inst_idx = j+n /\ u.vs_labels = s.vs_labels /\
        exec_block fuel ctx bb u = OK t
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (qexists_tac `s` >> simp[]) >>
  `j < LENGTH bb.bb_instructions` by decide_tac >>
  `is_param_opcode (EL j bb.bb_instructions).inst_opcode` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `~is_terminator (EL j bb.bb_instructions).inst_opcode` by
    (Cases_on `(EL j bb.bb_instructions).inst_opcode` >>
     gvs[is_param_opcode_def, is_terminator_def]) >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp_tac std_ss [Once exec_block_def, get_instruction_def] >>
  qpat_assum `s.vs_inst_idx = j` (fn th => rewrite_tac[th]) >>
  qpat_assum `j < _` (fn th => rewrite_tac[th]) >>
  qpat_assum `~is_terminator _` (fn th => rewrite_tac[th]) >>
  simp_tac std_ss [AllCaseEqs()] >> strip_tac >>
  fs[NoAsms] >>
  `s''.vs_labels = s.vs_labels` by metis_tac[step_inst_preserves_labels_always] >>
  first_x_assum (drule_at (Pat `exec_block _ _ _ _ = _`)) >>
  simp[] >> impl_tac
  >- (rpt strip_tac >>
      first_x_assum (qspec_then `SUC k` mp_tac) >>
      simp[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_SYM]) >>
  strip_tac >> qexists_tac `u` >>
  fs[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_SYM]
QED

(* Canonical parameters supply the actual executor prefix, not value shapes. *)
Theorem ready_entry_param_execution_layout:
  codegen_ready_fn fn /\ bb = HD fn.fn_blocks ==>
  LENGTH (get_params bb.bb_instructions) <= LENGTH bb.bb_instructions /\
  (!k. k < LENGTH (get_params bb.bb_instructions) ==>
    is_param_opcode (EL k bb.bb_instructions).inst_opcode)
Proof
  strip_tac >>
  qspec_then `bb.bb_instructions` strip_assume_tac get_params_suffix >>
  `param_insts_from 0 (get_params bb.bb_instructions)` by
    metis_tac[canonical_get_params_layout] >>
  conj_tac >- (qpat_x_assum `_ = _ ++ _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `_ = _ ++ _` (fn th => once_rewrite_tac[th]) >>
  simp[EL_APPEND1] >>
  drule_all param_insts_from_el >>
  simp[callLayoutDefsTheory.param_inst_at_def]
QED

Theorem ready_body_suffix_layout:
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb ==>
  EVERY (\inst. inst.inst_opcode <> PHI /\ ~is_param_opcode inst.inst_opcode)
    (DROP (MAX (LENGTH (get_params bb.bb_instructions))
               (LENGTH (collect_phis bb.bb_instructions))) bb.bb_instructions)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `bb_well_formed bb` by
    (gvs[stackPlanGenTheory.codegen_ready_fn_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  drule_all regional_canonical_body_layout >> strip_tac >>
  simp[EVERY_EL, EL_DROP] >> rpt strip_tac
  >- (`MAX (LENGTH (get_params bb.bb_instructions))
            (LENGTH (collect_phis bb.bb_instructions)) + n <
       LENGTH (collect_phis bb.bb_instructions)` by
        (irule phi_index_in_prefix >>
         gvs[bb_well_formed_def] >> metis_tac[SUB_LEFT_LESS]) >>
      gvs[MAX_DEF] >> decide_tac) >>
  qpat_x_assum `no_param_insts _` mp_tac >>
  simp[callLayoutDefsTheory.no_param_insts_def, EVERY_EL, EL_DROP] >>
  qexists_tac
    `MAX (LENGTH (get_params bb.bb_instructions))
         (LENGTH (collect_phis bb.bb_instructions)) + n -
     LENGTH (get_params bb.bb_instructions)` >>
  gvs[MAX_DEF] >> simp[] >> decide_tac
QED
