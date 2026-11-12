(* Opcode provenance for context plans. *)
Theory codegenNoReturndatacopy
Ancestors
  stackPlanGen stackPlanOps stackPlanTypes asmIR venomInst planWf prefixSim
  list rich_list arithmetic finite_map venomFnInstsProofs livenessTransferProofs

Theorem prefix_no_emit[local]:
  EVERY is_prefix_op ops ==> ~MEM (SOEmit name) ops
Proof
  simp[EVERY_MEM] >> metis_tac[is_prefix_op_def]
QED

Theorem do_restore_no_emit[local]:
  do_restore op ps = (ops, ps') ==> ~MEM (SOEmit name) ops
Proof
  simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >> rw[] >> simp[]
QED

Theorem restore_spilled_plan_no_emit[local]:
  !ops0 ps ops ps'. restore_spilled_plan ops0 ps = (ops, ps') ==>
  ~MEM (SOEmit name) ops
Proof
  Induct >> simp[restore_spilled_plan_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[do_restore_no_emit]
QED

Theorem spill_fold_no_emit[local]:
  !items acc_ops offsets al ops offsets' al'.
  FOLDL (\(ops, offs, al) item.
    (\(off, al'). (ops ++ [SOSpill off], SNOC off offs, al'))
      (alloc_spill_slot al))
    (acc_ops, offsets, al) items = (ops, offsets', al') /\
  ~MEM (SOEmit name) acc_ops ==> ~MEM (SOEmit name) ops
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `alloc_spill_slot al` >> simp[] >> strip_tac >>
  rename1 `alloc_spill_slot al = (off, next)` >>
  first_x_assum (qspec_then `acc_ops ++ [SOSpill off]` mp_tac) >>
  simp[] >> disch_then drule >> simp[]
QED

Theorem do_dup_no_emit[local]:
  do_dup dist ps = (ops, ps') ==> ~MEM (SOEmit name) ops
Proof
  simp[do_dup_def] >> IF_CASES_TAC >- (rw[] >> simp[]) >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt IF_CASES_TAC >> simp[] >> rpt gen_tac >>
  drule spill_fold_no_emit >> simp[]
QED

Theorem do_spill_tos_no_emit[local]:
  do_spill_tos ps = (ops, ps') ==> ~MEM (SOEmit name) ops
Proof
  simp[do_spill_tos_def] >> pairarg_tac >> simp[] >> rw[] >> simp[]
QED

Theorem do_spill_at_no_emit[local]:
  do_spill_at dist ps = (ops, ps') ==> ~MEM (SOEmit name) ops
Proof
  simp[do_spill_at_def] >> IF_CASES_TAC >> simp[]
  >- metis_tac[do_spill_tos_no_emit] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule do_spill_tos_no_emit >> simp[]
QED

Theorem reduce_depth_plan_no_emit[local]:
  !fuel target_ops target_op f n ps ops ps'.
  reduce_depth_plan fuel target_ops target_op f n ps = (ops, ps') ==>
  ~MEM (SOEmit name) ops
Proof
  Induct >> simp[reduce_depth_plan_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_unfixed_depth target_op f n ps.ps_stack` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  rename1 `stack_get_unfixed_depth target_op f n ps.ps_stack = SOME depth` >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops depth n` >> simp[] >>
  pairarg_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> metis_tac[do_spill_at_no_emit]
QED

Theorem reorder_one_no_emit[local]:
  reorder_one dfg target_ops idx op ps = (ops, ps') ==>
  ~MEM (SOEmit name) ops
Proof
  simp[reorder_one_def] >> pairarg_tac >>
  `~MEM (SOEmit name) restore_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[do_restore_no_emit]) >>
  gvs[] >> qpat_x_assum `_ = (restore_ops, ps1)` kall_tac >>
  Cases_on `stack_get_unfixed_depth op (LENGTH target_ops - (idx + 1))
              (LENGTH target_ops) ps1.ps_stack` >> simp[]
  >- (rw[] >> gvs[]) >>
  pairarg_tac >>
  `~MEM (SOEmit name) reduce_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[reduce_depth_plan_no_emit]) >>
  gvs[] >> qpat_x_assum `_ = (reduce_ops, ps2)` kall_tac >>
  Cases_on `stack_get_unfixed_depth op (LENGTH target_ops - (idx + 1))
              (LENGTH target_ops) ps2.ps_stack` >> simp[]
  >- (rw[] >> gvs[]) >>
  rpt IF_CASES_TAC >> simp[] >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[do_swap_prefix_op, prefix_no_emit, MEM_APPEND]
QED

Theorem reorder_fold_no_emit[local]:
  !xs acc_ops ps ops ps'.
  FOLDL (\(ops, ps) (idx, op).
    (\(step_ops, ps'). (ops ++ step_ops, ps'))
      (reorder_one dfg target_ops idx op ps)) (acc_ops, ps) xs =
    (ops, ps') /\ ~MEM (SOEmit name) acc_ops ==>
  ~MEM (SOEmit name) ops
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[] >>
  Cases_on `reorder_one dfg target_ops h0 h1 ps` >> simp[] >> strip_tac >>
  rename1 `reorder_one _ _ _ _ _ = (step_ops, ps_next)` >>
  first_x_assum (qspec_then `acc_ops ++ step_ops` mp_tac) >> simp[] >>
  disch_then drule >> drule reorder_one_no_emit >> simp[]
QED

Theorem reorder_plan_no_emit[local]:
  reorder_plan dfg target_ops ps = (ops, ps') ==> ~MEM (SOEmit name) ops
Proof
  simp[reorder_plan_def] >> strip_tac >> drule reorder_fold_no_emit >> simp[]
QED

Theorem emit_one_input_no_emit[local]:
  emit_one_input opc live op ps = (ops, ps') ==> ~MEM (SOEmit name) ops
Proof
  simp[emit_one_input_def] >> pairarg_tac >>
  `~MEM (SOEmit name) restore_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[do_restore_no_emit]) >>
  gvs[] >> qpat_x_assum `_ = (restore_ops, ps1)` kall_tac >>
  Cases_on `op` >> simp[] >> rpt IF_CASES_TAC >> simp[] >>
  gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> metis_tac[do_dup_no_emit]
QED

Theorem emit_input_plan_no_emit[local]:
  !operands ps ops ps'.
  emit_input_plan opc operands live ps = (ops, ps') ==>
  ~MEM (SOEmit name) ops
Proof
  Induct >> simp[emit_input_plan_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[emit_one_input_no_emit, MEM_APPEND]
QED

Theorem venom_name_returndatacopy[local]:
  venom_to_evm_name opc = SOME "RETURNDATACOPY" <=> opc = RETURNDATACOPY
Proof
  Cases_on `opc` >> simp[venom_to_evm_name_def]
QED

Theorem generate_emit_ops_no_returndatacopy[local]:
  generate_emit_ops inst topics ps = (ops, ps') /\
  inst.inst_opcode <> RETURNDATACOPY ==>
  ~MEM (SOEmit "RETURNDATACOPY") ops
Proof
  simp[generate_emit_ops_def] >> rpt IF_CASES_TAC >>
  gvs[AllCaseEqs(), bump_emit_ops_def] >>
  rpt strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[venom_name_returndatacopy]
QED

Theorem generate_phi_plan_no_emit[local]:
  generate_phi_plan inst live halting ps = (ops, ps') ==>
  ~MEM (SOEmit name) ops
Proof
  simp[generate_phi_plan_def] >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
              ps.ps_stack` >> simp[] >>
  rename1 `stack_get_phi_depth _ _ = SOME depth` >>
  Cases_on `MEM (operand_to_string (stack_peek depth ps.ps_stack)) live` >>
  simp[] >> rpt (pairarg_tac >> gvs[]) >>
  rw[] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac do_dup_no_emit >>
  imp_res_tac popmany_plan_prefix_op >>
  imp_res_tac prefix_no_emit >> gvs[]
QED

Theorem generate_regular_inst_plan_no_returndatacopy[local]:
  generate_regular_inst_plan liveness dfg cfg fn inst live halting term cur ps =
    (ops, ps') /\ inst.inst_opcode <> RETURNDATACOPY ==>
  ~MEM (SOEmit "RETURNDATACOPY") ops
Proof
  simp[generate_regular_inst_plan_def] >> pairarg_tac >>
  `~MEM (SOEmit "RETURNDATACOPY") input_ops` by
    metis_tac[emit_input_plan_no_emit] >>
  gvs[] >> qpat_x_assum `_ = (input_ops, ps1)` kall_tac >>
  pairarg_tac >>
  `~MEM (SOEmit "RETURNDATACOPY") join_ops` by
    (gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
     metis_tac[reorder_plan_no_emit, restore_spilled_plan_no_emit]) >>
  gvs[] >> qpat_x_assum `_ = (join_ops, ps2)` kall_tac >>
  pairarg_tac >>
  `~MEM (SOEmit "RETURNDATACOPY") reorder_ops` by
    (gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
     gvs[AllCaseEqs()] >> metis_tac[reorder_plan_no_emit]) >>
  gvs[] >> qpat_x_assum `_ = (reorder_ops, ps4)` kall_tac >>
  pairarg_tac >>
  drule generate_emit_ops_no_returndatacopy >>
  strip_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `_ = (emit_ops, ps7)` kall_tac >>
  Cases_on `inst.inst_outputs = []` >> gvs[] >>
  qpat_x_assum `_ = (ops, ps')` mp_tac >>
  pairarg_tac >>
  `~MEM (SOEmit "RETURNDATACOPY") pop_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[popmany_plan_prefix_op, prefix_no_emit]) >>
  gvs[] >> qpat_x_assum `_ = (pop_ops, ps8)` kall_tac >>
  pairarg_tac >>
  `~MEM (SOEmit "RETURNDATACOPY") opt_ops` by
    (gvs[AllCaseEqs()] >>
     metis_tac[optimistic_swap_plan_prefix_op, prefix_no_emit]) >>
  gvs[] >> rw[] >> gvs[]
QED

Theorem generate_inst_plan_no_returndatacopy[local]:
  generate_inst_plan liveness dfg cfg fn inst live halting term cur ps =
    SOME (ops, ps') /\ inst.inst_opcode <> RETURNDATACOPY ==>
  ~MEM (SOEmit "RETURNDATACOPY") ops
Proof
  simp[generate_inst_plan_def] >> rpt IF_CASES_TAC >> simp[] >>
  gvs[generate_offset_plan_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- metis_tac[generate_phi_plan_no_emit] >>
  drule_all generate_regular_inst_plan_no_returndatacopy >> simp[]
QED

Theorem prepare_params_plan_no_emit[local]:
  prepare_params_plan liveness fn ps = (ops, ps') ==> ~MEM (SOEmit name) ops
Proof
  simp[prepare_params_plan_def] >> IF_CASES_TAC >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  imp_res_tac popmany_plan_prefix_op >>
  imp_res_tac optimistic_swap_plan_prefix_op >>
  imp_res_tac prefix_no_emit >> gvs[]
QED

Theorem clean_stack_plan_no_emit[local]:
  clean_stack_plan liveness cfg fn bb ps = (ops, ps') ==>
  ~MEM (SOEmit name) ops
Proof
  simp[clean_stack_plan_def] >> gvs[AllCaseEqs()] >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[popmany_plan_prefix_op, prefix_no_emit]
QED

Theorem generate_block_insts_plan_no_returndatacopy[local]:
  !insts i ps ops ps'.
  generate_block_insts_plan liveness dfg cfg fn bb_label halting
    n_params block_len i insts ps = SOME (ops, ps') /\
  EVERY (\inst. inst.inst_opcode <> RETURNDATACOPY) insts ==>
  ~MEM (SOEmit "RETURNDATACOPY") ops
Proof
  Induct >> simp[generate_block_insts_plan_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  metis_tac[generate_inst_plan_no_returndatacopy, MEM_APPEND]
QED

Theorem generate_block_plan_no_returndatacopy[local]:
  generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') /\
  EVERY (\inst. inst.inst_opcode <> RETURNDATACOPY) bb.bb_instructions ==>
  ~MEM (SOEmit "RETURNDATACOPY") ops
Proof
  simp[generate_block_plan_def] >> pairarg_tac >>
  `~MEM (SOEmit "RETURNDATACOPY") param_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[prepare_params_plan_no_emit]) >>
  gvs[] >> qpat_x_assum `_ = (param_ops, ps1)` kall_tac >>
  pairarg_tac >>
  `~MEM (SOEmit "RETURNDATACOPY") clean_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[clean_stack_plan_no_emit]) >>
  gvs[] >> qpat_x_assum `_ = (clean_ops, ps2)` kall_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  `EVERY (\inst. inst.inst_opcode <> RETURNDATACOPY) (non_param_insts bb)` by
    (gvs[non_param_insts_def, EVERY_MEM, MEM_FILTER] >> metis_tac[]) >>
  drule_all generate_block_insts_plan_no_returndatacopy >> simp[]
QED

Theorem fn_plan_aux_no_returndatacopy[local]:
  (!liveness dfg cfg fn worklist visited ps ops visited' ps'.
    generate_fn_plan_aux liveness dfg cfg fn worklist visited ps =
      SOME (ops, visited', ps') /\
    EVERY (\inst. inst.inst_opcode <> RETURNDATACOPY) (fn_insts fn) ==>
    ~MEM (SOEmit "RETURNDATACOPY") ops) /\
  (!liveness dfg cfg fn ss sp succs visited ps ops visited' ps'.
    generate_succs_plan liveness dfg cfg fn ss sp succs visited ps =
      SOME (ops, visited', ps') /\
    EVERY (\inst. inst.inst_opcode <> RETURNDATACOPY) (fn_insts fn) ==>
    ~MEM (SOEmit "RETURNDATACOPY") ops)
Proof
  ho_match_mp_tac generate_fn_plan_aux_ind >> rpt conj_tac
  >- (rpt gen_tac >> simp[Once generate_fn_plan_aux_def] >> rw[] >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      simp[Once generate_fn_plan_aux_def] >>
      Cases_on `MEM lbl visited` >- (gvs[] >> metis_tac[]) >>
      gvs[] >> Cases_on `lookup_block lbl fn.fn_blocks`
      >- (gvs[] >> metis_tac[]) >>
      rename1 `lookup_block lbl fn.fn_blocks = SOME bb` >>
      simp[AllCaseEqs()] >> rpt gen_tac >> strip_tac >> gvs[] >>
      `EVERY (\inst. inst.inst_opcode <> RETURNDATACOPY) bb.bb_instructions` by
        (gvs[EVERY_MEM] >> rpt strip_tac >>
         drule lookup_block_mem >> strip_tac >>
         metis_tac[MEM_fn_insts]) >>
      drule_all generate_block_plan_no_returndatacopy >> strip_tac >>
      metis_tac[MEM_APPEND])
  >- (rpt gen_tac >> simp[Once generate_fn_plan_aux_def] >> rw[] >> simp[])
  >> rpt gen_tac >> strip_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[MEM_APPEND]
QED

Theorem generate_fn_plan_with_cleanup_no_returndatacopy[local]:
  generate_fn_plan_with_cleanup ch growth fn spill_base lbl_ctr =
    SOME (ops, ps) /\
  EVERY (\inst. inst.inst_opcode <> RETURNDATACOPY) (fn_insts fn) ==>
  ~MEM (SOEmit "RETURNDATACOPY") ops
Proof
  simp[generate_fn_plan_with_cleanup_def,
       generate_fn_plan_with_cleanup_analyzed_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> metis_tac[cj 1 fn_plan_aux_no_returndatacopy]
QED

Theorem generate_context_regions_no_returndatacopy[local]:
  !fns acc acc'.
    generate_context_regions gen fns acc = SOME acc' /\
    (!fn sb lc ops ps.
       MEM fn fns /\ gen fn sb lc = SOME (ops, ps) ==>
       ~MEM (SOEmit "RETURNDATACOPY") ops) /\
    (!r. MEM r acc.cpa_regions ==>
         ~MEM (SOEmit "RETURNDATACOPY") r.sr_plan) ==>
    !r. MEM r acc'.cpa_regions ==>
        ~MEM (SOEmit "RETURNDATACOPY") r.sr_plan
Proof
  Induct >> simp[generate_context_regions_def] >>
  rpt gen_tac >> simp[AllCaseEqs()] >> rpt strip_tac >>
  first_x_assum (drule_then (qspec_then `r` mp_tac)) >>
  impl_tac >- (rw[MEM_SNOC] >> gvs[] >> metis_tac[]) >> simp[]
QED

Theorem generate_context_plan_no_returndatacopy:
  !ctx cp. generate_context_plan ctx = SOME cp /\
  (!fn inst. MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) ==>
             inst.inst_opcode <> RETURNDATACOPY) ==>
  ~MEM (SOEmit "RETURNDATACOPY") (context_plan_ops cp)
Proof
  rpt gen_tac >>
  simp[generate_context_plan_def, generate_context_plan_with_def,
       AllCaseEqs()] >> strip_tac >>
  `!r. MEM r acc.cpa_regions ==>
       ~MEM (SOEmit "RETURNDATACOPY") r.sr_plan` by
    (rpt strip_tac >> drule generate_context_regions_no_returndatacopy >>
     disch_then (qspec_then `r` mp_tac) >> impl_tac
     >- (simp[] >> rpt strip_tac >>
         drule generate_fn_plan_with_cleanup_no_returndatacopy >>
         gvs[EVERY_MEM] >> metis_tac[]) >> gvs[]) >>
  gvs[context_plan_ops_def, finish_context_plan_def,
      revert_postamble_def, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED
