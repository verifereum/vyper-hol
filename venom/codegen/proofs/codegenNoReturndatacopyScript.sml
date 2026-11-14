(* Opcode provenance for context plans. *)
Theory codegenNoReturndatacopy
Ancestors
  stackPlanGen stackPlanOps stackPlanTypes asmIR venomInst planWf prefixSim
  list rich_list arithmetic finite_map venomFnInstsProofs livenessTransferProofs
  planEmissionProps

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
  strip_tac >> CCONTR_TAC >> fs[] >>
  drule generate_emit_ops_origin >>
  disch_then (qspec_then `SOEmit "RETURNDATACOPY"` mp_tac) >>
  simp[plan_admin_op_def, venom_name_returndatacopy]
QED

Theorem generate_regular_inst_plan_no_returndatacopy[local]:
  generate_regular_inst_plan liveness dfg cfg fn inst live halting term cur ps =
    (ops, ps') /\ inst.inst_opcode <> RETURNDATACOPY ==>
  ~MEM (SOEmit "RETURNDATACOPY") ops
Proof
  strip_tac >>
  `EVERY (\op. op <> SOEmit "RETURNDATACOPY") ops` suffices_by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  drule generate_regular_inst_plan_preserves >>
  disch_then (qspec_then `\op. op <> SOEmit "RETURNDATACOPY"` mp_tac) >>
  impl_tac >- (conj_tac
    >- (Cases >> simp[plan_admin_op_def]) >>
    rpt gen_tac >> strip_tac >>
    drule_all generate_emit_ops_no_returndatacopy >>
    simp[EVERY_MEM] >> metis_tac[]) >> simp[]
QED

Theorem generate_inst_plan_no_returndatacopy[local]:
  generate_inst_plan liveness dfg cfg fn inst live halting term cur ps =
    SOME (ops, ps') /\ inst.inst_opcode <> RETURNDATACOPY ==>
  ~MEM (SOEmit "RETURNDATACOPY") ops
Proof
  simp[generate_inst_plan_def] >> rpt IF_CASES_TAC >> simp[] >>
  gvs[generate_offset_plan_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- metis_tac[generate_phi_plan_admin, plan_admin_no_emit] >>
  drule_all generate_regular_inst_plan_no_returndatacopy >> simp[]
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
    (gvs[AllCaseEqs()] >> metis_tac[prepare_params_plan_admin, plan_admin_no_emit]) >>
  gvs[] >> qpat_x_assum `_ = (param_ops, ps1)` kall_tac >>
  pairarg_tac >>
  `~MEM (SOEmit "RETURNDATACOPY") clean_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[clean_stack_plan_admin, plan_admin_no_emit]) >>
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
