(* Reuse the relocated body branches with canonical, selected-site outcomes. *)
Theory symBodyCanonicalSelected
Ancestors
  symBodyAdvanceOwn symBodyResultBranchesOwn symFrameBoundaryPairing
  asmOwnCodeInvariant asmSymOwnStep fnBlockBodySteps frameRel contextCodegenRel
  codegenSymRel asmSymBridge

Theorem sym_body_canonical_facts:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  asm_static_wf prog /\ sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  lo = SND (compute_label_offsets prog) /\
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  as.as_code = vs.vs_code /\ asm_data_env_lo_ok lo prog env vs.vs_code /\
  sym_frame_inv_own lo prog env vs.vs_code ctx cpl fn ret srest labs0 ps as ss
Proof
  strip_tac >>
  `as.as_code = vs.vs_code` by
    gvs[body_inv_def, fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def] >>
  gvs[body_inv_reloc_specialize] >>
  simp[sym_frame_inv_canonical_own] >>
  gvs[sym_frame_inv_def, asm_data_env_lo_ok_canonical, asm_sym_rel_def]
QED

Theorem canonical_successor_frame[local]:
  asm_static_wf prog /\ as.as_code = own ==>
  ((asm_steps (SND (compute_label_offsets prog)) o2pc prog n as = AsmOK as1 /\
    A /\ B /\ C /\ sym_frame_inv_own (SND (compute_label_offsets prog)) prog env own
      ctx cpl fn ret srest labs0 ps as1 ss1) <=>
   (asm_steps (SND (compute_label_offsets prog)) o2pc prog n as = AsmOK as1 /\
    A /\ B /\ C /\ sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as1 ss1))
Proof
  strip_tac >> simp[sym_frame_inv_canonical_own] >>
  metis_tac[asm_steps_code_preserved]
QED

(* Parse-time interface only: no new logical constants. *)
val _ = Parse.temp_overload_on ("selected_canonical_invoke",
  ``?ops ps' rest'.
    generate_inst_plan liveness dfg (cfg:cfg_analysis) fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions)
      (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps' = SOME (rest', ps_after) /\
    rest_ops = ops ++ rest' /\
    (!vs1. step_inst fuel ctx inst vs = OK vs1 ==>
      ?n as1 ss1.
        asm_steps lo o2pc prog n as = AsmOK as1 /\
        fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
        as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
        sym_steps prog env n ss = SymOK ss1 /\
        sym_frame_inv prog env ctx cpl fn ret srest labs0 ps' as1 ss1) /\
    (!vs1. step_inst fuel ctx inst vs = Halt vs1 ==>
      ?n as1. asm_steps lo o2pc prog n as = AsmHalt as1 /\
        venom_asm_terminal_rel vs1 as1 /\ sym_terminal (sym_steps prog env n ss)) /\
    (!a vs1. step_inst fuel ctx inst vs = Abort a vs1 ==>
      ?n as1. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as1) \/
               (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as1)) /\
        venom_asm_terminal_rel vs1 as1 /\ sym_terminal (sym_steps prog env n ss))``);

(* The two forms of the result packet differ only in the symbolic run and relation. *)
val _ = Parse.temp_overload_on ("body_result_clauses",
  ``\run rel res.
    (!vs'. res = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as' /\ sym_terminal (run n)) /\
    (!a vs'. res = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as' /\ sym_terminal (run n)) /\
    (!rv vs'. res = IntRet rv vs' ==>
       ?n as' ss'. asm_steps lo o2pc prog n as = AsmOK as' /\
               as'.as_pc = pc_ret /\
               as'.as_stack = REVERSE rv.iret_values ++ rest /\
               context_memory_rel cpl vs'.vs_memory as'.as_memory /\
               (!b. context_spill_byte cpl b /\
                    ~closure_spill_byte ctx cpl fn.fn_name b ==>
                    read_byte b as'.as_memory = read_byte b mem0) /\
               shared_state_rel vs' as' /\ run n = SymOK ss' /\ rel as' ss' /\
               ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
               (!b. context_spill_byte cpl b /\
                    ~closure_spill_byte ctx cpl fn.fn_name b ==>
                    FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
               (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))``);

(* With the runs already in false mode, only the IntRet relation needs projection. *)
val project_canonical_result =
  gvs[asm_sym_rel_own_canonical] >> rpt strip_tac >>
  qpat_x_assum `!rv vs'. _ = IntRet rv vs' ==> _` drule >>
  strip_tac >> rpt (goal_assum (drule_at Any)) >> simp[];

Theorem sym_body_nonterm_prefix_selected_canonical:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  (inst.inst_opcode = LOG ==>
    ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
  step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss /\
  (inst.inst_opcode = INVOKE ==> selected_canonical_invoke) ==>
  ?prefix' rest' ps' vs' as1 ss1 n.
    body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix' rest' (SUC k) ps' pc0 vs' as1 Inv
      ra pc_ret rest mem0 /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps' as1 ss1 /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\ sym_steps prog env n ss = SymOK ss1 /\
    block_rest fuel ctx fn bb vs = block_rest fuel ctx fn bb vs' /\
    vs'.vs_call_ctx = vs.vs_call_ctx
Proof
  simp_tac (srw_ss()) [] >> strip_tac >>
  drule_all sym_body_canonical_facts >> strip_tac >>
  qpat_x_assum `lo = SND _` SUBST_ALL_TAC >>
  drule (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `own` |-> `vs.vs_code`]
      sym_body_nonterm_prefix_selected_own)) >>
  disch_then (drule_at (Pat `sym_frame_inv_own`)) >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
  simp[SF CONJ_ss, canonical_successor_frame] >> strip_tac >>
  gvs[body_inv_reloc_specialize, sym_frame_inv_canonical_own] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem sym_body_nonok_selected_canonical:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  (!j. ~revert_forward_pair bb k j) /\ LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = res /\ (!s. res <> OK s) /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss /\
  (inst.inst_opcode = INVOKE ==> selected_canonical_invoke) ==>
  body_result_clauses (\n. sym_steps prog env n ss) (asm_sym_rel prog env)
    (block_rest fuel ctx fn bb vs)
Proof
  simp_tac (srw_ss()) [] >> strip_tac >>
  drule_all sym_body_canonical_facts >> strip_tac >>
  qpat_x_assum `lo = SND _` SUBST_ALL_TAC >>
  drule (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `own` |-> `vs.vs_code`]
      sym_body_nonok_selected_own)) >>
  disch_then (drule_at (Pat `sym_frame_inv_own`)) >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = _`)) >>
  gs[SF CONJ_ss, canonical_successor_frame] >> strip_tac >>
  project_canonical_result
QED

Theorem sym_body_revert_result_canonical:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\ revert_forward_pair bb k j /\ label_flow_ok ctx /\
  asm_static_wf prog /\ sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  body_result_clauses (\n. sym_steps prog env n ss) (asm_sym_rel prog env)
    (block_rest fuel ctx fn bb vs)
Proof
  simp_tac (srw_ss()) [] >> strip_tac >>
  drule_all sym_body_canonical_facts >> strip_tac >>
  drule_all (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `own` |-> `vs.vs_code`]
      sym_body_revert_result_minimal_own)) >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  project_canonical_result
QED
