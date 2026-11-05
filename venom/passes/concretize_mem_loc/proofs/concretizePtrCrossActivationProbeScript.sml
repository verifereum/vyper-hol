Theory concretizePtrCrossActivationProbe
Ancestors concretizePtrSingletonOriginProbe concretizePtrSourceOwnership
  concretizePtrChronologicalHistory concretizePtrActivationBirths ptrDiscipline
  concretizePtrLedgerAlignment concretizePtrOperationalBytes concretizePtrLedgerProbe
  concretizeStepStructure concretizeStepShape concretizeStepCallChecks
  concretizeStepRetpc concretizeStageShape
  concretizeMemLocDefs venomExecSemantics venomState venomInst
  finite_map list words venomMemProofs
Libs wordsLib

(* Extend the checked singleton-origin fixture by a deleted source NOP.
   The two calls and the imported/local stores are inherited, not copied. *)
Definition cap_caller_def:
  cap_caller = sop_caller with fn_blocks :=
    [((HD sop_caller.fn_blocks) with bb_instructions :=
      [HD (HD sop_caller.fn_blocks).bb_instructions; mk_inst 7 NOP [] []] ++
      TL (HD sop_caller.fn_blocks).bb_instructions)]
End

Definition cap_source_def:
  cap_source = mk_venom_context [sop_callee;cap_caller] (SOME "main")
End

Definition cap_observed_def:
  cap_observed = mk_venom_context [sop_leaf_out;cap_caller] (SOME "main")
End

Definition cap_layout_def:
  cap_layout = THE (compute_function_layout_fuel_in_context
    (concretize_memloc_fuel cap_caller) cap_observed [] cap_caller)
End

Definition cap_caller_out_def:
  cap_caller_out = THE (concretize_function_fuel_in_context
    (concretize_memloc_fuel cap_caller) cap_observed [] cap_caller)
End

Definition cap_target_def:
  cap_target = mk_venom_context [sop_leaf_out;cap_caller_out] (SOME "main")
End

(* These positions come from execution of the production layout, not a
   hand-selected relocation. No full stage-contract claim is made here. *)
Theorem cap_production_layout:
  concretize_function_fuel_in_context (concretize_memloc_fuel sop_callee)
    cap_source [] sop_callee = SOME sop_leaf_out /\
  FLOOKUP cap_layout.cl_positions (Allocation 1) = SOME 32 /\
  cap_layout.cl_eom = 64 /\
  cap_caller_out.fn_eom = SOME 64
Proof
  EVAL_TAC
QED

Theorem cap_output_metadata:
  cap_caller_out.fn_mems_used = [(Allocation 1,32,32);(Allocation 101,0,32)]
Proof
  EVAL_TAC
QED

Definition cap_entry_def:
  cap_entry = ptr_observe [] [] FEMPTY entry_taint cap_caller
    (HD (HD cap_caller.fn_blocks).bb_instructions) sop_initial
End

Theorem cap_source_entry:
  ptr_chrono_history sop_initial cap_source [cap_entry] cap_entry
Proof
  simp[cap_entry_def] >> irule (cj 1 ptr_chrono_history_rules) >>
  conj_tac >- (qexists_tac `"main"` >> EVAL_TAC) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  qexists_tac `"entry"` >> EVAL_TAC >>
  simp[eval_phis_def, phi_prefix_length_def]
QED

Theorem cap_source_entry_owned:
  ptr_source_ownership sop_initial cap_source [cap_entry] cap_entry
    [0] (FEMPTY |+ (0,cap_caller)) FEMPTY [] FEMPTY []
Proof
  assume_tac cap_source_entry >>
  drule (cj 1 ptr_source_ownership_rules) >>
  simp[cap_entry_def, ptr_observe_def, sop_initial_def,
    init_venom_state_def, ptr_birth_lift_def]
QED

Definition cap_after_alloc_def:
  cap_after_alloc = ptr_observe [] [] sop_g1 sop_t1 cap_caller
    (EL 1 (HD cap_caller.fn_blocks).bb_instructions) sop_s1
End

Theorem cap_alloc_step:
  ptr_chrono_step cap_source cap_entry cap_after_alloc
Proof
  simp[Once ptr_chrono_step_cases, cap_entry_def, cap_after_alloc_def,
    ptr_observe_def] >> EVAL_TAC >>
  simp[FLOOKUP_UPDATE, FUPDATE_EQ, pred_setTheory.SUBSET_DEF]
QED

Definition cap_after_nop_def:
  cap_after_nop = cap_after_alloc with
    <| po_inst := EL 2 (HD cap_caller.fn_blocks).bb_instructions;
       po_state := sop_s1 with vs_inst_idx := 2 |>
End

Definition cap_at_call_def:
  cap_at_call = ptr_observe [] [] sop_g1 sop_t2 cap_caller
    (EL 3 (HD cap_caller.fn_blocks).bb_instructions)
    (sop_s2 with vs_inst_idx := 3)
End

Theorem cap_nop_step:
  ptr_chrono_step cap_source cap_after_alloc cap_after_nop
Proof
  simp[Once ptr_chrono_step_cases, cap_after_alloc_def, cap_after_nop_def,
    ptr_observe_def] >> EVAL_TAC >>
  simp[FLOOKUP_UPDATE, FUPDATE_EQ, pred_setTheory.SUBSET_DEF]
QED

Theorem cap_store_step:
  ptr_chrono_step cap_source cap_after_nop cap_at_call
Proof
  simp[Once ptr_chrono_step_cases, cap_after_alloc_def, cap_after_nop_def,
    cap_at_call_def, ptr_observe_def] >> EVAL_TAC >>
  simp[FLOOKUP_UPDATE, FUPDATE_EQ, pred_setTheory.SUBSET_DEF]
QED

Theorem cap_call_history:
  ptr_chrono_history sop_initial cap_source
    [cap_entry;cap_after_alloc;cap_after_nop;cap_at_call] cap_at_call
Proof
  metis_tac[cap_source_entry, cap_alloc_step, cap_nop_step,
    cap_store_step, ptr_chrono_history_rules, APPEND]
QED

Definition cap_frame_def:
  cap_frame = sop_frame with
    <| cf_fn := cap_caller;
       cf_inst := EL 3 (HD cap_caller.fn_blocks).bb_instructions;
       cf_state := sop_s2 with vs_inst_idx := 3 |>
End

Definition cap_in_callee_def:
  cap_in_callee = ptr_observe [cap_frame] [SOME (256,32)] FEMPTY
    (sop_t2 with t_var := FEMPTY) sop_callee
    (HD (HD sop_callee.fn_blocks).bb_instructions) sop_cs
End

Theorem cap_call_step:
  ptr_chrono_step cap_source cap_at_call cap_in_callee
Proof
  simp[Once ptr_chrono_step_cases, cap_at_call_def, cap_in_callee_def,
    cap_frame_def, ptr_observe_def] >> EVAL_TAC >>
  simp[FLOOKUP_UPDATE, FUPDATE_EQ, pred_setTheory.SUBSET_DEF,
    eval_phis_def, phi_prefix_length_def, eval_operands_def,
    eval_operand_def, lookup_var_def, op_prov_def]
QED

Definition cap_callee_suffix_def:
  cap_callee_suffix =
    [ptr_observe [cap_frame] sop_pg sop_gp sop_tp sop_callee
       (EL 1 (HD sop_callee.fn_blocks).bb_instructions) sop_cp;
     ptr_observe [cap_frame] sop_pg sop_gb sop_tb sop_callee
       (EL 2 (HD sop_callee.fn_blocks).bb_instructions) sop_cb;
     ptr_observe [cap_frame] sop_pg sop_gb sop_tw sop_callee
       (EL 3 (HD sop_callee.fn_blocks).bb_instructions) sop_cw;
     ptr_observe [cap_frame] sop_pg sop_gb sop_tr sop_callee
       (EL 4 (HD sop_callee.fn_blocks).bb_instructions) sop_cr]
End

Theorem cap_callee_steps:
  ptr_chrono_step cap_source cap_in_callee (EL 0 cap_callee_suffix) /\
  ptr_chrono_step cap_source (EL 0 cap_callee_suffix) (EL 1 cap_callee_suffix) /\
  ptr_chrono_step cap_source (EL 1 cap_callee_suffix) (EL 2 cap_callee_suffix) /\
  ptr_chrono_step cap_source (EL 2 cap_callee_suffix) (EL 3 cap_callee_suffix)
Proof
  rpt conj_tac >>
  simp[Once ptr_chrono_step_cases, cap_callee_suffix_def,
    cap_in_callee_def, ptr_observe_def]
  >- (disj1_tac >> qexistsl_tac [`sop_cp with vs_inst_idx := 0`,`0`] >>
      CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_t2``, ``cap_source``]) >>
      simp[FLOOKUP_UPDATE, FUPDATE_EQ])
  >- (disj1_tac >> qexistsl_tac [`sop_cb with vs_inst_idx := 1`,`0`] >>
      CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_tp``, ``cap_source``]) >>
      simp[FLOOKUP_UPDATE, FUPDATE_EQ, pred_setTheory.SUBSET_DEF])
  >- (disj1_tac >> qexistsl_tac [`sop_cw with vs_inst_idx := 2`,`0`] >>
      CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_tb``, ``cap_source``]) >>
      simp[FLOOKUP_UPDATE, FUPDATE_EQ]) >>
  disj1_tac >> qexistsl_tac [`sop_cr with vs_inst_idx := 3`,`0`] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_tw``, ``cap_source``]) >>
  simp[FLOOKUP_UPDATE, FUPDATE_EQ]
QED

Definition cap_second_call_def:
  cap_second_call = ptr_observe [] [] sop_g1 sop_t3 cap_caller
    (EL 4 (HD cap_caller.fn_blocks).bb_instructions)
    (sop_s3 with vs_inst_idx := 4)
End

Theorem cap_return_step:
  ptr_chrono_step cap_source (EL 3 cap_callee_suffix) cap_second_call
Proof
  simp[Once ptr_chrono_step_cases, cap_callee_suffix_def,
    cap_second_call_def, ptr_observe_def] >>
  qexistsl_tac [`<|iret_values := []; iret_adopt_fmp := NONE|>`,
    `sop_cr`, `sop_s3 with vs_inst_idx := 3`, `0`] >>
  simp[cap_frame_def, sop_frame_def, sop_t3_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_tr``, ``cap_source``]) >>
  simp[FLOOKUP_UPDATE, FUPDATE_EQ]
QED

Definition cap_frame2_def:
  cap_frame2 = sop_frame2 with
    <| cf_fn := cap_caller;
       cf_inst := EL 4 (HD cap_caller.fn_blocks).bb_instructions;
       cf_state := sop_s3 with vs_inst_idx := 4 |>
End

Definition cap_in_callee2_def:
  cap_in_callee2 = ptr_observe [cap_frame2] sop_pg FEMPTY
    (sop_t3 with t_var := FEMPTY) sop_callee
    (HD (HD sop_callee.fn_blocks).bb_instructions) sop_cs2
End

Theorem cap_second_entry_step:
  ptr_chrono_step cap_source cap_second_call cap_in_callee2
Proof
  simp[Once ptr_chrono_step_cases, cap_second_call_def, cap_in_callee2_def,
    cap_frame2_def, ptr_observe_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_t3``]) >>
  simp[FLOOKUP_UPDATE, FUPDATE_EQ, pred_setTheory.SUBSET_DEF,
    eval_phis_def, phi_prefix_length_def, eval_operands_def,
    eval_operand_def, lookup_var_def, op_prov_def]
QED

Definition cap_source_prefix_def:
  cap_source_prefix =
    [cap_entry;cap_after_alloc;cap_after_nop;cap_at_call;cap_in_callee] ++
    cap_callee_suffix ++ [cap_second_call;cap_in_callee2]
End


Theorem cap_second_entry_history:
  ptr_chrono_history sop_initial cap_source cap_source_prefix cap_in_callee2
Proof
  `cap_source_prefix =
    ((((((([cap_entry;cap_after_alloc;cap_after_nop;cap_at_call] ++
      [cap_in_callee]) ++ [EL 0 cap_callee_suffix]) ++
      [EL 1 cap_callee_suffix]) ++ [EL 2 cap_callee_suffix]) ++
      [EL 3 cap_callee_suffix]) ++ [cap_second_call]) ++ [cap_in_callee2])`
    by simp[cap_source_prefix_def, cap_callee_suffix_def] >>
  pop_assum SUBST1_TAC >>
  irule (cj 2 ptr_chrono_history_rules) >> qexists_tac `cap_second_call` >>
  conj_tac >- ACCEPT_TAC cap_second_entry_step >>
  irule (cj 2 ptr_chrono_history_rules) >> qexists_tac `EL 3 cap_callee_suffix` >>
  conj_tac >- ACCEPT_TAC cap_return_step >>
  irule (cj 2 ptr_chrono_history_rules) >> qexists_tac `EL 2 cap_callee_suffix` >>
  conj_tac >- metis_tac[cap_callee_steps] >>
  irule (cj 2 ptr_chrono_history_rules) >> qexists_tac `EL 1 cap_callee_suffix` >>
  conj_tac >- metis_tac[cap_callee_steps] >>
  irule (cj 2 ptr_chrono_history_rules) >> qexists_tac `EL 0 cap_callee_suffix` >>
  conj_tac >- metis_tac[cap_callee_steps] >>
  irule (cj 2 ptr_chrono_history_rules) >> qexists_tac `cap_in_callee` >>
  conj_tac >- metis_tac[cap_callee_steps] >>
  irule (cj 2 ptr_chrono_history_rules) >> qexists_tac `cap_at_call` >>
  conj_tac >- ACCEPT_TAC cap_call_step >>
  ACCEPT_TAC cap_call_history
QED

Definition cap_param2_def:
  cap_param2 = ptr_observe [cap_frame2] sop_pg sop_gp sop_tp2 sop_callee
    (EL 1 (HD sop_callee.fn_blocks).bb_instructions) sop_cp2
End

Definition cap_alloc2_def:
  cap_alloc2 = ptr_observe [cap_frame2] sop_pg sop_gb sop_tb2 sop_callee
    (EL 2 (HD sop_callee.fn_blocks).bb_instructions) sop_cb2
End

Theorem cap_second_activation_steps:
  ptr_chrono_step cap_source cap_in_callee2 cap_param2 /\
  ptr_chrono_step cap_source cap_param2 cap_alloc2
Proof
  conj_tac
  >- (simp[Once ptr_chrono_step_cases, cap_in_callee2_def, cap_param2_def,
        ptr_observe_def] >>
      disj1_tac >> qexistsl_tac [`sop_cp2 with vs_inst_idx := 0`,`0`] >>
      simp[sop_second_param_origins, GSYM sop_tp2_def, sop_cs2_projections,
        sop_cp2_def, update_var_def] >>
      CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_t3``, ``cap_source``, ``sop_cs2``]) >>
      simp[FLOOKUP_UPDATE, FUPDATE_EQ, sop_cs2_projections]) >>
  simp[Once ptr_chrono_step_cases, cap_param2_def, cap_alloc2_def,
    ptr_observe_def] >>
  disj1_tac >> qexistsl_tac [`sop_cb2 with vs_inst_idx := 1`,`0`] >>
  simp[sop_second_alloca_origins, GSYM sop_tb2_def, sop_cp2_projections,
    sop_cb2_projections] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_tp2``, ``cap_source``, ``sop_cp2``, ``sop_cb2``]) >>
  simp[FLOOKUP_UPDATE, FUPDATE_EQ, sop_cp2_projections, sop_cb2_projections,
    sop_cb2_def, update_var_def, venom_state_component_equality]
QED

Theorem cap_repeated_alloc_history:
  ptr_chrono_history sop_initial cap_source
    ((cap_source_prefix ++ [cap_param2]) ++ [cap_alloc2]) cap_alloc2
Proof
  irule (cj 2 ptr_chrono_history_rules) >> qexists_tac `cap_param2` >>
  conj_tac >- metis_tac[cap_second_activation_steps] >>
  irule (cj 2 ptr_chrono_history_rules) >> qexists_tac `cap_in_callee2` >>
  conj_tac >- metis_tac[cap_second_activation_steps] >>
  ACCEPT_TAC cap_second_entry_history
QED

Definition cap_target_entry_def:
  cap_target_entry = ptr_observe [] [] FEMPTY entry_taint cap_caller_out
    (HD (HD cap_caller_out.fn_blocks).bb_instructions) sop_initial
End

Theorem cap_target_entry_history:
  ptr_chrono_history sop_initial cap_target [cap_target_entry] cap_target_entry
Proof
  simp[cap_target_entry_def] >> irule (cj 1 ptr_chrono_history_rules) >>
  conj_tac >- (qexists_tac `"main"` >> EVAL_TAC) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  qexists_tac `"entry"` >> EVAL_TAC >>
  simp[eval_phis_def, phi_prefix_length_def]
QED

Definition cap_target_to_call_def:
  cap_target_to_call = THE (ptr_ledger_follow cap_target
    [EL 1 (HD cap_caller_out.fn_blocks).bb_instructions;
     EL 2 (HD cap_caller_out.fn_blocks).bb_instructions] cap_target_entry)
End

Theorem cap_target_to_call_checked:
  ptr_ledger_follow cap_target
    [EL 1 (HD cap_caller_out.fn_blocks).bb_instructions;
     EL 2 (HD cap_caller_out.fn_blocks).bb_instructions] cap_target_entry =
  SOME cap_target_to_call
Proof
  simp[cap_target_to_call_def] >> EVAL_TAC >> simp[]
QED

Theorem cap_target_call_history:
  ptr_chrono_history sop_initial cap_target
    ([cap_target_entry] ++ cap_target_to_call) (LAST cap_target_to_call)
Proof
  `cap_target_to_call <> []` by (EVAL_TAC >> simp[]) >>
  assume_tac cap_target_entry_history >>
  assume_tac cap_target_to_call_checked >>
  drule_all ptr_ledger_follow_history >> simp[]
QED

Definition cap_tcall_def:
  cap_tcall = LAST cap_target_to_call
End

Definition cap_tframe_def:
  cap_tframe = <| cf_fn := cap_caller_out; cf_inst := cap_tcall.po_inst;
    cf_state := cap_tcall.po_state; cf_params := cap_tcall.po_params;
    cf_prov := cap_tcall.po_prov; cf_tvar := cap_tcall.po_taint.t_var |>
End

Definition cap_tcs_def:
  cap_tcs = THE (setup_callee sop_leaf_out [32w] cap_tcall.po_state)
End

Definition cap_tcallee_def:
  cap_tcallee = ptr_observe [cap_tframe] [NONE] FEMPTY
    (cap_tcall.po_taint with t_var := FEMPTY) sop_leaf_out
    (HD (HD sop_leaf_out.fn_blocks).bb_instructions) cap_tcs
End

Theorem cap_target_call_view:
  cap_tcall = ptr_observe [] [] FEMPTY
    (entry_taint with t_var := FEMPTY |+ ("a",{})) cap_caller_out
    (EL 2 (HD cap_caller_out.fn_blocks).bb_instructions)
    ((mstore 32 1w (update_var "a" 32w sop_initial)) with vs_inst_idx := 2)
Proof
  EVAL_TAC >> simp[FLOOKUP_UPDATE, FUPDATE_EQ]
QED

Theorem cap_target_call_step:
  ptr_chrono_step cap_target cap_tcall cap_tcallee
Proof
  simp[Once ptr_chrono_step_cases, cap_target_call_view,
    cap_tcallee_def, cap_tframe_def, ptr_observe_def] >> EVAL_TAC >>
  simp[FLOOKUP_UPDATE, FUPDATE_EQ, pred_setTheory.SUBSET_DEF,
    eval_phis_def, phi_prefix_length_def, eval_operands_def,
    eval_operand_def, lookup_var_def, op_prov_def]
QED

Definition cap_target_callee_tail_def:
  cap_target_callee_tail = THE (ptr_ledger_follow cap_target
    (TL (HD sop_leaf_out.fn_blocks).bb_instructions) cap_tcallee)
End

Theorem cap_target_callee_follow:
  ptr_ledger_follow cap_target (TL (HD sop_leaf_out.fn_blocks).bb_instructions)
    cap_tcallee = SOME cap_target_callee_tail
Proof
  simp[cap_target_callee_tail_def, cap_tcallee_def, cap_tcs_def,
    cap_target_call_view, ptr_observe_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``cap_tframe``]) >> simp[]
QED

Theorem cap_target_return_history:
  ptr_chrono_history sop_initial cap_target
    ((([cap_target_entry] ++ cap_target_to_call) ++ [cap_tcallee]) ++
      cap_target_callee_tail)
    (if cap_target_callee_tail = [] then cap_tcallee else LAST cap_target_callee_tail)
Proof
  `ptr_chrono_history sop_initial cap_target
      (([cap_target_entry] ++ cap_target_to_call) ++ [cap_tcallee]) cap_tcallee`
    by (irule (cj 2 ptr_chrono_history_rules) >> qexists_tac `cap_tcall` >>
        conj_tac >- ACCEPT_TAC cap_target_call_step >>
        mp_tac cap_target_call_history >> simp[cap_tcall_def]) >>
  assume_tac cap_target_callee_follow >>
  drule_all ptr_ledger_follow_history >> simp[]
QED

Definition cap_tr_def:
  cap_tr = LAST cap_target_callee_tail
End

Definition cap_tcr_def:
  cap_tcr = (mstore 0 9w (mstore 32 7w
    (update_var "b" 0w (update_var "p" 32w cap_tcs)))) with vs_inst_idx := 4
End

Theorem cap_target_return_view:
  cap_tr = ptr_observe [cap_tframe] [NONE] FEMPTY
    (entry_taint with t_var := FEMPTY |+ ("p",{}) |+ ("b",{})) sop_leaf_out
    (EL 4 (HD sop_leaf_out.fn_blocks).bb_instructions) cap_tcr
Proof
  simp[cap_tr_def, cap_target_callee_tail_def, cap_tcallee_def, cap_tcs_def,
    cap_target_call_view, cap_tcr_def, ptr_observe_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``cap_tframe``]) >>
  simp[FLOOKUP_UPDATE, FUPDATE_EQ]
QED

Definition cap_target_second_call_def:
  cap_target_second_call = ptr_observe [] [] FEMPTY
    (cap_tr.po_taint with t_var := cap_tcall.po_taint.t_var) cap_caller_out
    (EL 3 (HD cap_caller_out.fn_blocks).bb_instructions)
    ((merge_callee_state cap_tcall.po_state cap_tr.po_state) with vs_inst_idx := 3)
End

Theorem cap_target_ret_step:
  ptr_chrono_step cap_target cap_tr cap_target_second_call
Proof
  simp[Once ptr_chrono_step_cases, cap_target_second_call_def,
    cap_target_return_view, cap_tframe_def, cap_target_call_view,
    ptr_observe_def] >>
  qexistsl_tac [`<|iret_values := []; iret_adopt_fmp := NONE|>`,
    `cap_tcr`, `merge_callee_state cap_tcall.po_state cap_tcr`, `0`] >>
  simp[cap_target_call_view, ptr_observe_def, cap_tcr_def, cap_tcs_def] >>
  EVAL_TAC >> simp[FLOOKUP_UPDATE, FUPDATE_EQ]
QED

Definition cap_tframe2_def:
  cap_tframe2 = <| cf_fn := cap_caller_out; cf_inst := cap_target_second_call.po_inst;
    cf_state := cap_target_second_call.po_state; cf_params := [];
    cf_prov := FEMPTY; cf_tvar := cap_target_second_call.po_taint.t_var |>
End

Definition cap_tcs2_def:
  cap_tcs2 = THE (setup_callee sop_leaf_out [32w] cap_target_second_call.po_state)
End

Definition cap_tcallee2_def:
  cap_tcallee2 = ptr_observe [cap_tframe2] [NONE] FEMPTY
    (cap_target_second_call.po_taint with t_var := FEMPTY) sop_leaf_out
    (HD (HD sop_leaf_out.fn_blocks).bb_instructions) cap_tcs2
End

Theorem cap_target_second_entry_step:
  ptr_chrono_step cap_target cap_target_second_call cap_tcallee2
Proof
  simp[Once ptr_chrono_step_cases, cap_tcallee2_def, cap_tframe2_def,
    cap_tcs2_def, cap_target_second_call_def, cap_target_return_view,
    cap_target_call_view, ptr_observe_def, cap_tcr_def, cap_tcs_def] >>
  EVAL_TAC >>
  simp[FLOOKUP_UPDATE, FUPDATE_EQ, eval_phis_def, phi_prefix_length_def,
    eval_operands_def, eval_operand_def, lookup_var_def, op_prov_def]
QED

Definition cap_target_reuse_tail_def:
  cap_target_reuse_tail = THE (ptr_ledger_follow cap_target
    [EL 1 (HD sop_leaf_out.fn_blocks).bb_instructions;
     EL 2 (HD sop_leaf_out.fn_blocks).bb_instructions] cap_tcallee2)
End

Theorem cap_target_reuse_follow:
  ptr_ledger_follow cap_target
    [EL 1 (HD sop_leaf_out.fn_blocks).bb_instructions;
     EL 2 (HD sop_leaf_out.fn_blocks).bb_instructions] cap_tcallee2 =
  SOME cap_target_reuse_tail
Proof
  simp[cap_target_reuse_tail_def, cap_tcallee2_def, cap_tcs2_def,
    cap_target_second_call_def, cap_target_return_view, cap_target_call_view,
    cap_tcr_def, cap_tcs_def, ptr_observe_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``cap_tframe2``]) >> simp[]
QED

Theorem cap_target_tail_nonempty:
  cap_target_callee_tail <> []
Proof
  simp[cap_target_callee_tail_def, cap_tcallee_def, cap_tcs_def,
    cap_target_call_view, ptr_observe_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``cap_tframe``]) >> simp[]
QED

Definition cap_target_prefix_def:
  cap_target_prefix =
    ((((([cap_target_entry] ++ cap_target_to_call) ++ [cap_tcallee]) ++
       cap_target_callee_tail) ++ [cap_target_second_call]) ++ [cap_tcallee2]) ++
    cap_target_reuse_tail
End

Theorem cap_target_repeated_alloc_history:
  ptr_chrono_history sop_initial cap_target cap_target_prefix
    (if cap_target_reuse_tail = [] then cap_tcallee2 else LAST cap_target_reuse_tail)
Proof
  `ptr_chrono_history sop_initial cap_target
    ((((([cap_target_entry] ++ cap_target_to_call) ++ [cap_tcallee]) ++
       cap_target_callee_tail) ++ [cap_target_second_call]) ++ [cap_tcallee2])
    cap_tcallee2`
    by (irule (cj 2 ptr_chrono_history_rules) >>
        qexists_tac `cap_target_second_call` >>
        conj_tac >- ACCEPT_TAC cap_target_second_entry_step >>
        irule (cj 2 ptr_chrono_history_rules) >> qexists_tac `cap_tr` >>
        conj_tac >- ACCEPT_TAC cap_target_ret_step >>
        mp_tac cap_target_return_history >>
        simp[cap_target_tail_nonempty, cap_tr_def]) >>
  assume_tac cap_target_reuse_follow >>
  drule_all ptr_ledger_follow_history >> simp[cap_target_prefix_def]
QED

Definition cap_owned_a_def:
  cap_owned_a = FEMPTY |+ ("a",(0n,1n))
End

Theorem cap_tagged_alloc:
  ptr_tagged_chrono_step cap_source 0 cap_entry cap_after_alloc
    [] FEMPTY [] [] cap_owned_a []
Proof
  simp[Once ptr_tagged_chrono_step_cases, cap_entry_def, cap_after_alloc_def,
    ptr_observe_def] >>
  disj1_tac >> qexistsl_tac [`sop_s1 with vs_inst_idx := 0`,`0`] >>
  EVAL_TAC >> simp[FLOOKUP_UPDATE, FUPDATE_EQ]
QED

Theorem cap_tagged_nop:
  ptr_tagged_chrono_step cap_source 0 cap_after_alloc cap_after_nop
    [] cap_owned_a [] [] cap_owned_a []
Proof
  simp[Once ptr_tagged_chrono_step_cases, cap_after_alloc_def, cap_after_nop_def,
    ptr_observe_def] >> EVAL_TAC >> simp[FLOOKUP_UPDATE, FUPDATE_EQ]
QED

Theorem cap_tagged_store:
  ptr_tagged_chrono_step cap_source 0 cap_after_nop cap_at_call
    [] cap_owned_a [] [] cap_owned_a []
Proof
  simp[Once ptr_tagged_chrono_step_cases, cap_after_alloc_def, cap_after_nop_def,
    cap_at_call_def, ptr_observe_def] >> EVAL_TAC >>
  simp[FLOOKUP_UPDATE, FUPDATE_EQ]
QED

Definition cap_birth_a_def:
  cap_birth_a = FEMPTY |+ ((0n,1n),(256n,32n))
End

Theorem cap_after_alloc_owned:
  ptr_source_ownership sop_initial cap_source ([cap_entry] ++ [cap_after_alloc])
    cap_after_alloc [0] (FEMPTY |+ (0,cap_caller)) cap_birth_a [] cap_owned_a []
Proof
  assume_tac cap_source_entry_owned >> assume_tac cap_tagged_alloc >>
  drule (cj 2 ptr_source_ownership_rules) >> simp[] >>
  disch_then (drule_at Any) >>
  `ptr_activation_tokens [cap_entry] cap_entry cap_after_alloc [0] = [0] /\
   ptr_activation_registry [cap_entry] cap_entry cap_after_alloc
     (FEMPTY |+ (0,cap_caller)) = FEMPTY |+ (0,cap_caller)` by
    simp[concretizePtrActivationChronologyTheory.ptr_activation_tokens_def,
      concretizePtrActivationChronologyTheory.ptr_activation_registry_def,
      cap_entry_def, cap_after_alloc_def, ptr_observe_def] >>
  `ptr_birth_overlay 0 cap_after_alloc.po_state.vs_allocas FEMPTY = cap_birth_a` by
    (simp[fmap_eq_flookup] >> Cases >>
     simp[ptr_birth_overlay_lookup, cap_after_alloc_def, ptr_observe_def,
       sop_s1_def, update_var_def, cap_birth_a_def, FLOOKUP_UPDATE] >>
     rpt IF_CASES_TAC >> gvs[]) >> simp[]
QED

Definition cap_birth_nop_def:
  cap_birth_nop = ptr_birth_overlay 0 cap_after_nop.po_state.vs_allocas cap_birth_a
End
Definition cap_birth_call_def:
  cap_birth_call = ptr_birth_overlay 0 cap_at_call.po_state.vs_allocas cap_birth_nop
End

Theorem cap_after_nop_owned:
  ptr_source_ownership sop_initial cap_source
    (([cap_entry] ++ [cap_after_alloc]) ++ [cap_after_nop]) cap_after_nop
    [0] (FEMPTY |+ (0,cap_caller)) cap_birth_nop [] cap_owned_a []
Proof
  assume_tac cap_after_alloc_owned >> assume_tac cap_tagged_nop >>
  drule (cj 2 ptr_source_ownership_rules) >> simp[] >>
  disch_then (drule_at Any) >>
  simp[concretizePtrActivationChronologyTheory.ptr_activation_tokens_def,
    concretizePtrActivationChronologyTheory.ptr_activation_registry_def,
    cap_birth_nop_def, cap_after_nop_def, cap_after_alloc_def, ptr_observe_def]
QED

Theorem cap_at_call_owned:
  ptr_source_ownership sop_initial cap_source
    [cap_entry;cap_after_alloc;cap_after_nop;cap_at_call] cap_at_call
    [0] (FEMPTY |+ (0,cap_caller)) cap_birth_call [] cap_owned_a []
Proof
  assume_tac cap_after_nop_owned >> assume_tac cap_tagged_store >>
  drule (cj 2 ptr_source_ownership_rules) >> simp[] >>
  disch_then (drule_at Any) >>
  simp[concretizePtrActivationChronologyTheory.ptr_activation_tokens_def,
    concretizePtrActivationChronologyTheory.ptr_activation_registry_def,
    cap_birth_call_def, cap_after_nop_def, cap_after_alloc_def,
    cap_at_call_def, ptr_observe_def]
QED

Theorem cap_tagged_call:
  ptr_tagged_chrono_step cap_source 0 cap_at_call cap_in_callee
    [] cap_owned_a [] [SOME (0,1)] FEMPTY [([],cap_owned_a)]
Proof
  simp[Once ptr_tagged_chrono_step_cases, cap_at_call_def, cap_in_callee_def,
    cap_frame_def, ptr_observe_def] >> EVAL_TAC >>
  simp[FLOOKUP_UPDATE, FUPDATE_EQ, pred_setTheory.SUBSET_DEF,
    eval_phis_def, phi_prefix_length_def, eval_operands_def,
    eval_operand_def, lookup_var_def, op_prov_def]
QED

Definition cap_birth_entry1_def:
  cap_birth_entry1 = ptr_birth_overlay 4 cap_in_callee.po_state.vs_allocas cap_birth_call
End

Theorem cap_first_entry_owned:
  ptr_source_ownership sop_initial cap_source
    ([cap_entry;cap_after_alloc;cap_after_nop;cap_at_call] ++ [cap_in_callee])
    cap_in_callee [4;0] (FEMPTY |+ (0,cap_caller) |+ (4,sop_callee))
    cap_birth_entry1 [SOME (0,1)] FEMPTY [([],cap_owned_a)]
Proof
  assume_tac cap_at_call_owned >> assume_tac cap_tagged_call >>
  drule (cj 2 ptr_source_ownership_rules) >> simp[] >>
  disch_then (drule_at Any) >>
  simp[concretizePtrActivationChronologyTheory.ptr_activation_tokens_def,
    concretizePtrActivationChronologyTheory.ptr_activation_registry_def,
    cap_birth_entry1_def, cap_at_call_def, cap_in_callee_def, ptr_observe_def]
QED

Definition cap_owned_p_def:
  cap_owned_p = FEMPTY |+ ("p",(0n,1n))
End
Definition cap_owned_b_def:
  cap_owned_b = cap_owned_p |+ ("b",(4n,101n))
End

Theorem cap_tagged_callee_steps:
  ptr_tagged_chrono_step cap_source 4 cap_in_callee (EL 0 cap_callee_suffix)
    [SOME (0,1)] FEMPTY [([],cap_owned_a)]
    [SOME (0,1)] cap_owned_p [([],cap_owned_a)] /\
  ptr_tagged_chrono_step cap_source 4 (EL 0 cap_callee_suffix) (EL 1 cap_callee_suffix)
    [SOME (0,1)] cap_owned_p [([],cap_owned_a)]
    [SOME (0,1)] cap_owned_b [([],cap_owned_a)] /\
  ptr_tagged_chrono_step cap_source 4 (EL 1 cap_callee_suffix) (EL 2 cap_callee_suffix)
    [SOME (0,1)] cap_owned_b [([],cap_owned_a)]
    [SOME (0,1)] cap_owned_b [([],cap_owned_a)] /\
  ptr_tagged_chrono_step cap_source 4 (EL 2 cap_callee_suffix) (EL 3 cap_callee_suffix)
    [SOME (0,1)] cap_owned_b [([],cap_owned_a)]
    [SOME (0,1)] cap_owned_b [([],cap_owned_a)]
Proof
  rpt conj_tac >>
  simp[Once ptr_tagged_chrono_step_cases, cap_callee_suffix_def,
    cap_in_callee_def, ptr_observe_def]
  >- (disj1_tac >> qexistsl_tac [`sop_cp with vs_inst_idx := 0`,`0`] >>
      CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_t2``, ``cap_source``]) >>
      simp[FLOOKUP_UPDATE, FUPDATE_EQ])
  >- (disj1_tac >> qexistsl_tac [`sop_cb with vs_inst_idx := 1`,`0`] >>
      CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_tp``, ``cap_source``]) >>
      simp[FLOOKUP_UPDATE, FUPDATE_EQ])
  >- (disj1_tac >> qexistsl_tac [`sop_cw with vs_inst_idx := 2`,`0`] >>
      CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_tb``, ``cap_source``]) >>
      simp[FLOOKUP_UPDATE, FUPDATE_EQ]) >>
  disj1_tac >> qexistsl_tac [`sop_cr with vs_inst_idx := 3`,`0`] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_tw``, ``cap_source``]) >>
  simp[FLOOKUP_UPDATE, FUPDATE_EQ]
QED

Definition cap_birth_return1_def:
  cap_birth_return1 = ptr_birth_overlay 4 (EL 3 cap_callee_suffix).po_state.vs_allocas
    (ptr_birth_overlay 4 (EL 2 cap_callee_suffix).po_state.vs_allocas
      (ptr_birth_overlay 4 (EL 1 cap_callee_suffix).po_state.vs_allocas
        (ptr_birth_overlay 4 (EL 0 cap_callee_suffix).po_state.vs_allocas cap_birth_entry1)))
End

Theorem cap_callee_stack_views[local]:
  cap_in_callee.po_stack = [cap_frame] /\
  (!n. n < 4 ==> (EL n cap_callee_suffix).po_stack = [cap_frame])
Proof
  simp[cap_in_callee_def, cap_callee_suffix_def, ptr_observe_def] >>
  rpt strip_tac >> `n = 0 \/ n = 1 \/ n = 2 \/ n = 3` by decide_tac >> gvs[]
QED


Definition cap_birth_param1_def:
  cap_birth_param1 = ptr_birth_overlay 4 (EL 0 cap_callee_suffix).po_state.vs_allocas cap_birth_entry1
End
Definition cap_birth_alloc1_def:
  cap_birth_alloc1 = ptr_birth_overlay 4 (EL 1 cap_callee_suffix).po_state.vs_allocas cap_birth_param1
End
Definition cap_birth_store1_def:
  cap_birth_store1 = ptr_birth_overlay 4 (EL 2 cap_callee_suffix).po_state.vs_allocas cap_birth_alloc1
End

Theorem cap_param1_owned:
  ptr_source_ownership sop_initial cap_source
    (([cap_entry;cap_after_alloc;cap_after_nop;cap_at_call] ++ [cap_in_callee]) ++
      [EL 0 cap_callee_suffix]) (EL 0 cap_callee_suffix) [4;0]
    (FEMPTY |+ (0,cap_caller) |+ (4,sop_callee)) cap_birth_param1
    [SOME (0,1)] cap_owned_p [([],cap_owned_a)]
Proof
  assume_tac cap_first_entry_owned >> assume_tac (cj 1 cap_tagged_callee_steps) >>
  drule (cj 2 ptr_source_ownership_rules) >> simp[] >>
  disch_then (drule_at Any) >>
  simp[concretizePtrActivationChronologyTheory.ptr_activation_tokens_def,
    concretizePtrActivationChronologyTheory.ptr_activation_registry_def,
    cap_callee_stack_views, cap_birth_param1_def]
QED

Theorem cap_alloc1_owned:
  ptr_source_ownership sop_initial cap_source
    ((([cap_entry;cap_after_alloc;cap_after_nop;cap_at_call] ++ [cap_in_callee]) ++
      [EL 0 cap_callee_suffix]) ++ [EL 1 cap_callee_suffix]) (EL 1 cap_callee_suffix) [4;0]
    (FEMPTY |+ (0,cap_caller) |+ (4,sop_callee)) cap_birth_alloc1
    [SOME (0,1)] cap_owned_b [([],cap_owned_a)]
Proof
  assume_tac cap_param1_owned >>
  assume_tac (REWRITE_RULE [EL] (cj 2 cap_tagged_callee_steps)) >>
  drule (cj 2 ptr_source_ownership_rules) >> simp[] >>
  disch_then (drule_at Any) >>
  simp[concretizePtrActivationChronologyTheory.ptr_activation_tokens_def,
    concretizePtrActivationChronologyTheory.ptr_activation_registry_def,
    cap_callee_stack_views,
    SRULE [EL] (Q.SPEC `0` (cj 2 cap_callee_stack_views)), cap_birth_alloc1_def]
QED

Theorem cap_store1_owned:
  ptr_source_ownership sop_initial cap_source
    (((([cap_entry;cap_after_alloc;cap_after_nop;cap_at_call] ++ [cap_in_callee]) ++
      [EL 0 cap_callee_suffix]) ++ [EL 1 cap_callee_suffix]) ++ [EL 2 cap_callee_suffix])
    (EL 2 cap_callee_suffix) [4;0]
    (FEMPTY |+ (0,cap_caller) |+ (4,sop_callee)) cap_birth_store1
    [SOME (0,1)] cap_owned_b [([],cap_owned_a)]
Proof
  assume_tac cap_alloc1_owned >> assume_tac (cj 3 cap_tagged_callee_steps) >>
  drule (cj 2 ptr_source_ownership_rules) >> simp[] >>
  disch_then (drule_at Any) >>
  simp[concretizePtrActivationChronologyTheory.ptr_activation_tokens_def,
    concretizePtrActivationChronologyTheory.ptr_activation_registry_def,
    cap_callee_stack_views, cap_birth_store1_def]
QED

Theorem cap_at_return_owned:
  ptr_source_ownership sop_initial cap_source
    ((((([cap_entry;cap_after_alloc;cap_after_nop;cap_at_call] ++ [cap_in_callee]) ++
      [EL 0 cap_callee_suffix]) ++ [EL 1 cap_callee_suffix]) ++
      [EL 2 cap_callee_suffix]) ++ [EL 3 cap_callee_suffix])
    (EL 3 cap_callee_suffix) [4;0]
    (FEMPTY |+ (0,cap_caller) |+ (4,sop_callee)) cap_birth_return1
    [SOME (0,1)] cap_owned_b [([],cap_owned_a)]
Proof
  assume_tac cap_store1_owned >> assume_tac (cj 4 cap_tagged_callee_steps) >>
  drule (cj 2 ptr_source_ownership_rules) >> simp[] >>
  disch_then (drule_at Any) >>
  simp[concretizePtrActivationChronologyTheory.ptr_activation_tokens_def,
    concretizePtrActivationChronologyTheory.ptr_activation_registry_def,
    cap_callee_stack_views, cap_birth_return1_def, cap_birth_store1_def,
    cap_birth_alloc1_def, cap_birth_param1_def]
QED

Theorem cap_tagged_return:
  ptr_tagged_chrono_step cap_source 4 (EL 3 cap_callee_suffix) cap_second_call
    [SOME (0,1)] cap_owned_b [([],cap_owned_a)] [] cap_owned_a []
Proof
  simp[Once ptr_tagged_chrono_step_cases, cap_callee_suffix_def,
    cap_second_call_def, ptr_observe_def] >>
  qexistsl_tac [`<|iret_values := []; iret_adopt_fmp := NONE|>`,
    `sop_cr`, `sop_s3 with vs_inst_idx := 3`, `0`] >>
  simp[cap_frame_def, sop_frame_def, sop_t3_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_tr``, ``cap_source``]) >>
  simp[FLOOKUP_UPDATE, FUPDATE_EQ, fmap_eq_flookup, FLOOKUP_DRESTRICT]
QED

Definition cap_birth_second_call_def:
  cap_birth_second_call = ptr_birth_overlay 0 cap_second_call.po_state.vs_allocas cap_birth_return1
End

Theorem cap_second_call_owned:
  ptr_source_ownership sop_initial cap_source
    ([cap_entry;cap_after_alloc;cap_after_nop;cap_at_call;cap_in_callee] ++
      cap_callee_suffix ++ [cap_second_call]) cap_second_call [0]
    (FEMPTY |+ (0,cap_caller) |+ (4,sop_callee)) cap_birth_second_call
    [] cap_owned_a []
Proof
  assume_tac cap_at_return_owned >> assume_tac cap_tagged_return >>
  drule (cj 2 ptr_source_ownership_rules) >> simp[] >>
  disch_then (drule_at Any) >>
  simp[concretizePtrActivationChronologyTheory.ptr_activation_tokens_def,
    concretizePtrActivationChronologyTheory.ptr_activation_registry_def,
    cap_callee_stack_views, cap_second_call_def, ptr_observe_def,
    cap_birth_second_call_def, cap_callee_suffix_def]
QED

Theorem cap_tagged_second_entry:
  ptr_tagged_chrono_step cap_source 0 cap_second_call cap_in_callee2
    [] cap_owned_a [] [SOME (0,1)] FEMPTY [([],cap_owned_a)]
Proof
  simp[Once ptr_tagged_chrono_step_cases, cap_second_call_def, cap_in_callee2_def,
    cap_frame2_def, ptr_observe_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_t3``]) >>
  simp[FLOOKUP_UPDATE, FUPDATE_EQ, pred_setTheory.SUBSET_DEF,
    eval_phis_def, phi_prefix_length_def, eval_operands_def,
    eval_operand_def, lookup_var_def, op_prov_def]
QED

Definition cap_birth_entry2_def:
  cap_birth_entry2 = ptr_birth_overlay 10 cap_in_callee2.po_state.vs_allocas cap_birth_second_call
End

Theorem cap_second_entry_owned:
  ptr_source_ownership sop_initial cap_source cap_source_prefix cap_in_callee2
    [10;0] (FEMPTY |+ (0,cap_caller) |+ (4,sop_callee) |+ (10,sop_callee))
    cap_birth_entry2 [SOME (0,1)] FEMPTY [([],cap_owned_a)]
Proof
  assume_tac cap_second_call_owned >> assume_tac cap_tagged_second_entry >>
  drule (cj 2 ptr_source_ownership_rules) >> simp[] >>
  disch_then (drule_at Any) >>
  simp[concretizePtrActivationChronologyTheory.ptr_activation_tokens_def,
    concretizePtrActivationChronologyTheory.ptr_activation_registry_def,
    cap_second_call_def, cap_in_callee2_def, ptr_observe_def,
    cap_birth_entry2_def, cap_source_prefix_def, cap_callee_suffix_def]
QED

Definition cap_owned_b2_def:
  cap_owned_b2 = cap_owned_p |+ ("b",(10n,101n))
End

Theorem cap_tagged_second_param:
  ptr_tagged_chrono_step cap_source 10 cap_in_callee2 cap_param2
    [SOME (0,1)] FEMPTY [([],cap_owned_a)]
    [SOME (0,1)] cap_owned_p [([],cap_owned_a)]
Proof
  simp[Once ptr_tagged_chrono_step_cases, cap_in_callee2_def, cap_param2_def,
    ptr_observe_def] >>
  disj1_tac >> qexistsl_tac [`sop_cp2 with vs_inst_idx := 0`,`0`] >>
  simp[sop_second_param_origins, GSYM sop_tp2_def, sop_cs2_projections,
    sop_cp2_def, update_var_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_t3``, ``cap_source``, ``sop_cs2``]) >>
  simp[FLOOKUP_UPDATE, FUPDATE_EQ, sop_cs2_projections]
QED

Theorem cap_tagged_second_alloc:
  ptr_tagged_chrono_step cap_source 10 cap_param2 cap_alloc2
    [SOME (0,1)] cap_owned_p [([],cap_owned_a)]
    [SOME (0,1)] cap_owned_b2 [([],cap_owned_a)]
Proof
  simp[Once ptr_tagged_chrono_step_cases, cap_param2_def, cap_alloc2_def,
    ptr_observe_def] >>
  disj1_tac >> qexistsl_tac [`sop_cb2 with vs_inst_idx := 1`,`0`] >>
  simp[sop_second_alloca_origins, GSYM sop_tb2_def, sop_cp2_projections,
    sop_cb2_projections] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_tp2``, ``cap_source``, ``sop_cp2``, ``sop_cb2``]) >>
  simp[FLOOKUP_UPDATE, FUPDATE_EQ, sop_cp2_projections, sop_cb2_projections,
    sop_cb2_def, update_var_def, venom_state_component_equality]
QED

Definition cap_birth_param2_def:
  cap_birth_param2 = ptr_birth_overlay 10 cap_param2.po_state.vs_allocas cap_birth_entry2
End
Definition cap_birth_alloc2_def:
  cap_birth_alloc2 = ptr_birth_overlay 10 cap_alloc2.po_state.vs_allocas cap_birth_param2
End

Theorem cap_param2_owned:
  ptr_source_ownership sop_initial cap_source (cap_source_prefix ++ [cap_param2]) cap_param2
    [10;0] (FEMPTY |+ (0,cap_caller) |+ (4,sop_callee) |+ (10,sop_callee))
    cap_birth_param2 [SOME (0,1)] cap_owned_p [([],cap_owned_a)]
Proof
  assume_tac cap_second_entry_owned >> assume_tac cap_tagged_second_param >>
  drule (cj 2 ptr_source_ownership_rules) >> simp[] >>
  disch_then (drule_at Any) >>
  simp[concretizePtrActivationChronologyTheory.ptr_activation_tokens_def,
    concretizePtrActivationChronologyTheory.ptr_activation_registry_def,
    cap_in_callee2_def, cap_param2_def, ptr_observe_def, cap_birth_param2_def]
QED

Theorem cap_alloc2_owned:
  ptr_source_ownership sop_initial cap_source
    ((cap_source_prefix ++ [cap_param2]) ++ [cap_alloc2]) cap_alloc2
    [10;0] (FEMPTY |+ (0,cap_caller) |+ (4,sop_callee) |+ (10,sop_callee))
    cap_birth_alloc2 [SOME (0,1)] cap_owned_b2 [([],cap_owned_a)]
Proof
  assume_tac cap_param2_owned >> assume_tac cap_tagged_second_alloc >>
  drule (cj 2 ptr_source_ownership_rules) >> simp[] >>
  disch_then (drule_at Any) >>
  simp[concretizePtrActivationChronologyTheory.ptr_activation_tokens_def,
    concretizePtrActivationChronologyTheory.ptr_activation_registry_def,
    cap_param2_def, cap_alloc2_def, ptr_observe_def, cap_birth_alloc2_def]
QED

Theorem cap_original_owner_lookups:
  FLOOKUP cap_owned_b "p" = SOME (0,1) /\
  FLOOKUP cap_owned_b "b" = SOME (4,101) /\
  FLOOKUP cap_owned_b2 "p" = SOME (0,1) /\
  FLOOKUP cap_owned_b2 "b" = SOME (10,101) /\
  FLOOKUP (FEMPTY |+ (0n,cap_caller) |+ (4,sop_callee) |+ (10,sop_callee)) 0 = SOME cap_caller /\
  FLOOKUP (FEMPTY |+ (0n,cap_caller) |+ (4,sop_callee) |+ (10,sop_callee)) 4 = SOME sop_callee /\
  FLOOKUP (FEMPTY |+ (0n,cap_caller) |+ (4,sop_callee) |+ (10,sop_callee)) 10 = SOME sop_callee /\
  4n <> 10
Proof
  EVAL_TAC
QED

Theorem cap_retained_birth_lookups:
  FLOOKUP cap_birth_alloc2 (0,1) = SOME (256,32) /\
  FLOOKUP cap_birth_alloc2 (4,101) = SOME (288,32) /\
  FLOOKUP cap_birth_alloc2 (10,101) = SOME (288,32)
Proof
  `FLOOKUP (EL 3 cap_callee_suffix).po_state.vs_allocas 101 = SOME (288,32)` by
    simp[cap_callee_suffix_def, ptr_observe_def, sop_cr_def, mstore_def,
      sop_first_origin_lookups] >>
  rpt conj_tac >>
  simp[cap_birth_alloc2_def, cap_birth_param2_def, cap_birth_entry2_def,
    ptr_birth_overlay_lookup, cap_alloc2_def, cap_param2_def, cap_in_callee2_def,
    ptr_observe_def, sop_cb2_def, sop_cp2_def, sop_cs2_projections,
    update_var_def, FLOOKUP_UPDATE] >>
  simp[cap_birth_second_call_def, ptr_birth_overlay_lookup, cap_second_call_def,
    ptr_observe_def, sop_s3_def, merge_callee_state_def, sop_s2_def,
    sop_s1_def, mstore_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[cap_birth_return1_def, ptr_birth_overlay_lookup] >>
  simp[cap_birth_entry1_def, cap_birth_call_def, cap_birth_nop_def,
    ptr_birth_overlay_lookup, cap_in_callee_def, cap_at_call_def,
    cap_after_nop_def, cap_after_alloc_def, ptr_observe_def, sop_cs_def,
    setup_callee_def, sop_s2_def, sop_s1_def, mstore_def, update_var_def,
    cap_birth_a_def, FLOOKUP_UPDATE] >> EVAL_TAC
QED

Theorem cap_original_owner_target_positions:
  MEM (Allocation 1,32,32) cap_caller_out.fn_mems_used /\
  MEM (Allocation 101,0,32) sop_leaf_out.fn_mems_used /\
  ~MEM (Allocation 1,32,32) sop_leaf_out.fn_mems_used
Proof
  EVAL_TAC
QED

Theorem cap_selected_scalar_contents:
  mload 256 sop_s3 = 7w /\ mload 288 sop_cr = 9w /\
  mload 32 cap_target_second_call.po_state = 7w /\
  mload 0 cap_target_second_call.po_state = 9w
Proof
  conj_tac
  >- (`mload 256 (mstore 288 9w (mstore 256 7w sop_cb)) = 7w`
        suffices_by simp_tac (srw_ss()) [LET_THM, sop_s3_def, merge_callee_state_def, sop_cr_def,
          sop_cw_def, mload_def, mstore_def] >>
      simp[mload_mstore_disjoint_proof, mload_mstore_same_proof,
        venomMemDefsTheory.regions_disjoint_def]) >>
  conj_tac
  >- (`mload 288 (mstore 288 9w sop_cw) = 9w`
        suffices_by simp_tac (srw_ss()) [LET_THM, sop_cr_def, mload_def] >>
      simp[mload_mstore_same_proof]) >>
  conj_tac
  >- (`mload 32 (mstore 0 9w (mstore 32 7w
        (update_var "b" 0w (update_var "p" 32w cap_tcs)))) = 7w`
        suffices_by simp_tac (srw_ss()) [LET_THM, cap_target_second_call_def, cap_target_return_view,
          ptr_observe_def, merge_callee_state_def, cap_tcr_def, mload_def] >>
      simp[mload_mstore_disjoint_proof, mload_mstore_same_proof,
        venomMemDefsTheory.regions_disjoint_def]) >>
  `mload 0 (mstore 0 9w (mstore 32 7w
      (update_var "b" 0w (update_var "p" 32w cap_tcs)))) = 9w`
    suffices_by simp_tac (srw_ss()) [LET_THM, cap_target_second_call_def, cap_target_return_view,
      ptr_observe_def, merge_callee_state_def, cap_tcr_def, mload_def] >>
  simp[mload_mstore_same_proof]
QED

Definition cap_embedding_def:
  cap_embedding n = if n = 0 then 0 else SUC n
End

Theorem cap_embedding_increasing:
  !i j. i < j ==> cap_embedding i < cap_embedding j
Proof
  simp[cap_embedding_def] >> rpt strip_tac >> rpt IF_CASES_TAC >> gvs[]
QED

Theorem cap_source_event_ids:
  MAP (\a. a.po_inst.inst_id) ((cap_source_prefix ++ [cap_param2]) ++ [cap_alloc2]) =
    [1;7;2;3;100;101;102;103;104;4;100;101;102]
Proof
  simp[cap_source_prefix_def, cap_entry_def, cap_after_alloc_def,
    cap_after_nop_def, cap_at_call_def, cap_in_callee_def, cap_callee_suffix_def,
    cap_second_call_def, cap_in_callee2_def, cap_param2_def, cap_alloc2_def,
    ptr_observe_def] >> EVAL_TAC
QED

Theorem cap_target_event_ids:
  MAP (\a. a.po_inst.inst_id) cap_target_prefix =
    [1;2;3;100;101;102;103;104;4;100;101;102]
Proof
  `MAP (\a. a.po_inst.inst_id) cap_target_to_call = [2;3]` by
    (EVAL_TAC >> simp[]) >>
  `MAP (\a. a.po_inst.inst_id) cap_target_callee_tail = [101;102;103;104]` by
    (simp[cap_target_callee_tail_def, cap_tcallee_def, cap_tcs_def,
       cap_target_call_view, ptr_observe_def] >>
     CONV_TAC (computeLib.RESTR_EVAL_CONV [``cap_tframe``]) >> simp[]) >>
  `MAP (\a. a.po_inst.inst_id) cap_target_reuse_tail = [101;102]` by
    (simp[cap_target_reuse_tail_def, cap_tcallee2_def, cap_tcs2_def,
       cap_target_second_call_def, cap_target_return_view, cap_target_call_view,
       cap_tcr_def, cap_tcs_def, ptr_observe_def] >>
     CONV_TAC (computeLib.RESTR_EVAL_CONV [``cap_tframe2``]) >> simp[]) >>
  simp[cap_target_prefix_def, cap_target_entry_def, cap_tcallee_def,
    cap_target_second_call_def, cap_tcallee2_def, ptr_observe_def] >> EVAL_TAC
QED

(* Each row is a pre-instruction observation, not a completed write.
   Target j   Source e(j)  inst   active source token / boundary
      0           0         1    0: root allocation / target ASSIGN
      -           1         7    0: deleted NOP (source-only gap)
      1           2         2    0: root initializing store
      2           3         3    0: first INVOKE
      3           4       100    4: first entry / imported PARAM (0,1)
      4           5       101    4: first local allocation (4,101)
      5           6       102    4: write through imported owner (0,1)
      6           7       103    4: write through local owner (4,101)
      7           8       104    4: first return
      8           9         4    0: restored caller / second INVOKE
      9          10       100   10: second entry / imported PARAM (0,1)
     10          11       101   10: reused raw base, new owner (10,101)
     11          12       102   10: next imported write (not yet executed)
   Thus the first imported writer's post-state is source 7 / target 6;
   the local writer's post-state is source 8 / target 7. Birth lookup
   retention is not a claim that the completed activation remains live. *)
Theorem cap_actual_event_correspondence:
  MAP (\j. (EL j cap_target_prefix).po_inst.inst_id) (COUNT_LIST 12) =
  MAP (\j. (EL (cap_embedding j)
    ((cap_source_prefix ++ [cap_param2]) ++ [cap_alloc2])).po_inst.inst_id)
    (COUNT_LIST 12)
Proof
  `LENGTH cap_target_prefix = 12` by
    (mp_tac cap_target_event_ids >>
     disch_then (mp_tac o AP_TERM ``LENGTH : num list -> num``) >> simp[]) >>
  `LENGTH ((cap_source_prefix ++ [cap_param2]) ++ [cap_alloc2]) = 13` by
    (mp_tac cap_source_event_ids >>
     disch_then (mp_tac o AP_TERM ``LENGTH : num list -> num``) >> simp[]) >>
  `MAP (\j. EL j (MAP (\a. a.po_inst.inst_id) cap_target_prefix)) (COUNT_LIST 12) =
   MAP (\j. EL (cap_embedding j) (MAP (\a. a.po_inst.inst_id)
     ((cap_source_prefix ++ [cap_param2]) ++ [cap_alloc2]))) (COUNT_LIST 12)`
    suffices_by
      (CONV_TAC (computeLib.RESTR_EVAL_CONV
        [``cap_target_prefix``, ``cap_source_prefix``, ``cap_param2``, ``cap_alloc2``]) >>
       simp[EL_MAP, Excl "MAP_APPEND"] >>
       Cases_on `cap_target_prefix` >> Cases_on `cap_source_prefix` >> gvs[]) >>
  rewrite_tac[cap_target_event_ids, cap_source_event_ids] >> EVAL_TAC
QED

Theorem cap_entry_correspondence_table:
  MAP (\j. (j,cap_embedding j)) [0;3;9] = [(0,0);(3,4);(9,10)] /\
  MAP (\j. (j,cap_embedding j)) [5;6;7;8;10;11] =
    [(5,6);(6,7);(7,8);(8,9);(10,11);(11,12)]
Proof
  EVAL_TAC
QED

Theorem cap_target_activation_observations:
  EL 0 cap_target_prefix = cap_target_entry /\
  EL 3 cap_target_prefix = cap_tcallee /\
  EL 7 cap_target_prefix = cap_tr /\
  EL 8 cap_target_prefix = cap_target_second_call /\
  EL 9 cap_target_prefix = cap_tcallee2
Proof
  `LENGTH cap_target_to_call = 2` by (EVAL_TAC >> simp[]) >>
  `LENGTH cap_target_callee_tail = 4` by
    (simp[cap_target_callee_tail_def, cap_tcallee_def, cap_tcs_def,
       cap_target_call_view, ptr_observe_def] >>
     CONV_TAC (computeLib.RESTR_EVAL_CONV [``cap_tframe``]) >> simp[]) >>
  simp[cap_target_prefix_def, EL_APPEND_EQN, cap_tr_def,
    LAST_EL, cap_target_tail_nonempty]
QED

(* The registry is SourceOwnership's token-to-source-function map.
   Target entry indices are correspondence data, never fresh owner tokens.
   Both activations consult the same callee layout, whereas the imported
   pointer continues to consult the root's metadata. *)
Theorem cap_owner_entry_placement:
  (EL 0 cap_target_prefix).po_fn = cap_caller_out /\
  (EL 3 cap_target_prefix).po_fn = sop_leaf_out /\
  (EL 9 cap_target_prefix).po_fn = sop_leaf_out /\
  MEM (Allocation (SND (THE (FLOOKUP cap_owned_b2 "p"))),32,32)
    (EL 0 cap_target_prefix).po_fn.fn_mems_used /\
  MEM (Allocation (SND (THE (FLOOKUP cap_owned_b "b"))),0,32)
    (EL 3 cap_target_prefix).po_fn.fn_mems_used /\
  MEM (Allocation (SND (THE (FLOOKUP cap_owned_b2 "b"))),0,32)
    (EL 9 cap_target_prefix).po_fn.fn_mems_used
Proof
  simp[cap_target_activation_observations, cap_target_entry_def,
    cap_tcallee_def, cap_tcallee2_def, ptr_observe_def,
    cap_original_owner_lookups, cap_original_owner_target_positions]
QED
