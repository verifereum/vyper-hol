Theory concretizePtrCrossActivationProbe
Ancestors concretizePtrSingletonOriginProbe concretizePtrSourceOwnership
  concretizePtrChronologicalHistory concretizePtrActivationBirths ptrDiscipline
  concretizePtrLedgerAlignment concretizePtrOperationalBytes concretizePtrLedgerProbe
  concretizeStepStructure concretizeStepShape concretizeStepCallChecks
  concretizeStepRetpc concretizeStageShape
  concretizeMemLocDefs venomExecSemantics venomState venomInst
  finite_map list words
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
      CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_t3``, ``cap_source``]) >>
      simp[FLOOKUP_UPDATE, FUPDATE_EQ]) >>
  simp[Once ptr_chrono_step_cases, cap_param2_def, cap_alloc2_def,
    ptr_observe_def] >>
  disj1_tac >> qexistsl_tac [`sop_cb2 with vs_inst_idx := 1`,`0`] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_tp2``, ``cap_source``]) >>
  simp[FLOOKUP_UPDATE, FUPDATE_EQ, pred_setTheory.SUBSET_DEF]
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
