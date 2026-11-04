Theory makeSsaCurrentActualRetention
Ancestors
  makeSsaCurrentOutputNames makeSsaCurrentExitTokens makeSsaCurrentRetention
  makeSsaCurrentFinalSlots makeSsaCurrentAllocation venomWf venomInst list pair

(* Extra predecessor labels are permitted by the frozen input contract.
   This probes the retention proof's proposed witness-to-event step, not
   the semantic correctness of the pass. *)
Definition current_extra_slot_phi_def:
  current_extra_slot_phi = mk_inst 2 PHI
    [Label "E"; Var "a"; Label "Ghost"; Var "b"; Label "Phantom"; Var "c"] ["v"]
End

Definition current_extra_slot_fn_def:
  current_extra_slot_fn = mk_raw_function "extra_slots"
    [<| bb_label := "E"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit 1w] ["a"]; mk_inst 1 JMP [Label "D"] []] |>;
     <| bb_label := "D"; bb_instructions :=
        [current_extra_slot_phi; mk_inst 3 STOP [] []] |>]
End

Theorem current_extra_slot_witness_probe:
  inst_wf current_extra_slot_phi /\
  phi_pairs current_extra_slot_phi.inst_operands =
    [("E","a"); ("Ghost","b"); ("Phantom","c")] /\
  fn_cfg_edge current_extra_slot_fn "E" "D" /\
  ~fn_cfg_edge current_extra_slot_fn "Ghost" "D" /\
  ~fn_cfg_edge current_extra_slot_fn "Phantom" "D"
Proof
  EVAL_TAC >>
  pure_rewrite_tac[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  simp[] >> qexists_tac `EL 0 current_extra_slot_fn.fn_blocks` >> EVAL_TAC
QED

Theorem current_extra_slot_input_probe:
  fn_inst_wf current_extra_slot_fn /\
  fn_phis_non_degenerate current_extra_slot_fn
Proof
  conj_tac >- EVAL_TAC >>
  simp[fn_phis_non_degenerate_def, fn_insts_def, fn_insts_blocks_def,
    current_extra_slot_fn_def, current_extra_slot_phi_def, mk_raw_function_def,
    mk_inst_def] >> rpt strip_tac >> gvs[] >>
  qexistsl_tac [`"E"`, `"a"`, `"Ghost"`, `"b"`] >> EVAL_TAC
QED

(* A source owner's unchanged spelling and allocated spellings form one
   name class. Different source owners have disjoint classes. *)
Definition current_owner_name_def:
  current_owner_name H (v : string) n <=>
    n = v \/ ?t : current_token. MEM (t,v,n) H
End

Theorem current_owner_name_separate:
  current_history_valid V H /\ MEM v V /\ MEM w V /\ v <> w /\
  current_owner_name H v n /\ current_owner_name H w m ==> n <> m
Proof
  rpt strip_tac >>
  gvs[current_owner_name_def, current_history_valid_def, EVERY_MEM,
    FORALL_PROD]
  >- metis_tac[]
  >- metis_tac[] >>
  qpat_x_assum `!a b c. _` kall_tac >>
  qpat_x_assum `MEM v V` kall_tac >>
  qpat_x_assum `MEM w V` kall_tac >>
  fs[MEM_EL] >>
  `EL n H = EL n' H` suffices_by metis_tac[PAIR_EQ] >>
  `n = n'` suffices_by simp[] >>
  `EL n (MAP (SND o SND) H) = EL n' (MAP (SND o SND) H)` by
    (simp[EL_MAP] >> metis_tac[SND]) >>
  metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP]
QED
