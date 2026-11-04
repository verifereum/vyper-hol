(* Algebraic two-sided cuts. Pending writes carry no provenance here. *)
Theory dftOccurrenceResidual
Ancestors
  dftOccurrenceFrame venomExecSemantics venomState venomInst list

Definition dft_pending_apply_def:
  dft_pending_apply us s =
    FOLDL (\u p. update_var (FST p) (SND p) u) s us
End

Definition dft_cut_data_def:
  dft_cut_data s = s with vs_inst_idx := 0
End

Definition dft_cut_pair_def:
  dft_cut_pair us vs s t <=>
    ?base. dft_cut_data s = dft_pending_apply us base /\
           dft_cut_data t = dft_pending_apply vs base
End

Theorem dft_cut_data_pending:
  !us s. dft_cut_data (dft_pending_apply us s) =
    dft_pending_apply us (dft_cut_data s)
Proof
  rewrite_tac[dft_pending_apply_def] >>
  Induct >> simp[] >>
  simp[dft_cut_data_def, update_var_def]
QED

Theorem dft_cut_data_eval_operands:
  eval_operands ops (dft_cut_data s) = eval_operands ops s
Proof
  Induct_on `ops` >> simp[eval_operands_def] >>
  Cases_on `h` >> simp[eval_operand_def, lookup_var_def, dft_cut_data_def]
QED

Theorem dft_cut_data_setup_callee:
  setup_callee fn args (dft_cut_data s) = setup_callee fn args s
Proof
  simp[dft_cut_data_def, setup_callee_def]
QED

Theorem dft_cut_pair_eval_operands:
  dft_cut_pair us vs s t /\
  EVERY (\p. ~MEM (Var (FST p)) ops) us /\
  EVERY (\p. ~MEM (Var (FST p)) ops) vs ==>
  eval_operands ops s = eval_operands ops t
Proof
  strip_tac >>
  gvs[dft_cut_pair_def] >>
  metis_tac[dft_cut_data_eval_operands, dft_eval_operands_fold,
            dft_pending_apply_def]
QED

Theorem dft_cut_pair_setup_callee:
  dft_cut_pair us vs s t ==>
  setup_callee fn args s = setup_callee fn args t
Proof
  simp[dft_cut_pair_def] >> rpt strip_tac >>
  metis_tac[dft_cut_data_setup_callee, dft_setup_callee_fold,
            dft_pending_apply_def]
QED

Theorem dft_cut_pair_refl:
  dft_cut_pair [] [] s s
Proof
  simp[dft_cut_pair_def, dft_pending_apply_def]
QED
