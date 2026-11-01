(* Proof-only composition interface for fixed label budgets and reservations. *)
Theory bodyIntCallLabelReservations
Ancestors
  bodyIntCallLabels compileEnv emitHelperProps pred_set list

Definition compiler_label_hoare_def:
  compiler_label_hoare P m Q <=>
  !st r out. P st /\ m st = (r,out) ==> Q r out
End

Definition compiler_label_reservation_def:
  compiler_label_reservation origin pending st <=>
    compile_state_ok st /\ origin.cs_next_label <= st.cs_next_label /\
    bound_labels st SUBSET
      (bound_labels origin UNION compiler_labels_future origin.cs_next_label) /\
    pending SUBSET
      (bound_labels origin UNION compiler_labels_future origin.cs_next_label) /\
    (!lbl. lbl IN pending ==> label_external st lbl)
End

Theorem compiler_label_hoare_bind:
  compiler_label_hoare P m Q /\
  (!x. compiler_label_hoare (Q x) (k x) R) ==>
  compiler_label_hoare P (comp_bind m k) R
Proof
  simp[compiler_label_hoare_def] >> strip_tac >> rpt gen_tac >>
  Cases_on `m st` >> simp[comp_bind_def] >> metis_tac[]
QED

Theorem compiler_label_hoare_return:
  compiler_label_hoare P (comp_return x) (\r st. r = x /\ P st)
Proof
  simp[compiler_label_hoare_def, comp_return_def] >> metis_tac[]
QED

Theorem compiler_label_hoare_consequence:
  compiler_label_hoare P m Q /\ (!st. P' st ==> P st) /\
  (!r st. Q r st ==> Q' r st) ==>
  compiler_label_hoare P' m Q'
Proof
  simp[compiler_label_hoare_def] >> metis_tac[]
QED

Theorem compiler_label_hoare_ignore_bind:
  compiler_label_hoare P m (\x st. Q st) /\
  compiler_label_hoare Q k R ==>
  compiler_label_hoare P (comp_ignore_bind m k) R
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule compiler_label_hoare_bind >>
  qexists_tac `\x st. Q st` >> simp[ETA_THM]
QED

Theorem compiler_label_reservation_init:
  compile_state_ok st ==> compiler_label_reservation st {} st
Proof
  simp[compiler_label_reservation_def, SUBSET_DEF]
QED

Theorem compiler_label_reservation_finish:
  compiler_label_reservation origin {} out ==>
  compile_state_ok out /\ origin.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET
    (bound_labels origin UNION compiler_labels_future origin.cs_next_label)
Proof
  simp[compiler_label_reservation_def]
QED

Theorem compiler_label_bounds_trans:
  st.cs_next_label <= mid.cs_next_label /\
  bound_labels mid SUBSET
    (bound_labels st UNION compiler_labels_future st.cs_next_label) /\
  mid.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET
    (bound_labels mid UNION compiler_labels_future mid.cs_next_label) ==>
  st.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET
    (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  strip_tac >>
  `compiler_labels_future mid.cs_next_label SUBSET
     compiler_labels_future st.cs_next_label` by
    (irule compiler_labels_future_antimono >> simp[]) >>
  conj_tac >- decide_tac >>
  gvs[SUBSET_DEF] >> metis_tac[]
QED

Theorem compiler_label_reservation_transport:
  compiler_label_reservation origin pending st /\
  compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET
    (bound_labels st UNION compiler_labels_future st.cs_next_label) ==>
  compiler_label_reservation origin pending out
Proof
  simp[compiler_label_reservation_def] >> strip_tac >>
  `origin.cs_next_label <= out.cs_next_label /\
   bound_labels out SUBSET
     (bound_labels origin UNION compiler_labels_future origin.cs_next_label)` by
    metis_tac[compiler_label_bounds_trans] >>
  simp[] >> rpt strip_tac >> irule label_external_reserved_transport >>
  qexists_tac `st` >> simp[]
QED

Theorem compiler_label_hoare_preserves_reservation:
  (!st r out. m st = (r,out) /\ compile_state_ok st ==>
    compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
    bound_labels out SUBSET
      (bound_labels st UNION compiler_labels_future st.cs_next_label)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending) m
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[compiler_label_hoare_def] >> rpt strip_tac >>
  `compile_state_ok st` by gvs[compiler_label_reservation_def] >>
  first_x_assum drule_all >> strip_tac >>
  irule compiler_label_reservation_transport >>
  simp[] >> qexists_tac `st` >> simp[]
QED

Theorem compiler_label_hoare_fresh_label:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (fresh_label suffix)
    (\lbl out. lbl NOTIN pending /\
      compiler_label_reservation origin (lbl INSERT pending) out)
Proof
  simp[compiler_label_hoare_def] >> rpt gen_tac >> strip_tac >>
  rename1 `fresh_label suffix st = (lbl,out)` >>
  `compile_state_ok st` by gvs[compiler_label_reservation_def] >>
  drule_all fresh_label_produces_external >> strip_tac >>
  `compiler_label_reservation origin pending out` by
    (irule compiler_label_reservation_transport >> simp[] >>
     qexists_tac `st` >> simp[SUBSET_DEF]) >>
  `lbl NOTIN pending` by
    (gvs[compiler_label_reservation_def, label_external_def] >>
     metis_tac[fresh_label_output_in_future, arithmeticTheory.LESS_EQ_REFL]) >>
  simp[] >>
  gvs[compiler_label_reservation_def, INSERT_SUBSET] >>
  `fresh_label_output suffix st.cs_next_label IN
     compiler_labels_future origin.cs_next_label` by
    simp[fresh_label_output_in_future] >>
  simp[] >> metis_tac[]
QED

Theorem compiler_label_hoare_new_block:
  lbl IN pending ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (new_block lbl)
    (\r out. compiler_label_reservation origin (pending DELETE lbl) out)
Proof
  simp[compiler_label_hoare_def] >> rpt strip_tac >>
  `compile_state_ok st /\ label_external st lbl` by
    gvs[compiler_label_reservation_def] >>
  drule_all compile_state_ok_new_block >> strip_tac >>
  gvs[compiler_label_reservation_def, SUBSET_DEF, label_external_def] >>
  metis_tac[]
QED
