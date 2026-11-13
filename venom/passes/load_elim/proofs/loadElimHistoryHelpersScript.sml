Theory loadElimHistoryHelpers
Ancestors
  venomState list pred_set arithmetic finite_map

(* An event records its finite write footprint and its post-state. The
   incoming state is supplied separately, so adjacent events share endpoints. *)
Definition le_framed_history_def:
  (le_framed_history s [] <=> T) /\
  (le_framed_history s ((outs,t)::h) <=>
    FINITE outs /\ (!v. v NOTIN outs ==> lookup_var v t = lookup_var v s) /\
    le_framed_history t h)
End

Definition le_history_end_def:
  le_history_end s [] = s /\
  le_history_end s ((outs,t)::h) = le_history_end t h
End

Definition le_epoch_def:
  le_epoch h v = LENGTH (FILTER (\e. v IN FST e) h)
End

Theorem le_history_end_append:
  le_history_end s (a ++ b) = le_history_end (le_history_end s a) b
Proof
  qid_spec_tac `s` >> Induct_on `a` >> simp[le_history_end_def] >>
  Cases_on `h` >> simp[le_history_end_def]
QED

Theorem le_framed_history_append:
  le_framed_history s (a ++ b) <=>
  le_framed_history s a /\ le_framed_history (le_history_end s a) b
Proof
  qid_spec_tac `s` >> Induct_on `a` >> simp[le_framed_history_def, le_history_end_def] >>
  Cases_on `h` >> simp[le_framed_history_def, le_history_end_def] >> metis_tac[]
QED

Theorem le_epoch_append[simp]:
  le_epoch (a ++ b) v = le_epoch a v + le_epoch b v
Proof
  simp[le_epoch_def, FILTER_APPEND_DISTRIB]
QED

Theorem le_epoch_mono:
  le_epoch a v <= le_epoch (a ++ b) v
Proof
  simp[]
QED

Theorem le_epoch_zero:
  le_epoch h v = 0 <=> EVERY (\e. v NOTIN FST e) h
Proof
  Induct_on `h` >> simp[le_epoch_def] >>
  gen_tac >> rename1 `FST e` >> Cases_on `v IN FST e` >> gvs[le_epoch_def]
QED

Theorem le_history_lookup_persistence:
  !h s v. le_framed_history s h /\ le_epoch h v = 0 ==>
    lookup_var v (le_history_end s h) = lookup_var v s
Proof
  Induct_on `h` >- simp[le_history_end_def] >>
  Cases >> simp[le_framed_history_def, le_history_end_def, le_epoch_zero] >>
  rpt strip_tac >> metis_tac[le_epoch_zero]
QED

(* A prefix/interval decomposition avoids partial EL/state_at operations at
   empty histories or at the endpoint LENGTH h. *)
Theorem le_history_interval_lookup:
  le_framed_history s (prefix ++ interval ++ suffix) /\
  le_epoch prefix v = le_epoch (prefix ++ interval) v ==>
  lookup_var v (le_history_end s (prefix ++ interval)) =
  lookup_var v (le_history_end s prefix)
Proof
  simp[le_framed_history_append, le_history_end_append] >>
  rpt strip_tac >> irule le_history_lookup_persistence >> simp[]
QED

Theorem le_history_interval_operand:
  le_framed_history s (prefix ++ interval ++ suffix) /\
  (!v. op = Var v ==>
    le_epoch prefix v = le_epoch (prefix ++ interval) v) /\
  (le_history_end s prefix).vs_labels =
    (le_history_end s (prefix ++ interval)).vs_labels ==>
  eval_operand op (le_history_end s (prefix ++ interval)) =
    eval_operand op (le_history_end s prefix)
Proof
  strip_tac >> Cases_on `op` >> simp[eval_operand_def] >>
  irule le_history_interval_lookup >> metis_tac[]
QED

(* Every read sees s, including reads whose source is another batch output.
   Writes unwind in list order, so the first occurrence wins on duplicates,
   exactly as for the operational PHI prefix. *)
Definition le_snapshot_batch_def:
  le_snapshot_batch read s [] = SOME s /\
  le_snapshot_batch read s (x::xs) =
    case read s x of
      NONE => NONE
    | SOME (out,value) =>
        case le_snapshot_batch read s xs of
          NONE => NONE
        | SOME t => SOME (update_var out value t)
End

Theorem le_snapshot_batch_frame:
  !xs s t.
    le_snapshot_batch read s xs = SOME t /\
    (!x value. MEM x xs ==> read s x <> SOME (v,value)) ==>
    lookup_var v t = lookup_var v s
Proof
  Induct_on `xs` >- simp[le_snapshot_batch_def] >>
  simp[le_snapshot_batch_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `out <> v` by metis_tac[] >> simp[] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem le_snapshot_batch_reads:
  !xs s t x. le_snapshot_batch read s xs = SOME t /\ MEM x xs ==>
    ?out value. read s x = SOME (out,value)
Proof
  Induct_on `xs` >> simp[le_snapshot_batch_def, AllCaseEqs()] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem le_snapshot_batch_selected:
  !prefix s t.
    le_snapshot_batch read s (prefix ++ x::suffix) = SOME t /\
    read s x = SOME (v,value) /\
    (!y w. MEM y prefix ==> read s y <> SOME (v,w)) ==>
    lookup_var v t = SOME value
Proof
  Induct_on `prefix`
  >- (rpt strip_tac >>
      gvs[le_snapshot_batch_def, AllCaseEqs(), lookup_var_def,
          update_var_def, FLOOKUP_UPDATE]) >>
  simp[le_snapshot_batch_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `out <> v` by metis_tac[] >> simp[] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem le_snapshot_batch_event:
  le_snapshot_batch read s xs = SOME t /\ FINITE outs /\
  (!x out value. MEM x xs /\ read s x = SOME (out,value) ==> out IN outs) ==>
  le_framed_history s [(outs,t)]
Proof
  simp[le_framed_history_def] >> rpt strip_tac >>
  irule le_snapshot_batch_frame >> metis_tac[]
QED
