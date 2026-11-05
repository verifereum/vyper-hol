(* Dynamic clocks and snapshots only; no compiler coherence or availability claim. *)
Theory makeSsaCurrentDynamicStores
Ancestors makeSsaCurrentSymbolicInterface makeSsaCurrentTokens list arithmetic

Definition current_origin_bounded_def:
  current_origin_bounded n X <=>
    !v m k. X v = SOME (CurrentOccurrence m k) ==> m < n
End

Definition current_origin_initial_def:
  current_origin_initial v = SOME (CurrentInitial v)
End

Definition current_token_initial_def:
  current_token_initial t =
    case t of CurrentDefault v => current_origin_initial v | _ => NONE
End

(* First binding wins, including a binding to NONE. All RHSs are snapshots. *)
Definition current_origin_snapshot_def:
  (current_origin_snapshot X [] v = X v) /\
  (current_origin_snapshot X ((w,s)::bs) v =
    if v = w then s else current_origin_snapshot X bs v)
End

Definition current_occurrence_bindings_def:
  (current_occurrence_bindings n k [] = []) /\
  (current_occurrence_bindings n k (v::vs) =
    (v,SOME (CurrentOccurrence n k))::current_occurrence_bindings n (SUC k) vs)
End

Definition current_origin_write_def:
  current_origin_write X n outputs =
    current_origin_snapshot X (current_occurrence_bindings n 0 outputs)
End

Definition current_origin_operand_def:
  current_origin_operand X op =
    case op of Var v => X v | _ => SOME (CurrentConstant op)
End

Definition current_origin_selected_def:
  current_origin_selected X p inst =
    case resolve_phi p inst.inst_operands of
      NONE => NONE | SOME op => current_origin_operand X op
End

Definition current_origin_phi_bindings_def:
  current_origin_phi_bindings key X p phis =
    MAP (\j. (key (HD j.inst_outputs), current_origin_selected X p j)) phis
End

Definition current_origin_batch_def:
  current_origin_batch X p phis =
    current_origin_snapshot X (current_origin_phi_bindings (\v. v) X p phis)
End

(* ks reads the source snapshot M, never the target-name store N. *)
Definition current_token_batch_def:
  current_token_batch ks key M p phis =
    current_origin_snapshot ks (current_origin_phi_bindings key M p phis)
End

Theorem current_origin_initial_bounded:
  current_origin_bounded 0 current_origin_initial /\
  current_origin_bounded 0 current_token_initial
Proof
  simp[current_origin_bounded_def, current_origin_initial_def] >>
  Cases >> simp[current_token_initial_def, current_origin_initial_def]
QED

Theorem current_token_initial_lookup:
  current_token_initial (CurrentDefault v) = current_origin_initial v /\
  current_token_initial (CurrentOriginal l i k) = NONE /\
  current_token_initial (CurrentInserted l v) = NONE
Proof
  simp[current_token_initial_def]
QED

Theorem current_origin_bounded_mono:
  current_origin_bounded n X /\ n <= q ==> current_origin_bounded q X
Proof
  rw[current_origin_bounded_def] >> res_tac >> decide_tac
QED

Theorem current_origin_snapshot_bounded:
  !bs X. current_origin_bounded n X /\
    EVERY (\b. !m k. SND b = SOME (CurrentOccurrence m k) ==> m < n) bs ==>
    current_origin_bounded n (current_origin_snapshot X bs)
Proof
  Induct >- simp[current_origin_bounded_def, current_origin_snapshot_def] >>
  gen_tac >> PairCases_on `h` >>
  rw[current_origin_snapshot_def, current_origin_bounded_def] >>
  gvs[AllCaseEqs()] >> metis_tac[current_origin_bounded_def]
QED

Theorem current_occurrence_bindings_bounded:
  !outputs k. EVERY
    (\b. !m j. SND b = SOME (CurrentOccurrence m j) ==> m < SUC n)
    (current_occurrence_bindings n k outputs)
Proof
  Induct >> simp[current_occurrence_bindings_def]
QED

Theorem current_origin_write_bounded:
  current_origin_bounded n X ==>
  current_origin_bounded (SUC n) (current_origin_write X n outputs)
Proof
  strip_tac >> simp[current_origin_write_def] >>
  irule current_origin_snapshot_bounded >>
  simp[current_occurrence_bindings_bounded] >>
  irule current_origin_bounded_mono >> qexists `n` >> simp[]
QED

Theorem current_origin_operand_bounded:
  current_origin_bounded n X /\
  current_origin_operand X op = SOME (CurrentOccurrence m k) ==> m < n
Proof
  Cases_on `op` >> simp[current_origin_operand_def, current_origin_bounded_def] >> metis_tac[]
QED

Theorem current_origin_selected_bounded:
  current_origin_bounded n X /\
  current_origin_selected X p inst = SOME (CurrentOccurrence m k) ==> m < n
Proof
  simp[current_origin_selected_def, AllCaseEqs()] >>
  metis_tac[current_origin_operand_bounded]
QED

Theorem current_origin_phi_bindings_bounded:
  !phis. current_origin_bounded n X ==>
  EVERY (\b. !m k. SND b = SOME (CurrentOccurrence m k) ==> m < n)
    (current_origin_phi_bindings key X p phis)
Proof
  Induct >> gvs[current_origin_phi_bindings_def] >>
  metis_tac[current_origin_selected_bounded]
QED

Theorem current_origin_batch_bounded:
  current_origin_bounded n X ==> current_origin_bounded n (current_origin_batch X p phis)
Proof
  simp[current_origin_batch_def] >> strip_tac >>
  irule current_origin_snapshot_bounded >> simp[current_origin_phi_bindings_bounded]
QED

Theorem current_token_batch_bounded:
  current_origin_bounded n ks /\ current_origin_bounded n M ==>
  current_origin_bounded n (current_token_batch ks key M p phis)
Proof
  simp[current_token_batch_def] >> strip_tac >>
  irule current_origin_snapshot_bounded >> simp[current_origin_phi_bindings_bounded]
QED

Theorem current_origin_incoming_fresh:
  current_origin_bounded n X ==> X v <> SOME (CurrentOccurrence n k)
Proof
  rw[current_origin_bounded_def] >>
  spose_not_then assume_tac >> first_x_assum drule >> simp[]
QED

Theorem current_origin_distinct_visits:
  n <> m ==> SOME (CurrentOccurrence n k) <> SOME (CurrentOccurrence m k)
Proof
  simp[]
QED

Theorem current_origin_snapshot_lookup:
  !bs X v s. ALOOKUP bs v = SOME s ==>
    current_origin_snapshot X bs v = s
Proof
  Induct >- simp[] >> gen_tac >> PairCases_on `h` >>
  simp[current_origin_snapshot_def] >> rw[] >> gvs[]
QED

Theorem current_origin_batch_selected:
  ALOOKUP (MAP (\j. (HD j.inst_outputs, resolve_phi p j.inst_operands)) phis) v =
    SOME (SOME rhs) ==>
  current_origin_batch X p phis v = current_origin_operand X rhs
Proof
  qid_spec_tac `phis` >> Induct >- simp[] >>
  simp[current_origin_batch_def, current_origin_phi_bindings_def,
       current_origin_snapshot_def, current_origin_selected_def] >>
  rw[] >> gvs[current_origin_batch_def, current_origin_phi_bindings_def,
              current_origin_selected_def]
QED

Theorem current_origin_batch_missing:
  ALOOKUP (MAP (\j. (HD j.inst_outputs, resolve_phi p j.inst_operands)) phis) v =
    SOME NONE ==> current_origin_batch X p phis v = NONE
Proof
  qid_spec_tac `phis` >> Induct >- simp[] >>
  simp[current_origin_batch_def, current_origin_phi_bindings_def,
       current_origin_snapshot_def, current_origin_selected_def] >>
  rw[] >> gvs[current_origin_batch_def, current_origin_phi_bindings_def,
              current_origin_selected_def]
QED

(* Even if u is another output, this is the old X u, not batch X u. *)
Theorem current_origin_batch_read_snapshot:
  ALOOKUP (MAP (\j. (HD j.inst_outputs, resolve_phi p j.inst_operands)) phis) v =
    SOME (SOME (Var u)) ==>
  current_origin_batch X p phis v = X u
Proof
  strip_tac >> drule current_origin_batch_selected >> simp[current_origin_operand_def]
QED

Definition current_token_copy_def:
  current_token_copy ks edges =
    current_origin_snapshot ks (MAP (\(dst,src). (dst,ks src)) edges)
End

Theorem current_token_copy_bounded:
  current_origin_bounded n ks ==> current_origin_bounded n (current_token_copy ks edges)
Proof
  strip_tac >> simp[current_token_copy_def] >>
  irule current_origin_snapshot_bounded >> simp[] >>
  qid_spec_tac `edges` >> Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  simp[] >> metis_tac[current_origin_bounded_def]
QED

(* Three independent stores, one clock advanced only by paired original writes.
   These rules deliberately assert no agreement and no runtime definedness. *)
Inductive current_dynamic_replay:
  current_dynamic_replay 0 current_origin_initial current_origin_initial current_token_initial /\
  (!n ms ns ks outs names tokens.
    current_dynamic_replay n ms ns ks ==>
    current_dynamic_replay (SUC n)
      (current_origin_write ms n outs)
      (current_origin_write ns n names)
      (current_origin_write ks n tokens)) /\
  (!n ms ns ks p phis renamed key.
    current_dynamic_replay n ms ns ks ==>
    current_dynamic_replay n
      (current_origin_batch ms p phis)
      (current_origin_batch ns p renamed)
      (current_token_batch ks key ms p phis)) /\
  (!n ms ns ks edges.
    current_dynamic_replay n ms ns ks ==>
    current_dynamic_replay n ms ns (current_token_copy ks edges))
End

Theorem current_dynamic_replay_bounded:
  !n ms ns ks. current_dynamic_replay n ms ns ks ==>
    current_origin_bounded n ms /\ current_origin_bounded n ns /\
    current_origin_bounded n ks
Proof
  ho_match_mp_tac current_dynamic_replay_ind >>
  simp[current_origin_initial_bounded] >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  simp[current_origin_write_bounded, current_origin_batch_bounded,
       current_token_batch_bounded, current_token_copy_bounded]
QED

Theorem current_origin_write_first:
  current_origin_write X n (v::vs) v = SOME (CurrentOccurrence n 0)
Proof
  simp[current_origin_write_def, current_occurrence_bindings_def,
       current_origin_snapshot_def]
QED

Theorem current_origin_repeated_write:
  n <> m ==>
  current_origin_write (current_origin_write X n (v::vs)) m (v::vs) v <>
    current_origin_write X n (v::vs) v
Proof
  simp[current_origin_write_first]
QED

Theorem current_dynamic_replay_fresh:
  current_dynamic_replay n ms ns ks ==>
  ms v <> SOME (CurrentOccurrence n k) /\
  ns w <> SOME (CurrentOccurrence n k) /\
  ks t <> SOME (CurrentOccurrence n k)
Proof
  strip_tac >> drule current_dynamic_replay_bounded >>
  metis_tac[current_origin_incoming_fresh]
QED
