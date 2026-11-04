Theory dftOccurrenceSquare
Ancestors
  dftOccurrenceReplay dftScheduleOrder arithmetic

(* Bounded certificates, not a global schedule simulation relation. *)
Datatype:
  dft_square_pos = SqBefore | SqMiddle | SqAfter
End

Datatype:
  dft_occ_square = <| sq_l0 : dft_occ_config;
                      sq_l1 : dft_occ_config;
                      sq_l2 : dft_occ_config;
                      sq_r0 : dft_occ_config;
                      sq_r1 : dft_occ_config;
                      sq_r2 : dft_occ_config |>
End

Definition dft_square_pick_def:
  (dft_square_pick SqBefore a b c = a) /\
  (dft_square_pick SqMiddle a b c = b) /\
  (dft_square_pick SqAfter a b c = c)
End

Definition dft_square_depth_def:
  (dft_square_depth SqBefore = (0:num)) /\
  (dft_square_depth SqMiddle = 1) /\
  (dft_square_depth SqAfter = 2)
End

Definition dft_occ_at_join_def:
  dft_occ_at_join l r <=>
    l.dft_occ_path = r.dft_occ_path /\
    l.dft_occ_visit = r.dft_occ_visit /\
    l.dft_occ_saved = r.dft_occ_saved /\
    ?fn fn' bb bb' s stack n.
      l.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
      r.dft_occ_core = DftOpen (DftAt fn' 0 bb' s) stack n
End

Definition dft_occ_square_ok_def:
  dft_occ_square_ok w C C' q <=>
    dft_occ_oracle_next w C q.sq_l0 = q.sq_l1 /\
    dft_occ_oracle_next w C q.sq_l1 = q.sq_l2 /\
    dft_occ_oracle_next w C' q.sq_r0 = q.sq_r1 /\
    dft_occ_oracle_next w C' q.sq_r1 = q.sq_r2 /\
    dft_occ_at_join q.sq_l2 q.sq_r2
End

Definition dft_occ_square_phase_def:
  dft_occ_square_phase q p p' l r <=>
    l = dft_square_pick p q.sq_l0 q.sq_l1 q.sq_l2 /\
    r = dft_square_pick p' q.sq_r0 q.sq_r1 q.sq_r2
End

Theorem dft_occ_square_left_prefix:
  dft_occ_square_ok w C C' q ==>
  FUNPOW (dft_occ_oracle_next w C) (dft_square_depth p) q.sq_l0 =
  dft_square_pick p q.sq_l0 q.sq_l1 q.sq_l2
Proof
  Cases_on `p` >> simp[dft_occ_square_ok_def, dft_square_depth_def,
                          dft_square_pick_def, FUNPOW_2, FUNPOW]
QED

Theorem dft_occ_square_right_prefix:
  dft_occ_square_ok w C C' q ==>
  FUNPOW (dft_occ_oracle_next w C') (dft_square_depth p) q.sq_r0 =
  dft_square_pick p q.sq_r0 q.sq_r1 q.sq_r2
Proof
  Cases_on `p` >> simp[dft_occ_square_ok_def, dft_square_depth_def,
                          dft_square_pick_def, FUNPOW_2, FUNPOW]
QED

Theorem dft_occ_square_after_join:
  dft_occ_square_ok w C C' q /\
  dft_occ_square_phase q SqAfter SqAfter l r ==> dft_occ_at_join l r
Proof
  simp[dft_occ_square_ok_def, dft_occ_square_phase_def,
       dft_square_pick_def]
QED

Theorem dft_occ_square_phase_pick:
  dft_occ_square_phase q p p'
    (dft_square_pick p q.sq_l0 q.sq_l1 q.sq_l2)
    (dft_square_pick p' q.sq_r0 q.sq_r1 q.sq_r2)
Proof
  simp[dft_occ_square_phase_def]
QED
