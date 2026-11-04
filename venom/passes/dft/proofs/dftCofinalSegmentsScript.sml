Theory dftCofinalSegments
Ancestors
  arithmetic pair combin

(* Lengths are selected as a pair: endpoints and accounting share a witness. *)
Definition dft_segment_choice_def:
  dft_segment_choice L R P H c d =
    @ab. 0 < FST ab /\ 0 < SND ab /\
      P (FUNPOW L (FST ab) c) (FUNPOW R (SND ab) d) /\
      H (FST ab) (SND ab) c d
End

Theorem dft_segment_choice_spec[local]:
  (!c d. P c d ==> ?a b. 0 < a /\ 0 < b /\
    P (FUNPOW L a c) (FUNPOW R b d) /\ H a b c d) /\ P c d ==>
  0 < FST (dft_segment_choice L R P H c d) /\
  0 < SND (dft_segment_choice L R P H c d) /\
  P (FUNPOW L (FST (dft_segment_choice L R P H c d)) c)
    (FUNPOW R (SND (dft_segment_choice L R P H c d)) d) /\
  H (FST (dft_segment_choice L R P H c d))
    (SND (dft_segment_choice L R P H c d)) c d
Proof
  strip_tac >> simp[dft_segment_choice_def] >> SELECT_ELIM_TAC >>
  conj_tac >- (first_x_assum drule >> strip_tac >> qexists `(a,b)` >> simp[]) >>
  simp[]
QED

Definition dft_segment_cuts_def:
  dft_segment_cuts L R P H c d 0 = (0,0) /\
  dft_segment_cuts L R P H c d (SUC n) =
    let ab = dft_segment_cuts L R P H c d n;
        step = dft_segment_choice L R P H
          (FUNPOW L (FST ab) c) (FUNPOW R (SND ab) d)
    in (FST ab + FST step, SND ab + SND step)
End

Theorem dft_segment_cuts_related[local]:
  P c d /\ (!u v. P u v ==> ?a b. 0 < a /\ 0 < b /\
    P (FUNPOW L a u) (FUNPOW R b v) /\ H a b u v) ==>
  !n. P (FUNPOW L (FST (dft_segment_cuts L R P H c d n)) c)
        (FUNPOW R (SND (dft_segment_cuts L R P H c d n)) d)
Proof
  strip_tac >> Induct >> simp[dft_segment_cuts_def] >>
  drule_all dft_segment_choice_spec >>
  simp[dft_segment_cuts_def, FUNPOW_ADD, ADD_COMM]
QED

Theorem dft_positive_segments:
  P c d /\ (!u v. P u v ==> ?a b. 0 < a /\ 0 < b /\
    P (FUNPOW L a u) (FUNPOW R b v) /\ H a b u v) ==>
  ?A B. A 0 = 0 /\ B 0 = 0 /\
    (!n. A n < A (SUC n) /\ B n < B (SUC n)) /\
    (!n. P (FUNPOW L (A n) c) (FUNPOW R (B n) d)) /\
    (!n. H (A (SUC n) - A n) (B (SUC n) - B n)
      (FUNPOW L (A n) c) (FUNPOW R (B n) d))
Proof
  strip_tac >>
  qexistsl [`\n. FST (dft_segment_cuts L R P H c d n)`,
            `\n. SND (dft_segment_cuts L R P H c d n)`] >>
  simp[] >>
  `!n. P (FUNPOW L (FST (dft_segment_cuts L R P H c d n)) c)
         (FUNPOW R (SND (dft_segment_cuts L R P H c d n)) d)` by
    metis_tac[dft_segment_cuts_related] >>
  simp[dft_segment_cuts_def] >> conj_tac
  >- metis_tac[dft_segment_choice_spec] >>
  metis_tac[dft_segment_choice_spec]
QED

Theorem dft_increasing_cuts_bound:
  A 0 = 0 /\ (!n. A n < A (SUC n)) ==> !n. n <= A n
Proof
  strip_tac >> Induct >> simp[] >>
  first_x_assum (qspec_then `n` assume_tac) >> decide_tac
QED

Theorem dft_increasing_cuts_cover:
  A 0 = 0 /\ (!n. A n < A (SUC n)) ==>
  !j. ?n. A n <= j /\ j < A (SUC n)
Proof
  strip_tac >> Induct
  >- (qexists `0` >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  pop_assum strip_assume_tac >>
  Cases_on `SUC j < A (SUC n)`
  >- (qexists `n` >> simp[] >> decide_tac) >>
  qexists `SUC n` >>
  first_x_assum (qspec_then `SUC n` assume_tac) >> decide_tac
QED

Theorem dft_cut_offset:
  A n <= j ==> FUNPOW L j c = FUNPOW L (j - A n) (FUNPOW L (A n) c)
Proof
  strip_tac >> rewrite_tac[GSYM FUNPOW_ADD] >> AP_THM_TAC >> AP_TERM_TAC >> decide_tac
QED

(* Unequal rates exercise the half-open coverage interface. *)
Theorem dft_unequal_cuts_probe:
  (!n. 2*n < 2*SUC n /\ n < SUC n) /\
  (!j. ?n. 2*n <= j /\ j < 2*SUC n) /\
  (!j. ?n. n <= j /\ j < SUC n)
Proof
  conj_tac >- simp[] >> conj_tac
  >- (irule dft_increasing_cuts_cover >> simp[]) >>
  gen_tac >> qexists `j` >> simp[]
QED

Theorem dft_cofinal_segments:
  P c d /\ (!u v. P u v ==> ?a b. 0 < a /\ 0 < b /\
    P (FUNPOW L a u) (FUNPOW R b v) /\ H a b u v) ==>
  ?A B. A 0 = 0 /\ B 0 = 0 /\
    (!n. A n < A (SUC n) /\ B n < B (SUC n)) /\
    (!n. n <= A n /\ n <= B n) /\
    (!j. ?n. A n <= j /\ j < A (SUC n)) /\
    (!j. ?n. B n <= j /\ j < B (SUC n)) /\
    (!n. P (FUNPOW L (A n) c) (FUNPOW R (B n) d)) /\
    (!n. H (A (SUC n) - A n) (B (SUC n) - B n)
      (FUNPOW L (A n) c) (FUNPOW R (B n) d))
Proof
  strip_tac >> drule_all dft_positive_segments >> strip_tac >>
  qexistsl [`A`, `B`] >> simp[] >>
  metis_tac[dft_increasing_cuts_bound, dft_increasing_cuts_cover]
QED

Theorem dft_unequal_segments_probe:
  ?A B. A 0 = 0 /\ B 0 = 0 /\
    (!n. A n < A (SUC n) /\ B n < B (SUC n)) /\
    (!n. A (SUC n) - A n = 2 /\ B (SUC n) - B n = 1) /\
    (!j. ?n. A n <= j /\ j < A (SUC n)) /\
    (!j. ?n. B n <= j /\ j < B (SUC n))
Proof
  qexistsl [`\n. 2*n`, `\n:num. n`] >>
  simp[dft_unequal_cuts_probe]
QED

(* Annotations are chosen jointly with the segment, and passed to the next cut. *)
Definition dft_annotated_choice_def:
  dft_annotated_choice L R P account z c d =
    @abz. 0 < FST abz /\ 0 < FST (SND abz) /\
      P (SND (SND abz)) (FUNPOW L (FST abz) c) (FUNPOW R (FST (SND abz)) d) /\
      account z (SND (SND abz)) (FST abz) (FST (SND abz)) c d
End

Theorem dft_annotated_choice_spec[local]:
  (!z c d. P z c d ==> ?a b z'. 0 < a /\ 0 < b /\
    P z' (FUNPOW L a c) (FUNPOW R b d) /\ account z z' a b c d) /\ P z c d ==>
  0 < FST (dft_annotated_choice L R P account z c d) /\
  0 < FST (SND (dft_annotated_choice L R P account z c d)) /\
  P (SND (SND (dft_annotated_choice L R P account z c d)))
    (FUNPOW L (FST (dft_annotated_choice L R P account z c d)) c)
    (FUNPOW R (FST (SND (dft_annotated_choice L R P account z c d))) d) /\
  account z (SND (SND (dft_annotated_choice L R P account z c d)))
    (FST (dft_annotated_choice L R P account z c d))
    (FST (SND (dft_annotated_choice L R P account z c d))) c d
Proof
  strip_tac >> simp[dft_annotated_choice_def] >> SELECT_ELIM_TAC >>
  conj_tac >- (first_x_assum drule >> strip_tac >> qexists `(a,b,z')` >> simp[]) >> simp[]
QED

Definition dft_annotated_cuts_def:
  dft_annotated_cuts L R P account z c d 0 = (0,0,z) /\
  dft_annotated_cuts L R P account z c d (SUC n) =
    let abz = dft_annotated_cuts L R P account z c d n;
        step = dft_annotated_choice L R P account (SND (SND abz))
          (FUNPOW L (FST abz) c) (FUNPOW R (FST (SND abz)) d)
    in (FST abz + FST step, FST (SND abz) + FST (SND step), SND (SND step))
End

Theorem dft_annotated_cuts_related[local]:
  P z c d /\ (!z u v. P z u v ==> ?a b z'. 0 < a /\ 0 < b /\
    P z' (FUNPOW L a u) (FUNPOW R b v) /\ account z z' a b u v) ==>
  !n. P (SND (SND (dft_annotated_cuts L R P account z c d n)))
        (FUNPOW L (FST (dft_annotated_cuts L R P account z c d n)) c)
        (FUNPOW R (FST (SND (dft_annotated_cuts L R P account z c d n))) d)
Proof
  strip_tac >> Induct >> simp[dft_annotated_cuts_def] >>
  drule_all dft_annotated_choice_spec >>
  simp[dft_annotated_cuts_def, FUNPOW_ADD, ADD_COMM]
QED

Theorem dft_annotated_positive_segments:
  P z c d /\ (!z u v. P z u v ==> ?a b z'. 0 < a /\ 0 < b /\
    P z' (FUNPOW L a u) (FUNPOW R b v) /\ account z z' a b u v) ==>
  ?A B Z. A 0 = 0 /\ B 0 = 0 /\ Z 0 = z /\
    (!n. A n < A (SUC n) /\ B n < B (SUC n)) /\
    (!n. P (Z n) (FUNPOW L (A n) c) (FUNPOW R (B n) d)) /\
    (!n. account (Z n) (Z (SUC n)) (A (SUC n) - A n) (B (SUC n) - B n)
      (FUNPOW L (A n) c) (FUNPOW R (B n) d))
Proof
  strip_tac >>
  qexistsl [`\n. FST (dft_annotated_cuts L R P account z c d n)`,
            `\n. FST (SND (dft_annotated_cuts L R P account z c d n))`,
            `\n. SND (SND (dft_annotated_cuts L R P account z c d n))`] >> simp[] >>
  `!n. P (SND (SND (dft_annotated_cuts L R P account z c d n)))
        (FUNPOW L (FST (dft_annotated_cuts L R P account z c d n)) c)
        (FUNPOW R (FST (SND (dft_annotated_cuts L R P account z c d n))) d)` by
    metis_tac[dft_annotated_cuts_related] >>
  simp[dft_annotated_cuts_def] >> conj_tac
  >- metis_tac[dft_annotated_choice_spec] >>
  metis_tac[dft_annotated_choice_spec]
QED

Theorem dft_annotated_cofinal_segments:
  P z c d /\ (!z u v. P z u v ==> ?a b z'. 0 < a /\ 0 < b /\
    P z' (FUNPOW L a u) (FUNPOW R b v) /\ account z z' a b u v) ==>
  ?A B Z. A 0 = 0 /\ B 0 = 0 /\ Z 0 = z /\
    (!n. A n < A (SUC n) /\ B n < B (SUC n)) /\
    (!n. n <= A n /\ n <= B n) /\
    (!j. ?n. A n <= j /\ j < A (SUC n)) /\
    (!j. ?n. B n <= j /\ j < B (SUC n)) /\
    (!n. P (Z n) (FUNPOW L (A n) c) (FUNPOW R (B n) d)) /\
    (!n. account (Z n) (Z (SUC n)) (A (SUC n) - A n) (B (SUC n) - B n)
      (FUNPOW L (A n) c) (FUNPOW R (B n) d))
Proof
  strip_tac >> drule_all dft_annotated_positive_segments >> strip_tac >>
  qexistsl [`A`,`B`,`Z`] >> simp[] >>
  metis_tac[dft_increasing_cuts_bound, dft_increasing_cuts_cover]
QED
