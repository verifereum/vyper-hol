Theory bodyPtrPopWindow
Ancestors
  list rich_list arithmetic

(* These list interfaces retain actual instructions/operands and factor the
   repeated finite-window decompositions needed at compiler bind boundaries. *)
Definition occurs5_def:
  occurs5 winp xs <=>
    ?p w q. xs = p ++ w ++ q /\ LENGTH w = 5 /\ winp w
End

Definition tail4_def:
  tail4 xs = DROP (LENGTH xs - 4) xs
End

Theorem occurs5_nil[simp]:
  ~occurs5 winp []
Proof
  simp[occurs5_def]
QED

Theorem length_tail4:
  LENGTH (tail4 xs) = MIN 4 (LENGTH xs)
Proof
  simp[tail4_def, LENGTH_DROP, MIN_DEF]
QED

Theorem length_tail4_bound:
  LENGTH (tail4 xs) <= 4
Proof
  simp[length_tail4]
QED

Theorem tail4_short:
  LENGTH xs <= 4 ==> tail4 xs = xs
Proof
  strip_tac >> `LENGTH xs - 4 = 0` by decide_tac >> simp[tail4_def]
QED

Theorem tail4_append:
  tail4 (xs ++ ys) = tail4 (tail4 xs ++ ys)
Proof
  Cases_on `LENGTH xs <= 4`
  >- simp[tail4_short] >>
  simp[tail4_def, LENGTH_DROP, DROP_APPEND] >>
  `LENGTH xs - (LENGTH xs - 4) = 4` by decide_tac >>
  Cases_on `LENGTH ys <= 4`
  >- (`LENGTH xs + LENGTH ys - 4 = LENGTH ys + (LENGTH xs - 4)`
        by decide_tac >> pure_asm_rewrite_tac [] >>
      sym_tac >> irule DROP_DROP >> decide_tac) >>
  simp[DROP_LENGTH_TOO_LONG]
QED

Theorem occurs5_append_left:
  occurs5 winp xs ==> occurs5 winp (xs ++ ys)
Proof
  simp[occurs5_def] >> rpt strip_tac >>
  qexistsl_tac [`p`,`w`,`q ++ ys`] >> simp[APPEND_ASSOC]
QED

Theorem occurs5_append_right:
  occurs5 winp ys ==> occurs5 winp (xs ++ ys)
Proof
  simp[occurs5_def] >> rpt strip_tac >>
  qexistsl_tac [`xs ++ p`,`w`,`q`] >> simp[APPEND_ASSOC]
QED

Theorem occurs5_short:
  LENGTH xs < 5 ==> ~occurs5 winp xs
Proof
  simp[occurs5_def] >> rpt strip_tac >> gvs[]
QED

Theorem occurs5_cons:
  occurs5 winp (h::xs) <=>
  occurs5 winp xs \/
    (?w q. h::xs = w ++ q /\ LENGTH w = 5 /\ winp w)
Proof
  eq_tac
  >- (simp[occurs5_def] >> rpt strip_tac >> Cases_on `p` >> gvs[]
      >- metis_tac[] >> disj1_tac >>
      qexistsl_tac [`t`,`w`,`q`] >> simp[]) >>
  simp[occurs5_def] >> rpt strip_tac
  >- (qexistsl_tac [`h::p`,`w`,`q`] >> simp[]) >>
  qexistsl_tac [`[]`,`w`,`q`] >> simp[]
QED

Theorem occurs5_head:
  (?w q. xs = w ++ q /\ LENGTH w = 5 /\ winp w) <=>
  5 <= LENGTH xs /\ winp (TAKE 5 xs)
Proof
  eq_tac
  >- (rpt strip_tac >> gvs[TAKE_APPEND] >>
      metis_tac[TAKE_LENGTH_ID]) >>
  strip_tac >> qexistsl_tac [`TAKE 5 xs`,`DROP 5 xs`] >>
  simp[TAKE_DROP, LENGTH_TAKE]
QED

Theorem occurs5_cons_take:
  occurs5 winp (h::xs) <=> occurs5 winp xs \/
    (5 <= LENGTH (h::xs) /\ winp (TAKE 5 (h::xs)))
Proof
  simp[occurs5_cons, occurs5_head]
QED

Theorem occurs5_exact:
  LENGTH xs = 5 ==> (occurs5 winp xs <=> winp xs)
Proof
  strip_tac >> eq_tac
  >- (simp[occurs5_def] >> rpt strip_tac >> gvs[] >>
      `LENGTH p = 0 /\ LENGTH q = 0` by decide_tac >> gvs[]) >>
  strip_tac >> simp[occurs5_def] >>
  qexistsl_tac [`[]`,`xs`,`[]`] >> simp[]
QED

Theorem tail4_cons_long:
  4 <= LENGTH xs ==> tail4 (h::xs) = tail4 xs
Proof
  strip_tac >> simp[tail4_def] >>
  `SUC (LENGTH xs) - 4 = SUC (LENGTH xs - 4)` by decide_tac >>
  simp[DROP] >> AP_THM_TAC >> AP_TERM_TAC >> decide_tac
QED

Theorem occurs5_snoc:
  occurs5 winp (xs ++ [i]) <=> occurs5 winp xs \/
    (4 <= LENGTH xs /\ winp (tail4 xs ++ [i]))
Proof
  Induct_on `xs`
  >- simp[occurs5_short] >>
  Cases_on `LENGTH xs < 4`
  >- (Cases_on `LENGTH xs = 3`
      >- simp[occurs5_short, tail4_short, occurs5_exact] >>
      simp[occurs5_short, tail4_short]) >>
  simp[occurs5_cons_take, tail4_cons_long, TAKE_APPEND] >>
  `4 - LENGTH xs = 0` by decide_tac >> simp[] >> metis_tac[]
QED

Theorem occurs5_append_tail:
  !ys xs. occurs5 winp (xs ++ ys) <=>
    occurs5 winp xs \/ occurs5 winp (tail4 xs ++ ys)
Proof
  Induct_on `ys` using SNOC_INDUCT
  >- simp[occurs5_short, length_tail4] >>
  rpt gen_tac >>
  pure_rewrite_tac[SNOC_APPEND, APPEND_ASSOC, occurs5_snoc, LENGTH_APPEND,
                   LENGTH] >>
  first_x_assum (qspec_then `xs` assume_tac) >>
  `tail4 (tail4 xs ++ ys) = tail4 (xs ++ ys)` by
    metis_tac[tail4_append] >>
  `(4 <= LENGTH xs + LENGTH ys) =
   (4 <= LENGTH (tail4 xs) + LENGTH ys)` by
    simp[length_tail4, MIN_DEF] >>
  metis_tac[]
QED

Theorem occurs5_reverse:
  occurs5 winp (REVERSE xs) <=> occurs5 (winp o REVERSE) xs
Proof
  simp[occurs5_def] >> eq_tac >> rpt strip_tac
  >- (qexistsl_tac [`REVERSE q`,`REVERSE w`,`REVERSE p`] >>
      simp[] >> metis_tac[REVERSE_APPEND, REVERSE_REVERSE, APPEND_ASSOC]) >>
  qexistsl_tac [`REVERSE q`,`REVERSE w`,`REVERSE p`] >>
  simp[REVERSE_APPEND]
QED

Theorem reverse_tail4:
  REVERSE (tail4 (REVERSE xs)) = TAKE 4 xs
Proof
  Cases_on `LENGTH xs <= 4`
  >- simp[tail4_short, TAKE_LENGTH_TOO_LONG] >>
  `LENGTH (TAKE 4 xs) = 4` by simp[LENGTH_TAKE] >>
  `tail4 (REVERSE (DROP 4 xs) ++ REVERSE (TAKE 4 xs)) =
   REVERSE (TAKE 4 xs)` by
    simp[tail4_def, DROP_APPEND, LENGTH_REVERSE] >>
  `REVERSE xs = REVERSE (DROP 4 xs) ++ REVERSE (TAKE 4 xs)` by
    metis_tac[TAKE_DROP, REVERSE_APPEND] >>
  metis_tac[REVERSE_REVERSE]
QED

Theorem occurs5_append_head:
  occurs5 winp (xs ++ ys) <=>
    occurs5 winp ys \/ occurs5 winp (xs ++ TAKE 4 ys)
Proof
  qspecl_then [`winp o REVERSE`,`REVERSE xs`,`REVERSE ys`] mp_tac
    (GEN_ALL occurs5_append_tail) >>
  pure_rewrite_tac[GSYM occurs5_reverse] >>
  simp[REVERSE_APPEND, reverse_tail4]
QED

Theorem occurs5_append:
  occurs5 winp (xs ++ ys) <=> occurs5 winp xs \/ occurs5 winp ys \/
    occurs5 winp (tail4 xs ++ TAKE 4 ys)
Proof
  metis_tac[occurs5_append_tail, occurs5_append_head]
QED
