Theory fmpStepList
Ancestors
  list

(* Compositional counterparts of the indexed block-order conditions. *)
Definition list_prefix_def:
  (list_prefix P [] <=> T) /\
  (list_prefix P (h::t) <=>
    list_prefix P t /\ (~P h ==> EVERY (\x. ~P x) t))
End

Definition list_terminal_def:
  (list_terminal P [] <=> F) /\
  (list_terminal P (h::t) <=>
    if t = [] then P h else ~P h /\ list_terminal P t)
End

Theorem list_prefix_every:
  EVERY P xs ==> list_prefix P xs
Proof
  Induct_on `xs` >> simp[list_prefix_def]
QED

Theorem list_prefix_none:
  EVERY (\x. ~P x) xs ==> list_prefix P xs
Proof
  Induct_on `xs` >> simp[list_prefix_def]
QED

Theorem list_prefix_append:
  list_prefix P (xs ++ ys) <=>
    list_prefix P xs /\ list_prefix P ys /\
    ((?x. MEM x xs /\ ~P x) ==> EVERY (\x. ~P x) ys)
Proof
  Induct_on `xs` >> simp[list_prefix_def, EVERY_APPEND] >>
  metis_tac[]
QED

Theorem list_terminal_append:
  ys <> [] ==>
  (list_terminal P (xs ++ ys) <=>
   EVERY (\x. ~P x) xs /\ list_terminal P ys)
Proof
  Induct_on `xs` >> simp[list_terminal_def] >> metis_tac[]
QED

Theorem list_prefix_indexed:
  list_prefix P xs <=>
    !i j. i < j /\ j < LENGTH xs /\ P (EL j xs) ==> P (EL i xs)
Proof
  Induct_on `xs` >- simp[list_prefix_def] >>
  gen_tac >> rewrite_tac[list_prefix_def] >> eq_tac
  >- (strip_tac >> map_every qx_gen_tac [`i`, `j`] >>
      Cases_on `i` >> Cases_on `j` >> simp[] >>
      rpt strip_tac >> gvs[EVERY_EL] >> metis_tac[]) >>
  disch_tac >> conj_tac
  >- (asm_rewrite_tac[] >> rpt strip_tac >>
      first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
  strip_tac >> simp[EVERY_EL] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]
QED

Theorem list_terminal_indexed:
  list_terminal P xs <=>
    xs <> [] /\ P (LAST xs) /\
    (!i. i < LENGTH xs /\ P (EL i xs) ==> i = PRE (LENGTH xs))
Proof
  Induct_on `xs` >- simp[list_terminal_def] >>
  gen_tac >> Cases_on `xs = []` >- gvs[list_terminal_def] >>
  simp[list_terminal_def, LAST_DEF] >>
  `0 < LENGTH xs` by (Cases_on `xs` >> gvs[]) >>
  eq_tac
  >- (strip_tac >> simp[] >> Cases >> simp[] >> rpt strip_tac >>
      `n = PRE (LENGTH xs)` by metis_tac[] >> decide_tac) >>
  strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[] >> decide_tac) >>
  simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >> simp[] >> decide_tac
QED

Theorem list_prefix_expand:
  (!x. MEM x xs ==> if P x then EVERY Q (f x)
                            else EVERY (\y. ~Q y) (f x)) /\
  list_prefix P xs ==> list_prefix Q (FLAT (MAP f xs))
Proof
  Induct_on `xs` >- simp[list_prefix_def] >>
  simp[list_prefix_def, list_prefix_append] >>
  gen_tac >> disch_then strip_assume_tac >> Cases_on `P h`
  >- (conj_tac
      >- (irule list_prefix_every >> metis_tac[]) >>
      gvs[EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (irule list_prefix_none >> metis_tac[]) >>
  simp[EVERY_FLAT, EVERY_MAP, EVERY_MEM] >>
  rpt strip_tac >> gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem list_terminal_expand:
  (!x. MEM x xs ==> f x <> [] /\
    if P x then list_terminal Q (f x)
    else EVERY (\y. ~Q y) (f x)) /\
  list_terminal P xs ==> list_terminal Q (FLAT (MAP f xs))
Proof
  Induct_on `xs` >- simp[list_terminal_def] >>
  gen_tac >> Cases_on `xs = []`
  >- (gvs[list_terminal_def] >> metis_tac[]) >>
  simp[list_terminal_def] >> strip_tac >>
  `FLAT (MAP f xs) <> []` by
    (Cases_on `xs` >> gvs[] >> metis_tac[]) >>
  simp[list_terminal_append] >> metis_tac[]
QED

(* Identity and insertion probes exercise both append boundaries. *)
Theorem list_expand_identity:
  FLAT (MAP (\x. [x]) xs) = xs
Proof
  Induct_on `xs` >> simp[]
QED

Theorem list_prefix_insert:
  list_prefix P (xs ++ ys) /\ EVERY (\x. ~P x) ins /\
  EVERY (\x. ~P x) ys ==> list_prefix P (xs ++ ins ++ ys)
Proof
  simp[list_prefix_append, EVERY_APPEND] >>
  metis_tac[list_prefix_none]
QED

Theorem list_terminal_insert:
  ys <> [] /\ list_terminal P (xs ++ ys) /\
  EVERY (\x. ~P x) ins ==> list_terminal P (xs ++ ins ++ ys)
Proof
  strip_tac >> gvs[list_terminal_append, EVERY_APPEND]
QED
