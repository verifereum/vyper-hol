Theory dftPacketKeySubstitution
Ancestors
  list rich_list option arithmetic

Theorem dft_key_substitute_shape:
  !slots keys needle w.
    LENGTH slots = LENGTH keys ==>
    LENGTH (MAP2 (\slot key. if key = needle then SOME w else slot) slots keys) =
      LENGTH slots /\
    (~MEM needle keys ==>
      MAP2 (\slot key. if key = needle then SOME w else slot) slots keys = slots)
Proof
  Induct_on `slots` >> Cases_on `keys` >> simp[] >> metis_tac[]
QED

Theorem dft_key_substitute_lupdate:
  !slots keys i needle w.
    LENGTH slots = LENGTH keys /\ ALL_DISTINCT keys /\
    i < LENGTH keys /\ EL i keys = needle ==>
    MAP2 (\slot key. if key = needle then SOME w else slot) slots keys =
      LUPDATE (SOME w) i slots
Proof
  Induct_on `slots` >> Cases_on `keys` >> simp[] >>
  Cases_on `i` >> simp[LUPDATE_def] >> rpt strip_tac
  >- metis_tac[dft_key_substitute_shape] >>
  rename1 `~MEM key keys` >>
  `EL n keys <> key` by metis_tac[MEM_EL] >> simp[] >>
  first_x_assum irule >> simp[]
QED

Theorem dft_key_substitute_compatible:
  !slots keys needle w gs.
    LENGTH slots = LENGTH keys /\
    (!i. i < LENGTH keys /\ EL i keys = needle ==> EL i slots = NONE) /\
    LIST_REL (\slot v. slot = NONE \/ slot = SOME v)
      (MAP2 (\slot key. if key = needle then SOME w else slot) slots keys) gs ==>
    LIST_REL (\slot v. slot = NONE \/ slot = SOME v) slots gs
Proof
  simp[LIST_REL_EL_EQN] >> rpt gen_tac >> strip_tac >>
  conj_tac >- gvs[] >> qx_gen_tac `i` >> strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[EL_MAP2] >>
  Cases_on `EL i keys = needle` >> simp[] >> metis_tac[]
QED

Theorem dft_key_substitute_rows_compatible:
  !rows keyrows needle w gss.
    LIST_REL (\slots keys. LENGTH slots = LENGTH keys) rows keyrows /\
    (!i j. i < LENGTH rows /\ j < LENGTH (EL i keyrows) /\
      EL j (EL i keyrows) = needle ==> EL j (EL i rows) = NONE) /\
    LIST_REL (LIST_REL (\slot v. slot = NONE \/ slot = SOME v))
      (MAP2 (\slots keys.
        MAP2 (\slot key. if key = needle then SOME w else slot) slots keys)
        rows keyrows) gss ==>
    LIST_REL (LIST_REL (\slot v. slot = NONE \/ slot = SOME v)) rows gss
Proof
  rpt gen_tac >> strip_tac >> simp[Once LIST_REL_EL_EQN] >>
  conj_tac >- gvs[LIST_REL_EL_EQN] >>
  qx_gen_tac `i` >> strip_tac >>
  irule dft_key_substitute_compatible >>
  qexistsl [`EL i keyrows`, `needle`, `w`] >>
  gvs[LIST_REL_EL_EQN, EL_MAP2] >> metis_tac[]
QED

Theorem dft_key_substitute_rows_take_compatible:
  !rows keyrows needle w n gss.
    LIST_REL (\slots keys. LENGTH slots = LENGTH keys) rows keyrows /\
    (!i j. i < LENGTH rows /\ j < LENGTH (EL i keyrows) /\
      EL j (EL i keyrows) = needle ==> EL j (EL i rows) = NONE) /\
    LIST_REL (LIST_REL (\slot v. slot = NONE \/ slot = SOME v))
      (TAKE n (MAP2 (\slots keys.
        MAP2 (\slot key. if key = needle then SOME w else slot) slots keys)
        rows keyrows)) gss ==>
    LIST_REL (LIST_REL (\slot v. slot = NONE \/ slot = SOME v)) (TAKE n rows) gss
Proof
  rpt gen_tac >> strip_tac >> simp[Once LIST_REL_EL_EQN] >>
  conj_tac >- gvs[LIST_REL_EL_EQN, LENGTH_TAKE_EQ] >>
  qx_gen_tac `i` >> strip_tac >>
  `i < n /\ i < LENGTH rows` by
    (Cases_on `n <= LENGTH rows` >> gvs[LENGTH_TAKE_EQ]) >>
  simp[EL_TAKE] >> irule dft_key_substitute_compatible >>
  qexistsl [`EL i keyrows`, `needle`, `w`] >>
  gvs[LIST_REL_EL_EQN, LENGTH_TAKE_EQ, EL_TAKE, EL_MAP2] >> metis_tac[]
QED
