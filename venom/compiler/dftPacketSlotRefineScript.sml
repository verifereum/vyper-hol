Theory dftPacketSlotRefine
Ancestors
  list rich_list sorting option

Theorem dft_slot_fill_values:
  !slots i w tail.
    i < LENGTH slots /\ EL i slots = NONE ==>
    PERM (MAP THE (FILTER IS_SOME (LUPDATE (SOME w) i slots)) ++ tail)
      (MAP THE (FILTER IS_SOME slots) ++ w::tail)
Proof
  Induct_on `slots` >- simp[LUPDATE_def] >>
  rpt gen_tac >> Cases_on `i` >> simp[LUPDATE_def] >>
  Cases_on `h` >> simp[LUPDATE_def] >>
  irule CONS_PERM >> simp[]
QED

Theorem dft_slot_fill_compatible:
  !slots i w gs.
    i < LENGTH slots /\ EL i slots = NONE /\
    LIST_REL (\slot v. slot = NONE \/ slot = SOME v)
      (LUPDATE (SOME w) i slots) gs ==>
    LIST_REL (\slot v. slot = NONE \/ slot = SOME v) slots gs
Proof
  Induct_on `slots` >- simp[LUPDATE_def] >>
  rpt gen_tac >> Cases_on `i` >> Cases_on `gs` >> simp[LUPDATE_def] >>
  metis_tac[]
QED

Theorem dft_slot_fill_observation:
  !slots keys i w obs.
    LENGTH keys = LENGTH slots /\ i < LENGTH slots /\ EL i slots = NONE /\
    PERM (MAP (\(k,v). (k,THE v))
      (FILTER (\(k,v). IS_SOME v) (ZIP(keys,slots)))) obs ==>
    PERM (MAP (\(k,v). (k,THE v))
      (FILTER (\(k,v). IS_SOME v) (ZIP(keys,LUPDATE (SOME w) i slots))))
      (obs ++ [(EL i keys,w)])
Proof
  Induct_on `slots` >- simp[LUPDATE_def] >>
  rpt gen_tac >> Cases_on `keys` >- simp[LUPDATE_def] >>
  Cases_on `i` >> simp[LUPDATE_def] >>
  Cases_on `h` >> simp[LUPDATE_def] >> rpt strip_tac
  >- (irule CONS_PERM >> simp[]) >>
  qpat_x_assum `PERM (_::_) obs` mp_tac >>
  simp[PERM_CONS_EQ_APPEND] >> rpt strip_tac >> gvs[] >>
  qexistsl [`M`, `N ++ [(EL n t,w)]`] >>
  simp[APPEND_ASSOC] >> first_x_assum irule >> simp[]
QED
