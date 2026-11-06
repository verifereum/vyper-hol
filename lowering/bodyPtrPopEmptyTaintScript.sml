Theory bodyPtrPopEmptyTaint
Ancestors
  ptrDiscipline finite_map

Theorem pop_fempty_taint:
  !u m. FLOOKUP FEMPTY u = SOME m ==> m = ({}:num set)
Proof
  simp[]
QED

Theorem pop_fupdate_taint_empty:
  (!u m. FLOOKUP tv u = SOME m ==> m = {}) ==>
  (!u m. FLOOKUP (tv |+ (v,{})) u = SOME m ==> m = {})
Proof
  simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem pop_set_var_taint_empty:
  (!u m. FLOOKUP tv u = SOME m ==> m = {}) ==>
  (!u m. FLOOKUP (set_var_taint tv outs {}) u = SOME m ==> m = {})
Proof
  strip_tac >> Cases_on `outs`
  >- (simp[set_var_taint_def, DRESTRICT_UNIV] >> metis_tac[]) >>
  Cases_on `t` >> simp[set_var_taint_def, FLOOKUP_UPDATE,
    FLOOKUP_DRESTRICT] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem pop_op_taint_empty:
  (!u m. FLOOKUP tn.t_var u = SOME m ==> m = {}) ==>
  op_taint tn op = {}
Proof
  strip_tac >> Cases_on `op` >> simp[op_taint_def] >>
  CASE_TAC >> simp[] >> metis_tac[]
QED

Theorem pop_taint_ok_empty:
  (!u m. FLOOKUP tn.t_var u = SOME m ==> m = {}) /\
  tn.t_mem = {} /\ tn.t_stor = {} /\ tn.t_trans = {} ==>
  taint_ok fn tn inst s
Proof
  strip_tac >> drule pop_op_taint_empty >> strip_tac >>
  simp[taint_ok_def]
QED
