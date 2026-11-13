(* Parallel pointer/taint PHIs and updates independent of their selected inputs. *)
Theory ptrPhiUpdate
Ancestors ptrDiscipline finite_map list pred_set

Theorem set_prov_update_commute:
  ~MEM x outs ==>
  set_prov (G |+ (x,value)) outs p = (set_prov G outs p) |+ (x,value)
Proof
  Cases_on `outs` >> Cases_on `p` >> simp[set_prov_def] >>
  Cases_on `t` >> simp[set_prov_def, FUPDATE_COMMUTES] >>
  rw[fmap_eq_flookup, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >> simp[]
QED

Theorem phi_prov_update_independent:
  (!lbl. prev = SOME lbl ==> resolve_phi lbl inst.inst_operands <> SOME (Var x)) ==>
  phi_prov prev (G |+ (x,value)) inst = phi_prov prev G inst
Proof
  Cases_on `prev` >> simp[phi_prov_def] >>
  Cases_on `resolve_phi x' inst.inst_operands` >> simp[] >>
  Cases_on `x''` >> simp[op_prov_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem phis_prov_update_commute:
  !insts. EVERY (\i. ~MEM x i.inst_outputs /\
    (!lbl. prev = SOME lbl ==> resolve_phi lbl i.inst_operands <> SOME (Var x))) insts ==>
  phis_prov prev (G |+ (x,value)) insts =
    (phis_prov prev G insts) |+ (x,value)
Proof
  Induct >> simp[phis_prov_def] >> strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  simp[phi_prov_update_independent, set_prov_update_commute]
QED

Theorem set_var_taint_update_commute:
  ~MEM x outs ==>
  set_var_taint (tv |+ (x,value)) outs m = (set_var_taint tv outs m) |+ (x,value)
Proof
  Cases_on `outs` >> simp[set_var_taint_def] >>
  Cases_on `t` >> simp[set_var_taint_def, FUPDATE_COMMUTES] >>
  rw[fmap_eq_flookup, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >> simp[]
QED

Theorem phi_taint_update_independent:
  (!lbl. prev = SOME lbl ==> resolve_phi lbl inst.inst_operands <> SOME (Var x)) ==>
  phi_taint prev (tn with t_var := tn.t_var |+ (x,value)) inst = phi_taint prev tn inst
Proof
  Cases_on `prev` >> simp[phi_taint_def] >>
  Cases_on `resolve_phi x' inst.inst_operands` >> simp[] >>
  Cases_on `x''` >> simp[op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem phis_taint_update_commute:
  !insts. EVERY (\i. ~MEM x i.inst_outputs /\
    (!lbl. prev = SOME lbl ==> resolve_phi lbl i.inst_operands <> SOME (Var x))) insts ==>
  phis_taint prev (tn with t_var := tn.t_var |+ (x,value)) insts =
    (phis_taint prev tn insts) |+ (x,value)
Proof
  Induct >> simp[phis_taint_def] >> strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  simp[phi_taint_update_independent, set_var_taint_update_commute]
QED
