Theory o1MakeSsaClosure
Ancestors
  unitShapeDefs o1SourceUnitCheck list pred_set

(* Predicate-valued version of the existing finite-list certificate. *)
Definition cp_closed_def:
  cp_closed origin fn P <=>
    (!inst x. MEM inst (fn_insts fn) /\ inst.inst_opcode = origin /\
      MEM x inst.inst_outputs ==> P x) /\
    (!inst x y. MEM inst (fn_insts fn) /\ inst.inst_opcode = ASSIGN /\
      inst.inst_operands = [Var y] /\ MEM x inst.inst_outputs /\ P y ==> P x) /\
    (!inst x y. MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
      MEM (Var y) inst.inst_operands /\ MEM x inst.inst_outputs /\ P y ==> P x)
End

Theorem copy_phi_var_closed_sound:
  !origin fn x. copy_phi_var origin fn x ==>
    !P. cp_closed origin fn P ==> P x
Proof
  Induct_on `copy_phi_var` >> rpt strip_tac >>
  qpat_assum `cp_closed _ _ _` mp_tac >>
  pure_rewrite_tac[cp_closed_def] >> metis_tac[]
QED

Theorem copy_phi_var_closed:
  cp_closed origin fn (copy_phi_var origin fn)
Proof
  simp[cp_closed_def] >> metis_tac[copy_phi_var_rules]
QED

Theorem copy_phi_var_least_closed:
  copy_phi_var origin fn x <=> !P. cp_closed origin fn P ==> P x
Proof
  eq_tac >- metis_tac[copy_phi_var_closed_sound] >>
  disch_then (qspec_then `copy_phi_var origin fn` mp_tac) >>
  simp[copy_phi_var_closed]
QED

Theorem copy_phi_var_closed_certificate:
  (!P. cp_closed origin fn P ==> !x. x IN A ==> P x) ==>
  !x. x IN A ==> copy_phi_var origin fn x
Proof
  metis_tac[copy_phi_var_least_closed]
QED

Definition cp_bad_set_def:
  cp_bad_set origin fn B <=>
    (!inst x. MEM inst (fn_insts fn) /\ inst.inst_opcode = origin /\
      MEM x inst.inst_outputs ==> x NOTIN B) /\
    (!inst x y. MEM inst (fn_insts fn) /\ inst.inst_opcode = ASSIGN /\
      inst.inst_operands = [Var y] /\ MEM x inst.inst_outputs /\ x IN B ==>
      y IN B) /\
    (!inst x y. MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
      MEM (Var y) inst.inst_operands /\ MEM x inst.inst_outputs /\ x IN B ==>
      y IN B)
End

Theorem cp_bad_set_complement:
  cp_bad_set origin fn B <=> cp_closed origin fn (\x. x NOTIN B)
Proof
  simp[cp_bad_set_def, cp_closed_def] >> metis_tac[]
QED

Theorem copy_phi_var_bad_set:
  ~copy_phi_var origin fn x <=> ?B. x IN B /\ cp_bad_set origin fn B
Proof
  eq_tac
  >- (strip_tac >> qexists_tac `{y | ~copy_phi_var origin fn y}` >>
      simp[cp_bad_set_complement, SF ETA_ss, copy_phi_var_closed]) >>
  strip_tac >> fs[cp_bad_set_complement] >>
  strip_tac >> drule copy_phi_var_closed_sound >>
  disch_then (qspec_then `\x. x NOTIN B` mp_tac) >> simp[]
QED

Theorem cp_closed_list_certificate:
  cp_closed origin fn (\x. MEM x seen) <=> copy_phi_closed origin fn seen
Proof
  simp[cp_closed_def, copy_phi_closed_def, EVERY_MEM,
       copy_phi_fires_def, EXISTS_MEM] >>
  eq_tac >> rpt strip_tac
  >- metis_tac[]
  >- (Cases_on `inst.inst_operands` >> gvs[] >>
      rename1 `h::t` >> Cases_on `h` >> gvs[] >>
      Cases_on `t` >> gvs[] >> metis_tac[])
  >- (rename1 `MEM op inst.inst_operands` >>
      Cases_on `op` >> gvs[] >> metis_tac[])
  >- (first_x_assum drule >> simp[] >> metis_tac[])
  >- (first_x_assum drule >> simp[] >> metis_tac[])
  >- (first_x_assum drule >> simp[] >>
      disch_then irule >> conj_tac >- simp[] >> disj2_tac >>
      qexists_tac `Var x'` >> simp[])
QED
