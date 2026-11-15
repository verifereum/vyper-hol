Theory fmpStepClosure
Ancestors
  unitShapeDefs

Definition copy_phi_upper_bound_def:
  copy_phi_upper_bound origin fn P <=>
  (!inst x. MEM inst (fn_insts fn) /\ inst.inst_opcode = origin /\
       MEM x inst.inst_outputs ==> P x) /\
  (!inst x y. MEM inst (fn_insts fn) /\ inst.inst_opcode = ASSIGN /\
       inst.inst_operands = [Var y] /\ MEM x inst.inst_outputs /\ P y ==> P x) /\
  (!inst x y. MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
       MEM (Var y) inst.inst_operands /\ MEM x inst.inst_outputs /\ P y ==> P x)
End

Theorem copy_phi_upper_bound_sound:
  !origin fn x. copy_phi_var origin fn x ==>
    !P. copy_phi_upper_bound origin fn P ==> P x
Proof
  Induct_on `copy_phi_var` >> rpt conj_tac >> rpt gen_tac >>
  strip_tac >> gen_tac >> strip_tac >>
  qpat_assum `copy_phi_upper_bound _ _ P`
    (strip_assume_tac o PURE_REWRITE_RULE [copy_phi_upper_bound_def])
  >- (qpat_x_assum `!i z. _ /\ i.inst_opcode = origin /\ _ ==> _` irule >>
      qexists_tac `inst` >> asm_rewrite_tac[]) 
  >- (first_x_assum (qspec_then `P` mp_tac) >>
      asm_rewrite_tac[] >> strip_tac >>
      qpat_x_assum `!i z y. _ /\ i.inst_opcode = ASSIGN /\ _ ==> _` irule >>
      qexistsl_tac [`inst`,`x'`] >> asm_rewrite_tac[]) >>
  first_x_assum (qspec_then `P` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `!i z y. _ /\ i.inst_opcode = PHI /\ _ ==> _` irule >>
  qexistsl_tac [`inst`,`x'`] >> asm_rewrite_tac[]
QED

Theorem copy_phi_upper_bound_identity:
  copy_phi_upper_bound origin fn (copy_phi_var origin fn)
Proof
  simp[copy_phi_upper_bound_def] >>
  metis_tac[copy_phi_var_rules]
QED

Theorem copy_phi_upper_bound_assign_nonopaque:
  ~P y ==>
  !x. (inst.inst_operands = [Var y] /\ P y ==> P x)
Proof
  simp[]
QED

Theorem copy_phi_upper_bound_transfer:
  copy_phi_upper_bound origin fn P /\
  (!j. MEM j (fn_insts fn') ==>
    ~MEM j.inst_opcode [origin; ASSIGN; PHI] \/
    ?i. MEM i (fn_insts fn) /\ j.inst_opcode = i.inst_opcode /\
      j.inst_outputs = i.inst_outputs /\
      (MEM j.inst_opcode [ASSIGN; PHI] ==> j.inst_operands = i.inst_operands)) ==>
  copy_phi_upper_bound origin fn' P
Proof
  simp[copy_phi_upper_bound_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED
