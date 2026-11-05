Theory o1MakeSsaRetpcTransport
Ancestors o1ContractMakeSsaPtrOk o1MakeSsaRequiredUses unitShapeDefs list

Theorem mssa_retpc_definition_cases:
  retpc_shape_ok fn /\ mssa_inst_origin orig fn i /\
  MEM i (fn_insts g) /\ MEM v i.inst_outputs /\ retpc_var fn (orig v) ==>
  i.inst_opcode = RETPC_PARAM \/
  (i.inst_opcode = ASSIGN /\ ?u. i.inst_operands = [Var u] /\ retpc_var fn (orig u)) \/
  (i.inst_opcode = PHI /\ !u. MEM (Var u) i.inst_operands ==> retpc_var fn (orig u))
Proof
  strip_tac >> qpat_x_assum `mssa_inst_origin _ _ _` mp_tac >>
  pure_rewrite_tac[mssa_inst_origin_def] >> strip_tac
  >- (`MEM (orig v) inst.inst_outputs` by metis_tac[listTheory.MEM_MAP] >>
      gvs[retpc_shape_ok_def] >>
      qpat_x_assum `!inst x. MEM inst (fn_insts fn) /\ _ ==> _` drule_all >>
      strip_tac >> gvs[] >>
      Cases_on `i.inst_operands` >> gvs[] >>
      Cases_on `h` >> gvs[]) >>
  gvs[retpc_shape_ok_def] >>
  qpat_x_assum `!inst x. MEM inst (fn_insts fn) /\ _ ==> _` drule_all >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem mssa_retpc_origin_forward:
  !g v. retpc_var g v ==> !orig fn.
  (!i. MEM i (fn_insts g) ==> mssa_inst_origin orig fn i) ==>
  retpc_var fn (orig v)
Proof
  simp[retpc_var_def] >> Induct_on `copy_phi_var` >> rpt strip_tac >> gvs[]
  >- (qpat_x_assum `!i. MEM i _ ==> mssa_inst_origin _ _ _` drule >>
      pure_rewrite_tac[mssa_inst_origin_def] >> strip_tac >> gvs[] >>
      metis_tac[copy_phi_var_rules, MEM_MAP]) >>
  rename1 `copy_phi_var RETPC_PARAM g u` >>
  `copy_phi_var RETPC_PARAM fn (orig u)` by
    (first_x_assum irule >> simp[]) >>
  qpat_x_assum `!i. MEM i _ ==> mssa_inst_origin _ _ _` drule >>
  pure_rewrite_tac[mssa_inst_origin_def] >> strip_tac >>
  gvs[]
  >- (`MEM (orig v) inst'.inst_outputs` by metis_tac[MEM_MAP] >>
      irule (cj 2 copy_phi_var_rules) >> metis_tac[]) >>
  metis_tac[cj 3 copy_phi_var_rules]
QED
