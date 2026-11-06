Theory fnLineageInvPhi
Ancestors
  fnPlanLineagePhiInventory fnPlanPrefix fnPlanLineagePhiTemporal
  stackPlanOps stackModel stackPlanGen stackPlanTypes planAlign venomInst list finite_map

Theorem dead_input_live_output_phi_released_membership:
 !inst nl halting ps d x ops qs final.
 stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
 stack_peek d ps.ps_stack = x /\
 is_var_operand x /\
 LENGTH (FILTER (\op. op = x) ps.ps_stack) = 1 /\
 ~MEM (operand_to_string x) nl /\
 MEM (HD inst.inst_outputs) nl /\
 (!op. MEM op ps.ps_stack /\ op <> dead_stack_marker /\ op <> x ==> MEM op (MAP Var nl)) /\
 (!v. MEM v nl /\ v <> HD inst.inst_outputs ==> MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
 generate_phi_plan inst nl halting ps = (ops,qs) /\
 final = release_dead_spills nl qs
 ==>
 (!op. ((MEM op final.ps_stack /\ op <> dead_stack_marker) \/ op IN FDOM final.ps_spilled) <=> MEM op (MAP Var nl))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dead_phi_spilled_unchanged >> strip_tac >>
  `d < LENGTH ps.ps_stack` by
    (fs[stack_get_phi_depth_def] >> drule stack_find_bound >> simp[]) >>
  drule generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`nl`, `halting`] mp_tac) >>
  simp[phi_write_phase_def] >> strip_tac >>
  gvs[] >> simp[release_dead_spills_stack, phi_release_dead_spills_domain] >>
  gen_tac >> eq_tac
  >- (strip_tac
      >- (drule_at (Pos last) stack_poke_unique_inventory >> simp[] >> strip_tac >> gvs[] >>
          metis_tac[MEM_MAP]) >>
      metis_tac[MEM_MAP]) >>
  simp[MEM_MAP] >> strip_tac >> gvs[] >> rename1 `MEM v nl` >>
  `Var v <> dead_stack_marker` by simp[dead_stack_marker_def] >>
  Cases_on `v = HD inst.inst_outputs`
  >- (gvs[] >> disj1_tac >> simp[stack_poke_def, MEM_LUPDATE]) >>
  `Var v <> stack_peek d ps.ps_stack` by
    (strip_tac >> qpat_x_assum `Var v = _` (mp_tac o GSYM) >>
     disch_then SUBST_ALL_TAC >> gvs[operand_to_string_def]) >>
  `MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by metis_tac[] >>
  metis_tac[stack_poke_preserves_other_member]
QED
