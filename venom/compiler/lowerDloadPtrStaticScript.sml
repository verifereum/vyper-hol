Theory lowerDloadPtrStatic
Ancestors
  o1ContractLowerDload o1PassContract ptrDiscipline lowerDloadDefs
  venomPassSchedule list

(* A stage-level lifting boundary, also retaining the source membership
   required by consumers whose property depends on the input context. *)
Theorem lower_dload_stage_every:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  EVERY P C.ctx_functions /\
  (!f s g t. MEM f C.ctx_functions /\ P f /\
     lower_dload_function_supply s f = (g,t) ==> Q g) ==>
  EVERY Q C'.ctx_functions
Proof
  rw[ctx_pass_stage_def, EVERY_MEM, LIST_REL_EL_EQN, MEM_EL] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  impl_tac >- fs[] >> strip_tac >>
  gvs[fn_pass_step_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem lower_dload_function_no_dalloca:
  lower_dload_function_supply s f = (g,t) /\
  EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f) ==>
  EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts g)
Proof
  strip_tac >> irule lower_dload_function_supply_every >>
  conj_tac
  >- (rpt strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
      metis_tac[lower_dload_inst_supply_kept_dalloca]) >>
  qexistsl [`f`,`s`,`t`] >> simp[]
QED

Theorem lower_dload_stage_no_dalloca:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  ~ctx_has_dalloca C ==> ~ctx_has_dalloca C'
Proof
  simp[ctx_has_dalloca_def, GSYM EVERY_NOT_EXISTS] >> strip_tac >>
  irule lower_dload_stage_every >>
  qexistsl [`C`,`\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)`,
            `rpolicy`,`view`] >>
  pure_rewrite_tac[combinTheory.o_DEF, GSYM EVERY_NOT_EXISTS] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all lower_dload_function_no_dalloca >>
      simp[combinTheory.o_DEF]) >>
  fs[EVERY_MEM, EXISTS_MEM, combinTheory.o_DEF] >> metis_tac[]
QED
