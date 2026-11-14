(* Inversion for allocation-map lookups after a successful instruction. *)
Theory allocationLookup
Ancestors
  venomMemProps venomExecProofs venomExecSemantics venomState finite_map

Theorem step_inst_alloca_lookup_origin:
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK t /\
  FLOOKUP t.vs_allocas id = SOME (off,sz) ==>
  FLOOKUP s.vs_allocas id = SOME (off,sz) \/
  (inst.inst_opcode = ALLOCA /\ inst.inst_id = id /\
   ?w. inst.inst_operands = [Lit w] /\ sz = w2n w)
Proof
  strip_tac >>
  `step_inst_base inst s = OK t` by gvs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
      simp[Once step_inst_base_def, AllCaseEqs()] >> strip_tac >>
      gvs[exec_alloca_def, AllCaseEqs(), update_var_def, FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  metis_tac[step_inst_base_preserves_allocas]
QED
