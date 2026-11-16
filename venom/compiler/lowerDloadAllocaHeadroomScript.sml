Theory lowerDloadAllocaHeadroom
Ancestors
  o1LowerDloadReadiness venomExecSemantics venomState venomInst
  venomWf lowerDloadDefs unitMemInv contextRawReachable
  contextCodegenRel finite_map words list

(* Successful original ALLOCA steps require literal syntax; evaluation of
   a variable to a clean/equal scalar does not suffice. *)
Theorem ld_alloca_malformed_failure:
  i.inst_opcode = ALLOCA /\ (~?n. i.inst_operands = [Lit n]) ==>
  step_inst fuel C i s = Error "alloca requires 1 literal operand"
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  Cases_on `i.inst_operands` >> simp[] >>
  rename1 `h::t` >> Cases_on `t` >> simp[] >>
  Cases_on `h` >> gvs[]
QED

Theorem ld_alloca_source_future_headroom:
  wf_function fn /\ mem_inv dload_headroom_ok C vs0 /\
  raw_reachable vs0 C fn i s /\ active_inst fn i s /\
  i.inst_opcode = ALLOCA /\ i.inst_operands = [Lit n] /\
  i.inst_outputs = [out] ==>
  ?s1. step_inst fuel C i s = OK s1 /\
    s1.vs_alloca_next + 32 * ctx_dload_count C < dimword(:256) /\
    (FLOOKUP s.vs_allocas i.inst_id = NONE ==>
      s.vs_alloca_next + w2n n + 32 * ctx_dload_count C < dimword(:256)) /\
    (FLOOKUP s.vs_allocas i.inst_id <> NONE ==>
      s1.vs_alloca_next = s.vs_alloca_next)
Proof
  strip_tac >>
  `?s1. step_inst fuel C i s = OK s1 /\
     (FLOOKUP s.vs_allocas i.inst_id = NONE ==>
       s1.vs_alloca_next = s.vs_alloca_next + w2n n) /\
     (FLOOKUP s.vs_allocas i.inst_id <> NONE ==>
       s1.vs_alloca_next = s.vs_alloca_next)` by
    (simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_alloca_def] >>
     Cases_on `FLOOKUP s.vs_allocas i.inst_id` >>
     simp[update_var_def] >> PairCases_on `x` >> simp[update_var_def]) >>
  drule_all ld_alloca_successor_active >> strip_tac >>
  `~is_terminator i.inst_opcode` by simp[is_terminator_def] >>
  `s1.vs_alloca_next + 32 * ctx_dload_count C < dimword(:256)` by
    (drule_all ld_next_headroom >> simp[is_terminator_def]) >>
  qexists_tac `s1` >> gvs[] >> strip_tac >> gvs[]
QED

(* Under DALLOCA, the source's frontier after an original ALLOCA still
   leaves the DLOAD headroom below the initial free memory pointer. *)
Theorem ld_alloca_source_dyn_headroom:
  wf_function fn /\ mem_inv dload_headroom_ok C vs0 /\
  raw_reachable vs0 C fn i s /\ active_inst fn i s /\
  i.inst_opcode = ALLOCA /\ step_inst fuel C i s = OK s1 /\
  EXISTS (\f. EXISTS (\i. i.inst_opcode = DALLOCA) (fn_insts f))
    C.ctx_functions ==>
  s1.vs_alloca_next + 32 * ctx_dload_count C <= w2n s1.vs_initial_fmp
Proof
  strip_tac >>
  drule_all ld_alloca_successor_active >> strip_tac >>
  `~is_terminator i.inst_opcode` by simp[is_terminator_def] >>
  `raw_reachable vs0 C fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    metis_tac[raw_reachable_next] >>
  qpat_x_assum `mem_inv _ _ _` mp_tac >>
  simp[mem_inv_raw_reachable, dload_headroom_ok_def] >> strip_tac >>
  first_x_assum (qspecl_then [`fn`, `inst2`,
    `s1 with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[]
QED
