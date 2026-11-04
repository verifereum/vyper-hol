(* Original cached ALLOCA: requested sizes are irrelevant on cache hits. *)
Theory lowerDloadSafetyAllocation
Ancestors
  lowerDloadSafetyRelation lowerDloadSafetyAdvance venomExecSemantics
  venomState finite_map

Theorem ld_cached_alloca_pair:
  ld_maps A f /\ inst.inst_outputs = [out] /\
  FLOOKUP f.lf_src.vs_allocas inst.inst_id = SOME (b,n) ==>
  ?c. FLOOKUP A (f.lf_serial,inst.inst_id) = SOME (b,c,n) /\
    FLOOKUP f.lf_tgt.vs_allocas inst.inst_id = SOME (c,n) /\
    exec_alloca inst f.lf_src szS = OK (update_var out (n2w b) f.lf_src) /\
    exec_alloca inst f.lf_tgt szT = OK (update_var out (n2w c) f.lf_tgt) /\
    ld_maps A (f with <|lf_src := update_var out (n2w b) f.lf_src;
                        lf_tgt := update_var out (n2w c) f.lf_tgt|>)
Proof
  strip_tac >> drule_all ld_maps_original >> strip_tac >>
  qexists_tac `c` >> simp[exec_alloca_def] >>
  irule ld_maps_cached_original >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`b`,`inst`,`n`,`szS`] >> simp[exec_alloca_def]
QED

Theorem ld_alloca_step:
  inst.inst_opcode = ALLOCA ==>
  (step_inst fuel C inst s = OK ss <=>
   ?sz. inst.inst_operands = [Lit sz] /\ exec_alloca inst s sz = OK ss)
Proof
  strip_tac >> simp[step_inst_non_invoke, Once step_inst_base_def] >>
  namedCases_on `inst.inst_operands` ["", "operand rest"] >> simp[] >>
  Cases_on `rest` >> simp[] >> Cases_on `operand` >> simp[]
QED
