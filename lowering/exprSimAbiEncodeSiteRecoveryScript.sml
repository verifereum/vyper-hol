Theory exprSimAbiEncodeSiteRecovery
Ancestors
  exprSimAbiEncodeSiteSyntax exprSimAbiEncodeSiteEncoder
  exprLoweringProps compileEnv context venomInst list

Theorem site_interval_instruction:
  site_step a b /\
  (!j. MEM j (frag_code a b) ==> MEM j (fn_insts fn)) /\
  ALL_DISTINCT (MAP (\j. j.inst_id) (fn_insts fn)) /\
  MEM i (fn_insts fn) /\
  a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id ==>
  MEM i (frag_code a b)
Proof
  strip_tac >> drule_all site_step_coverage >> strip_tac >>
  `i = i'` suffices_by metis_tac[] >>
  gvs[MEM_EL] >>
  metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP, EL_MAP]
QED

Theorem site_interval_alloca:
  site_step a b /\
  (!j. MEM j (frag_code a b) ==> MEM j (fn_insts fn)) /\
  ALL_DISTINCT (MAP (\j. j.inst_id) (fn_insts fn)) /\
  MEM i (fn_insts fn) /\
  a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id /\
  i.inst_opcode = ALLOCA ==>
  ?n. a.cs_next_var <= n /\ n < b.cs_next_var /\
      i.inst_operands = [Lit 32w] /\
      i.inst_outputs = [STRING #"%" (toString n)]
Proof
  metis_tac[site_interval_instruction, site_step_alloca]
QED

Theorem site_interval_alloca_not_local:
  site_step a b /\
  (!j. MEM j (frag_code a b) ==> MEM j (fn_insts fn)) /\
  ALL_DISTINCT (MAP (\j. j.inst_id) (fn_insts fn)) /\
  MEM i (fn_insts fn) /\
  a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id /\
  i.inst_opcode = ALLOCA /\ local_ptrs_reserved cenv a ==>
  ?p. i.inst_operands = [Lit 32w] /\ i.inst_outputs = [p] /\
      not_local_ptr cenv scopes p
Proof
  metis_tac[site_interval_alloca, local_ptrs_reserved_fresh]
QED
