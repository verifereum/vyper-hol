(* Shared address-position facts for invoke copy forwarding consumers.
   These live above memLocDefs because the use classification depends on
   icf_is_assign_output_use. *)
Theory invokeCopyFwdMemoryUses
Ancestors
  invokeCopyFwdCommonDefs memLocDefs list

Theorem icf_read_address_position:
  mem_read_ops inst = SOME ops ==>
  inst.inst_opcode <> INVOKE /\
  ?p. p < LENGTH inst.inst_operands /\ EL p inst.inst_operands = ops.iao_ofst /\
    ~icf_is_assign_output_use inst p /\ ~(inst.inst_opcode = MCOPY /\ p = 0)
Proof
  Cases_on `inst.inst_opcode` >>
  simp[mem_read_ops_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[icf_is_assign_output_use_def] >>
  FIRST_PROVE (map (fn q => qexists_tac q >> simp[])
    [`0`,`1`,`2`,`3`,`4`,`5`] @
    [metis_tac[MEM_EL, MEM_REVERSE, MEM]])
QED

Theorem icf_write_address_position:
  mem_write_ops inst = SOME ops ==>
  inst.inst_opcode <> INVOKE /\
  ?p. p < LENGTH inst.inst_operands /\ EL p inst.inst_operands = ops.iao_ofst /\
    ~icf_is_assign_output_use inst p
Proof
  Cases_on `inst.inst_opcode` >>
  simp[mem_write_ops_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[icf_is_assign_output_use_def] >>
  FIRST_PROVE (map (fn q => qexists_tac q >> simp[])
    [`0`,`1`,`2`,`3`,`4`,`5`])
QED
