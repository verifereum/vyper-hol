(* Opcode-independent ghost frames and clean-write boundaries. *)
Theory decoderGhostFramePtr
Ancestors bodyPtrDefs ptrDiscipline venomInst venomState finite_map pred_set list

Theorem step_prov_other_output:
  ~MEM x inst.inst_outputs ==>
  FLOOKUP (step_prov PG G inst t) x = FLOOKUP G x
Proof
  simp[step_prov_def, set_prov_def] >>
  Cases_on `inst.inst_outputs` >> simp[FLOOKUP_DRESTRICT] >>
  Cases_on `t'` >> simp[FLOOKUP_DRESTRICT] >>
  Cases_on `out_prov PG G inst t` >>
  simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem step_taint_other_output:
  ~MEM x inst.inst_outputs ==>
  op_taint (step_taint inst s t tn) (Var x) = op_taint tn (Var x)
Proof
  simp[step_taint_def, op_taint_def, set_var_taint_def] >>
  Cases_on `inst.inst_outputs` >> simp[FLOOKUP_DRESTRICT] >>
  rename1 `inst.inst_outputs = h::outs` >>
  Cases_on `outs` >> simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem step_taint_memory_bound:
  new_site_bytes s t SUBSET R /\ written_taint tn inst s SUBSET R ==>
  (step_taint inst s t tn).t_mem SUBSET tn.t_mem UNION R
Proof
  simp[step_taint_def, mem_taint_def] >> SET_TAC[]
QED

Theorem step_taint_clean_write:
  written_taint tn inst s = {} ==>
  DISJOINT (range_bytes (step_writes inst s t))
    (step_taint inst s t tn).t_mem
Proof
  simp[step_taint_def, mem_taint_def] >> SET_TAC[]
QED

Theorem ptr_covers_step_frame:
  ptr_covers G tn x s C /\ ~MEM x inst.inst_outputs /\
  lookup_var x t = lookup_var x s ==>
  ptr_covers (step_prov PG G inst t) (step_taint inst s t tn) x t C
Proof
  simp[ptr_covers_def, step_prov_other_output, step_taint_other_output]
QED

Theorem step_taint_nonmemory_frame:
  inst.inst_opcode <> CALL /\ inst.inst_opcode <> SSTORE /\
  inst.inst_opcode <> TSTORE /\ inst.inst_opcode <> ISTORE ==>
  (step_taint inst s t tn).t_stor = tn.t_stor /\
  (step_taint inst s t tn).t_trans = tn.t_trans /\
  (step_taint inst s t tn).t_imm = tn.t_imm
Proof
  simp[step_taint_def, adopt_reset_def, store_taint_def, imm_taint_def]
QED
