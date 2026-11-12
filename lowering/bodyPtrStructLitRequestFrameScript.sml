(* Symbolic ordinary-step request frame. Opcode branch equations avoid
   repeatedly rebuilding the large step_inst_base opcode dispatch. *)
Theory bodyPtrStructLitRequestFrame
Ancestors venomExecSemantics venomState venomInst finite_map list

Theorem structlit_ordinary_step_requests:
  !i s t. MEM i.inst_opcode [ALLOCA;MSTORE;MLOAD;ADD;AND;MCOPY] /\
    step_inst_base i s = OK t ==> t.vs_requests = s.vs_requests
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  gvs[step_inst_base_opcode_eqs] >>
  gvs[exec_alloca_def, exec_pure2_def, exec_read1_def, exec_write2_def,
      AllCaseEqs()] >>
  simp[mcopy_def, mload_def, mstore_def, update_var_def]
QED
