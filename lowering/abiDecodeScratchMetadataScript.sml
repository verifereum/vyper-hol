(* Allocation provenance at the actual emitted scratch endpoint. *)
Theory abiDecodeScratchMetadata
Ancestors
  exprLoweringProps emitHelperProps fragExec venomExecSemantics venomState venomInst
  words finite_map list arithmetic

Theorem abi_decode_alloca_sequence_metadata:
  emit_op ALLOCA [Lit 32w] st = (out,st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) ==>
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!q. q <> st.cs_next_id ==>
    FLOOKUP t.vs_allocas q = FLOOKUP s.vs_allocas q) /\
  (case FLOOKUP s.vs_allocas st.cs_next_id of
     NONE => p = s.vs_alloca_next
   | SOME (b,sz) => p = b)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      eval_operand_def] >>
  Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >>
  gvs[exec_alloca_def, AllCaseEqs(), update_var_def, FLOOKUP_UPDATE]
QED
