(* Complementary raw and checked execution facts for emitted scalar singletons.
   Gas paths use the same explicit witnesses from emit_op_zero_path_ptr. *)
Theory abiDecodePtrEmit
Ancestors
  emitHelper emitHelperProps exprLoweringProps fragExec fragGasSeqPtr ptrDiscipline
  venomExecSemantics venomInst venomState

Theorem emit_op_raw_checked_ptr:
  emit_op opc args sa = (op,sb) /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  (!out. ptr_inst_ok D lo 0 ctx func G tn
    (mk_inst sa.cs_next_id opc args [out]) s) /\
  (!out. step_inst_base (mk_inst sa.cs_next_id opc args [out]) s =
    OK (update_var out w s)) ==>
  !out. op = Var out ==>
    run_inst_seq (emitted_insts sa sb) s = OK (update_var out w s) /\
    inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s
      (step_prov PG G (mk_inst sa.cs_next_id opc args [out]) (update_var out w s))
      (step_taint (mk_inst sa.cs_next_id opc args [out]) s (update_var out w s) tn)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  rpt strip_tac >> gvs[] >> simp[run_inst_seq_def, inst_seq_ptr_def]
QED
