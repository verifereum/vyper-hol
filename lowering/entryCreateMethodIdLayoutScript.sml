(* Static straight-line layout of the MethodId runtime suffix. *)
Theory entryCreateMethodIdLayout
Ancestors
  entryCreateBuiltinHashSupport entryCreateAdminSequence
  exprSimHash builtinHashing createSizeCutCode exprLoweringProps
  logInstSeqPtr emitHelper compileEnv venomInst venomState venomExecSemantics list

(* The suffix after hashing is a single straight-line fragment.  The
   hash/selector intermediate states remain explicit in the caller's
   compiler equations; this lemma records the fragment boundary itself. *)
Theorem method_id_runtime_admin_layout:
  !ty x fixed sm op sb hash sh.
    compile_method_id_runtime ty x fixed sm = (op,sb) /\
    compile_method_id_hash ty x sm = (hash,sh) ==>
      same_blocks sh sb /\
      sb.cs_current_insts = sh.cs_current_insts ++ emitted_insts sh sb /\
      EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (emitted_insts sh sb)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all method_id_tail_shape >> simp[same_blocks_def]
QED

Theorem method_id_runtime_counted_concat:
  !xs ys s m t.
    run_inst_seq xs s = OK m /\
    run_inst_seq ys (m with vs_inst_idx := s.vs_inst_idx + LENGTH xs) = OK t /\
    EVERY (\i. ~is_terminator i.inst_opcode) ys ==>
    run_inst_seq (xs ++ ys) s = OK (t with vs_inst_idx := m.vs_inst_idx)
Proof
  rpt strip_tac >> irule run_inst_seq_append_advanced >> metis_tac[]
QED
