(* Literal transient stores preserve provenance and clear the written key's taint. *)
Theory transientLockPtr
Ancestors
  transientLockProps fragGasSeqPtr stmtAppendStorageRunPtr
  ptrSafeRun ptrDiscipline contextCodegenRel codegenRel venomExecSemantics venomInst venomState

Theorem literal_tstore_inst_seq_ptr_at:
  ~ctx_has_dalloca ctx /\ ~ss.vs_call_ctx.cc_static /\
  allocas_from lo ss ==>
  inst_seq_ptr D lo ctx func PG G tn
    [mk_inst id TSTORE [Lit key; Lit value] []] ss G
    (tn with t_trans := key_update tn.t_trans key {})
Proof
  strip_tac >>
  `step_inst_base (mk_inst id TSTORE [Lit key; Lit value] []) ss =
     OK (tstore key value ss)` by simp[step_TSTORE_lit] >>
  `ptr_inst_ok D lo 0 ctx func G tn
     (mk_inst id TSTORE [Lit key; Lit value] []) ss` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       mk_inst_def, op_taint_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, step_TSTORE_lit,
          tstore_def] >> rpt strip_tac >> gvs[]) >>
  `step_taint (mk_inst id TSTORE [Lit key; Lit value] []) ss
     (tstore key value ss) tn =
     tn with t_trans := key_update tn.t_trans key {}` by
    (mp_tac (Q.INST [`tr` |-> `T`, `a` |-> `Lit key`,
       `v` |-> `Lit value`, `slot` |-> `key`, `s` |-> `ss`,
       `s'` |-> `tstore key value ss`]
       (SPEC_ALL scalar_storage_store_taint)) >>
     simp[eval_operand_def, op_taint_def, tstore_def]) >>
  simp[inst_seq_ptr_def, scalar_void_prov]
QED
