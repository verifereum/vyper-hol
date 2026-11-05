(* The middle, taint-transferring segment of a storage copy body. *)
Theory exprPtrUnwrapStoreSegment
Ancestors
  exprPtrUnwrapCopyEdges fragGasSeqPtr fragExec ptrDiscipline ptrSafeRun
  venomExecSemantics venomInst venomState finite_map exprLoweringProps

Theorem copy_store_segment:
  ptr_covers G tn root s 32 /\
  eval_operand (Var root) s = SOME addr /\ eval_operand v s = SOME value /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq [mk_inst id MSTORE [Var root;v] []] s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn [mk_inst id MSTORE [Var root;v] []]
      s Gf tnf /\
    t = mstore (w2n addr) value s /\
    tnf.t_mem =
      (tn.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr + 32}) UNION
        {w2n addr + k | k IN op_taint tn v} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. FLOOKUP Gf p = FLOOKUP G p /\
         op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qexistsl_tac [`step_prov PG G (mk_inst id MSTORE [Var root;v] [])
    (mstore (w2n addr) value s)`,
    `step_taint (mk_inst id MSTORE [Var root;v] []) s
      (mstore (w2n addr) value s) tn`, `mstore (w2n addr) value s`] >>
  `step_inst_base (mk_inst id MSTORE [Var root;v] []) s =
    OK (mstore (w2n addr) value s)` by
    simp[step_inst_base_def, mk_inst_def, exec_write2_def] >>
  simp[run_inst_seq_def, inst_seq_ptr_def, ptr_inst_ok_mstore_tainted,
       mstore_transferred_taint] >>
  simp[step_prov_def, set_prov_def, step_taint_def, set_var_taint_def,
       store_taint_def, adopt_reset_def, mk_inst_def, op_taint_def,
       FLOOKUP_DRESTRICT]
QED
