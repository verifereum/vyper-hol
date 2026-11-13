(* Diagnostic only: the word forcing branch has a fixed instruction sequence.
   No production judgment is derived from a pointer twin. *)
Theory bodyFullToplevelWordDiagnostic
Ancestors
  bodySimFull fragGasSeqPtr exprLoweringProps emitHelperProps context
  compileEnv exprLowering fragExecMem fragExec venomInst list emitHelper

Theorem toplevel_word_load_code_diagnostic[local]:
  compile_expr cenv ty (TopLevelName ann nsid) sa =
    (LocatedValue ann p,sa) /\ is_word_type ann /\
  lower_value compile_expr cenv ty (TopLevelName ann nsid) sa = (op,sb) ==>
  compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
    p.ptr_location p.ptr_operand sa = (op,sb) /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >>
  `compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
     p.ptr_location p.ptr_operand sa = (op,sb)` by
    gvs[lower_value_def, comp_bind_def, unwrap_value_def] >>
  simp[] >>
  pop_assum mp_tac >>
  Cases_on `p.ptr_location` >>
  simp[compile_ptr_load_def, compile_imm_load_word_def] >>
  Cases_on `cenv.ce_is_ctor` >> Cases_on `cenv.ce_imm_alloca` >>
  simp[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
       emit_def, comp_return_def, comp_ignore_bind_def] >>
  rpt strip_tac >> gvs[emitted_insts_def, mk_inst_def, is_terminator_def, rich_listTheory.DROP_APPEND] >>
  `LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + 1) = 0` by decide_tac >>
  simp[mk_inst_def, is_terminator_def]
QED

(* t, G' and tn' are parameters, not witnesses chosen under !H.  The
   outstanding certificates are deliberately visible; pointer paths alone
   do not supply run_inst_seq_mem_ok. *)
Theorem toplevel_word_common_endpoint_diagnostic[local]:
  compile_expr cenv ty (TopLevelName ann nsid) sa =
    (LocatedValue ann p,sa) /\ is_word_type ann /\
  lower_value compile_expr cenv ty (TopLevelName ann nsid) sa = (op,sb) /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sa sb) s G' tn') ==>
  !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')
Proof
  strip_tac >> drule_all toplevel_word_load_code_diagnostic >> strip_tac >>
  rpt strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by gvs[EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (gvs[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    metis_tac[LENGTH_APPEND] >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` drule >> strip_tac >>
  drule_all run_inst_seq_gas_origin_ptr_path >> simp[]
QED
