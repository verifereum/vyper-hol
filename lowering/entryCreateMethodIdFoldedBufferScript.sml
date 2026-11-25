(* Folded dynamic MethodId has one installed literal-buffer run and no
   compiled argument. Its value and VV posts describe the same allocation. *)
Theory entryCreateMethodIdFoldedBuffer
Ancestors
  bodyFullBuiltinEnvMethodIdCompose bodyFullEmptyLeafData exprSimFullBundleProps
  entryCreateFocusSpec entryCreateAdminSequence entryIntCallStageNeutral
  entryCreateCompletedCut createSizeBuiltinBodyCode createSizeCutCode
  literalBufferOpcodeShape exprSimLiteralBuffer exprLoweringProps exprSimAbiGasBridge
  fragExec gasSummary gasExplicitSites
  s1PrefixDefs vyperStorageTrace vyperTypeBytesCrypto list

Triviality folded_buffer_code:
  compile_bytelike_literal bytes (LENGTH bytes) sa = (buf,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_id IN frag_ids sa sb /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts sa sb)
Proof
  strip_tac >> drule literal_bytelike_counted_shape >> strip_tac >>
  drule literal_bytelike_emitted_admin >> strip_tac >>
  `create_cut_code {} sa sb` by
    (mp_tac (Q.INST [`exits` |-> `{}`, `a` |-> `sa`, `n` |-> `LENGTH (bytes:word8 list)`, `bs` |-> `bytes`]
       create_bytelike_literal_cut_code) >> simp[]) >>
  `frag_code sa sb = emitted_insts sa sb` by
    fs[same_blocks_def, frag_code_def, emitted_blocks_def] >>
  fs[same_blocks_def, create_cut_code_def, EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]
QED

Triviality folded_buffer_outcome:
  ~s0.vs_halted /\ storage_trace_frame source /\
  (!tail. source (es with gas_obs := tail) = (res,es with gas_obs := tail)) /\
  (storage_trace_domain cx st0 es.storage_trace ==>
    ?t G' tn'. create_operand_full_scope sa sb E C f s0 [] (OK t) /\
      !H. valid_horizon cx st0 H es.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s0,G0,tn0) [] (OK t,G',tn') /\
        Q H res (es with gas_obs := []) G' tn' t) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 sa sb source (es,s0,G0,tn0) Q R
Proof
  strip_tac >> irule stage_scoped_initial_domain >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`,`es`,`OK t`,`G'`,`tn'`] >> simp[gas_explicit_def] >> metis_tac[]
QED

Triviality folded_buffer_vv_post:
  expr_vv_sim_full_post (DF,lo,d,ctx,func) ce cx e
    (es,sa,sb,s0,vv,G0,tn0) H res ee G tn t ==>
  create_operand_vv_post (DF,lo,d,ctx,func) ce cx e
    (es,sa,sb,s0,vv,G0,tn0) H res ee G tn t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  simp[expr_vv_sim_full_post_def,expr_sim_full_endpoint_def,create_operand_vv_post_def] >>
  strip_tac >> simp[] >> qexists_tac `tv` >> simp[]
QED

Theorem method_id_folded_buffer_sites:
  method_id_literal (Literal la l) = SOME bs ==>
  let e = Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l] in
  (!st0 sa sb sha shb op s0 G0 tn0.
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es
      (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
      (cx_tops cx) cx st0 sa sb (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
      (expr_sim_full_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s0,op,G0,tn0))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
      (bind (eval_expr cx e) (read_result cx)) (es,s0)) /\
  (!st0 sa sb sha shb vv s0 G0 tn0.
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es
      (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
      (cx_tops cx) cx st0 sa sb (eval_expr cx e) (es,s0,G0,tn0)
      (\H res ee G' tn' t.
        create_operand_vv_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s0,vv,G0,tn0)
          H res ee G' tn' t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (create_operand_exit_post ctx cx) /\
    create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
      (eval_expr cx e) (es,s0))
Proof
  simp_tac bool_ss [LET_THM,expr_sim_full_pre_def,expr_vv_sim_full_pre_def] >>
  strip_tac >> conj_tac >> rpt gen_tac >> strip_tac >>
  drule method_id_literal_dynamic_compiles >> strip_tac >> gvs[] >>
  `create_operand_at sa s0` by simp[create_operand_at_def] >>
  drule folded_buffer_code >> strip_tac >>
  (reverse conj_tac
   >- (irule create_admin_sequence_cut >> simp[] >> fs[EVERY_MEM])) >>
  drule method_id_literal_dynamic_source >> strip_tac >>
  irule folded_buffer_outcome >>
  simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_bind,
       vyperStorageTraceTheory.storage_trace_frame_read_result] >>
  rpt strip_tac >>
  drule_all method_id_literal_dynamic_selected_run >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shctx`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`raw with vs_inst_idx := LENGTH sb.cs_current_insts`,`G'`,`tn'`] >>
  (conj_tac
   >- (irule create_admin_sequence_scope >> simp[] >> fs[EVERY_MEM])) >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> LET _ _`
    (drule_then (strip_assume_tac o SIMP_RULE bool_ss [LET_THM])) >>
  FIRST [first_assum ACCEPT_TAC,
         (drule folded_buffer_vv_post >> simp[])]
QED
