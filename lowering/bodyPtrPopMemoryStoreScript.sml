Theory bodyPtrPopMemoryStore
Ancestors
  wordLoadStorePtr
  exprSimPtrProps typedCopyPtr fragExecPtr fragExec fragGasPathPtr bodyPtrDefs
  emitHelperProps emitHelper compileEnv venomInst venomState venomExecSemantics
  ptrDiscipline ptrSafeRun decoderGhostFramePtr codegenRel contextCodegenRel
  finite_map pred_set list

Theorem pop_emit_mstore_path:
  emit_void MSTORE [Var dst; value] sa = ((),sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn dst s 32 /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G tn' (OK t) /\
    t = ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!v. lookup_var v t = lookup_var v s) /\
    tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    mem_agree_outside {i | w2n a <= i /\ i < w2n a + 32}
      t.vs_memory s.vs_memory
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_void_def, emit_inst_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id MSTORE [Var dst; value] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst sa.cs_next_id MSTORE [Var dst; value] []) s =
     OK (mstore (w2n a) w s)` by
    (irule step_MSTORE >> simp[eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
      (mk_inst sa.cs_next_id MSTORE [Var dst; value] []) s` by
    (irule ptr_inst_ok_mstore >> simp[]) >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `sa.cs_next_id`] strip_assume_tac) >>
  qexistsl_tac [`(mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_taint (mk_inst sa.cs_next_id MSTORE [Var dst; value] []) s
       (mstore (w2n a) w s) tn`] >>
  conj_tac
  >- (`gas_path_ptr D 0 ctx fn PG G tn s 0
         (step_prov PG G (mk_inst sa.cs_next_id MSTORE [Var dst; value] [])
            (mstore (w2n a) w s))
         (step_taint (mk_inst sa.cs_next_id MSTORE [Var dst; value] []) s
            (mstore (w2n a) w s) tn)
         (OK ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx))` by
        (irule gas_path_ptr_one_step >>
         simp[mk_inst_def, is_terminator_def, mstore_def] >>
         fs[mk_inst_def]) >>
      gvs[]) >>
  `mem_agree_outside {i | w2n a <= i /\ i < w2n a + 32}
     (mstore (w2n a) w s).vs_memory s.vs_memory` by
    irule mstore_memory_frame >>
  `(step_taint (mk_inst sa.cs_next_id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn).t_imm = tn.t_imm` by
    (irule (cj 3 step_taint_nonmemory_frame) >> simp[mk_inst_def]) >>
  simp[lookup_var_def, mstore_def] >> gvs[mstore_def]
QED

Theorem pop_clean_header_store_path:
  emit_void MSTORE [Var dst; value] sa = ((),sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn dst s 32 /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ?t. gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK t) /\
    t = ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!v. lookup_var v t = lookup_var v s) /\
    mem_agree_outside {i | w2n a <= i /\ i < w2n a + 32}
      t.vs_memory s.vs_memory /\
    (!bytes. ptr_covers G tn dst s bytes ==> ptr_covers G tn dst t bytes)
Proof
  strip_tac >> drule_all pop_emit_mstore_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `tn'.t_mem = tn.t_mem` by
    (gvs[EXTENSION] >> metis_tac[]) >>
  `tn' = tn` by simp[taint_component_equality] >> gvs[] >>
  rpt strip_tac >>
  gvs[ptr_covers_def, lookup_var_def, mstore_def]
QED
