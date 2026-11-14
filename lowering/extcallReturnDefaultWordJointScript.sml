(* The scalar default store has one explicit operational/ghost endpoint. *)
Theory extcallReturnDefaultWordJoint
Ancestors
  bodyFullUnwrapRun fragGasCopyLoop
  exprSimPtrTopLevelImmutableCopy allocaFootprint bodyPtrDefs
  extcallReturnDefaultStore exprSimBufferStore
  context emitHelperProps exprLoweringProps venomState venomInst venomExecSemantics ptrDiscipline fragExec
  finite_map list pred_set

Theorem return_default_word_store_joint:
  compile_store_memory ce src (Var dst) ty sty a = ((),b) /\
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  eval_operand src s = SOME w /\ w = typed_val_to_w256 tv v /\
  lookup_var dst s = SOME dw /\ ptr_covers G tn dst s 32 /\
  op_taint tn src = {} /\ ~ctx_has_dalloca ctx /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  allocas_from lo s /\ w2n dw + 32 <= s.vs_alloca_next ==>
  ?u tm.
    u = (mstore (w2n dw) w s) with vs_inst_idx := LENGTH b.cs_current_insts /\
    tm = tn with t_mem := tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32} /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK u,G,tm)) /\
    (!mem. mem_agree_outside tm.t_mem u.vs_memory mem ==>
       val_in_memory tv v (w2n dw) mem) /\
    (!op. eval_operand op u = eval_operand op s) /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + 32) ==>
       mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\
    u.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!op. op_taint tm op = op_taint tn op) /\
    (!lo ce es sa G0 tn0 s0.
       ghost_kept_at lo ce es sa G0 tn0 s0 G tn ==>
       ghost_kept_at lo ce es sa G0 tn0 s0 G tm)
Proof
  strip_tac >>
  `emit_void MSTORE [Var dst;src] a = ((),b)` by
    gvs[compile_store_memory_def] >>
  `emitted_insts a b = [mk_inst a.cs_next_id MSTORE [Var dst;src] []]` by
    (drule emitted_insts_emit_void >> simp[]) >>
  `step_inst_base (mk_inst a.cs_next_id MSTORE [Var dst;src] []) s =
     OK (mstore (w2n dw) w s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def] >>
  `step_prov PG G (mk_inst a.cs_next_id MSTORE [Var dst;src] [])
       (mstore (w2n dw) w s) = G /\
   step_taint (mk_inst a.cs_next_id MSTORE [Var dst;src] []) s
       (mstore (w2n dw) w s) tn =
       tn with t_mem := tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32}` by
    (irule toplevel_immutable_mstore_ghost_frame >> simp[]) >>
  qexistsl_tac [`(mstore (w2n dw) w s) with vs_inst_idx := LENGTH b.cs_current_insts`,
    `tn with t_mem := tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32}`] >>
  simp[] >> conj_tac >- suspend "path" >>
  conj_tac >- suspend "value" >>
  conj_tac >- suspend "exterior" >>
  simp[mstore_def, write_memory_with_expansion_def] >>
  conj_tac >- suspend "block" >>
  simp[op_taint_def, ghost_kept_at_def] >> metis_tac[]
QED
Resume return_default_word_store_joint[path]:
  gen_tac >>
  irule emitted_origin_ptr_path >> simp[] >>
  qexistsl_tac [`[mk_inst a.cs_next_id MSTORE [Var dst;src] []]`, `a`] >>
  simp[run_inst_seq_def] >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> simp[same_blocks_def] >> strip_tac >>
  simp[is_terminator_def] >>
  conj_tac >- (drule emit_mstore_mem_ok >> simp[eval_operand_def]) >>
  irule inst_seq_ptr_lower_bound_transport >>
  conj_tac >- simp[mk_inst_def] >> simp[] >>
  qexists_tac `0` >> simp[] >>
  gvs[fragGasSeqPtrTheory.inst_seq_ptr_def] >>
  irule fragExecPtrTheory.ptr_inst_ok_mstore >> simp[]
QED
Resume return_default_word_store_joint[value]:
  `eval_operand (Var dst) s = SOME dw` by simp[eval_operand_def] >>
  drule_all buffer_store_word_encoding >> strip_tac >>
  `q = mstore (w2n dw) w s` by gvs[run_inst_seq_def] >>
  `type_memory_size tv = 32` by metis_tac[stmtSimReturnTheory.word_type_sizes] >>
  rpt strip_tac >>
  irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
  conj_tac >- simp[] >>
  qexistsl_tac [`32`, `(mstore (w2n dw) w s).vs_memory`] >> gvs[] >>
  irule LIST_EQ >> simp[valueEncodingProofsTheory.EL_mem_bytes_at] >> rpt strip_tac >>
  qpat_x_assum `mem_agree_outside _ _ mem` mp_tac >>
  simp[mem_agree_outside_def] >>
  disch_then (qspec_then `w2n dw+x` mp_tac) >>
  simp[LIST_EQ_REWRITE,valueEncodingProofsTheory.EL_mem_bytes_at]
QED
Resume return_default_word_store_joint[exterior]:
  `eval_operand (Var dst) s = SOME dw` by simp[eval_operand_def] >>
  drule_all buffer_store_word_encoding >> strip_tac >>
  `q = mstore (w2n dw) w s` by gvs[run_inst_seq_def] >>
  `type_memory_size tv = 32` by metis_tac[stmtSimReturnTheory.word_type_sizes] >>
  gvs[] >> rpt strip_tac >> first_x_assum irule >> decide_tac
QED
Resume return_default_word_store_joint[block]:
  drule emit_void_same_blocks >> simp[same_blocks_def]
QED
Finalise return_default_word_store_joint
