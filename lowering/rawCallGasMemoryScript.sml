(* The optional GAS instruction in the raw_call prefix, on its concrete run. *)
Theory rawCallGasMemory
Ancestors
  rawCallArgumentMemory bodyMemBiMethodIdSuffix fragGasMode fragGasPathMem
  fragExecMem instMemFrontier entrySinkExtraction emitHelperProps emitHelper
  context compileEnv venomState venomExecSemantics venomInst rich_list
  exprSimHash exprLoweringProps memSafeRun gasOutcome gasSummary gasSummaryCompose gasExemptCert
  vyperInterpreter vyperState

Theorem raw_call_optional_gas_counted_mem:
  (case go of SOME g => (g,sa) | NONE => emit_op GAS [] sa) = (gas,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path_mem ctx func s (if IS_NONE go then 1 else 0)
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  s.vs_alloca_next = t.vs_alloca_next
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) =
     (if IS_NONE go then 1 else 0) /\
   run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (Cases_on `go` >> gvs[]
     >- (drule emitted_insts_emit_op >> strip_tac >> simp[] >>
         simp[mk_inst_def, is_terminator_def, run_inst_seq_mem_ok_last,
              inst_dload_in_section_def] >>
         conj_tac
         >- (qpat_x_assum `emit_op GAS [] sa = _` mp_tac >>
             simp[emit_op_def, comp_bind_def, comp_ignore_bind_def,
                  comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
             rpt strip_tac >> gvs[]) >>
         irule below_frontier_no_ranges >> simp[]) >>
     simp[emitted_insts_def, run_inst_seq_def, run_inst_seq_mem_ok_def]) >>
  drule_all method_id_run_path_mem >>
  simp[gas_marked_path_def] >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  simp[] >>
  qpat_x_assum `(case go of NONE => _ | SOME g => _) = _` mp_tac >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  Cases_on `go` >> gvs[]
  >- (drule emitted_insts_emit_op >> strip_tac >>
      gvs[run_inst_seq_def, step_inst_def, step_GAS, update_var_def]) >>
  gvs[emitted_insts_def, run_inst_seq_def]
QED

Theorem raw_call_implicit_mem_suffix:
  gas_path_mem ctx func s n (OK t) /\ es.gas_obs = [] /\
  gas_outcome T tops (ctx,func) k (es,t) Q R ==>
  gas_outcome T tops (ctx,func) k (es,s) Q R
Proof
  strip_tac >>
  `es with gas_obs := [] = es` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `gas_marked_exec T (ctx,func) (return ()) (es,s) (REPLICATE n F) (INL ()) es (OK t)` by
    simp[gas_marked_exec_def, return_def, gas_marked_path_def] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  simp[gas_outcome_def] >> strip_tac
  >- (fs[gas_summary_at_def] >>
      `gas_marked_exec T (ctx,func) (bind (return ()) (\u. k))
         (es,s) (REPLICATE n F ++ marks) res es_end r` by
        (irule gas_marked_exec_bind_normal >>
         qexistsl_tac [`es`, `t`, `()`] >> gvs[]) >>
      qexists_tac `REPLICATE n F ++ marks` >> disj1_tac >>
      fs[bind_return] >> simp[gas_summary_at_def] >> metis_tac[]) >>
  `gas_exempt_cert T tops (ctx,func)
     (bind (return ()) (\u. ignore_bind k (return ())))
     (es,s) (REPLICATE n F ++ marks) (err,ee) (leaf,finish')` by
    (irule gas_exempt_cert_bind_unit >>
     qexistsl_tac [`es`, `t`, `()`] >> simp[]) >>
  qexists_tac `REPLICATE n F ++ marks` >> disj2_tac >> fs[bind_return] >> metis_tac[]
QED
