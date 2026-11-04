(* Conditional sequential coverage for successful external calls. *)
Theory lowerDloadOracleCallCoverage
Ancestors
  lowerDloadOracleCallAssembly lowerDloadOracleCallSafety
  lowerDloadSafetyOrdinaryCoverage
  lowerDloadSafetyAmbient lowerDloadSafetyRelation lowerDloadSafetyKernel
  ptrDiscipline venomInst finite_map list

Theorem ld_sync_oracle_call_coverage:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\
  ptr_discipline lo C vs0 /\ mem_inv dload_headroom_ok C vs0 /\
  ~in_revert_forward fn s /\
  MEM inst.inst_opcode [CALL;STATICCALL] /\
  step_inst fuel C' inst t = OK ts /\
  active_inst (FST (lower_dload_function_supply f.lf_supply fn)) ti
    (ts with vs_inst_idx := SUC t.vs_inst_idx) /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
    list_precedes (EL j (f::fs)).lf_fn.fn_name
                  (EL k (f::fs)).lf_fn.fn_name names) ==>
  ld_pair lo P names Sigma C C' vs0 (ld_image f) ti
    (ts with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >>
  `f.lf_fn = fn` by (drule ld_sync_active >> simp[]) >>
  `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES /\
   ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    (qpat_assum `MEM inst.inst_opcode _` mp_tac >>
     simp[is_terminator_def] >> strip_tac >> gvs[is_terminator_def]) >>
  drule_all ld_sync_oracle_call_effect >> strip_tac >>
  `active_inst (ld_image f) ti (ts with vs_inst_idx := SUC t.vs_inst_idx)` by
    simp[ld_image_def] >>
  drule_all ld_sync_ordinary_coverage >> simp[]
QED
