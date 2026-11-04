(* Conditional sequential coverage for successful external calls. *)
Theory lowerDloadOracleCallCoverage
Ancestors
  lowerDloadOracleCallAssembly lowerDloadOracleCallSafety
  lowerDloadSafetyWriteCoverage lowerDloadSafetyAdvance lowerDloadSafetyLocations
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
  `f.lf_src = s /\ f.lf_tgt = t /\ f.lf_fn = fn` by
    (drule ld_sync_active >> simp[]) >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES /\
   ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    (qpat_assum `MEM inst.inst_opcode _` mp_tac >>
     simp[is_terminator_def] >> strip_tac >> gvs[is_terminator_def]) >>
  drule_all ld_sync_ordinary_envelope >> strip_tac >>
  drule_all ld_sync_oracle_call_effect >> strip_tac >>
  `ld_envelope f.lf_supply fn ss s.vs_inst_idx [inst] p` by
    (fs[ld_envelope_def] >> qexists_tac `bi` >> simp[]) >>
  `ts.vs_current_bb = ss.vs_current_bb` by
    (drule ld_sync_control >> simp[]) >>
  `active_inst (FST (lower_dload_function_supply f.lf_supply fn)) ti
     (ts with vs_inst_idx := SUC p)` by metis_tac[] >>
  drule_all ld_envelope_singleton_next >> strip_tac >>
  qabbrev_tac `postframe = f with <|lf_src := ss; lf_tgt := ts; lf_H := H';
      lf_tv := (step_taint inst s ss tn).t_var|>` >>
  qabbrev_tac `newframe = postframe with
    <|lf_src := postframe.lf_src with vs_inst_idx := SUC s.vs_inst_idx;
      lf_tgt := postframe.lf_tgt with vs_inst_idx := SUC p|>` >>
  `ld_vars P A newframe` by
    (simp[Abbr `newframe`, ld_vars_inst_indices, Abbr `postframe`]) >>
  `ld_sync lo P C vs0 stk PG (step_prov PG G inst ss)
     (step_taint inst s ss tn) fn next
     (ss with vs_inst_idx := SUC s.vs_inst_idx)
     (ts with vs_inst_idx := SUC p) A (newframe::fs) N /\
   ld_global lo A (newframe::fs)` by
    (irule ld_sync_ordinary_advance >>
     simp[] >>
     goal_assum (drule_at Any) >>
     simp[Abbr `newframe`, Abbr `postframe`] >>
     metis_tac[]) >>
  `EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (newframe::fs)` by
    (simp[Abbr `newframe`, Abbr `postframe`] >> fs[]) >>
  `!j. (EL j (newframe::fs)).lf_fn = (EL j (f::fs)).lf_fn` by
    (gen_tac >> Cases_on `j` >> simp[Abbr `newframe`, Abbr `postframe`]) >>
  `!j k. j < k /\ k < LENGTH (newframe::fs) ==>
     list_precedes (EL j (newframe::fs)).lf_fn.fn_name
                   (EL k (newframe::fs)).lf_fn.fn_name names` by
    (simp[] >> metis_tac[]) >>
  `ld_image f = ld_image newframe` by
    simp[Abbr `newframe`, Abbr `postframe`, ld_image_def] >>
  `active_inst (ld_image f) ti (ts with vs_inst_idx := SUC p)` by
    simp[Abbr `newframe`, Abbr `postframe`, ld_image_def] >>
  drule_all ld_pair_zero >> simp[]
QED
