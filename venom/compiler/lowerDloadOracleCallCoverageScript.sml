(* Live-successor coverage for external oracle calls. *)
Theory lowerDloadOracleCallCoverage
Ancestors
  lowerDloadOracleCallAssembly lowerDloadSafetyWriteCoverage
  lowerDloadSafetyLocations lowerDloadSafetyAdvance lowerDloadSafetyAmbient
  lowerDloadSafetyRelation lowerDloadSafetyKernel ptrDiscipline venomInst finite_map list

Theorem ld_sync_current_bb:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N ==>
  s.vs_current_bb = t.vs_current_bb
Proof
  simp[ld_sync_def] >> strip_tac >> gvs[]
QED

Theorem ld_sync_oracle_call_advance:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\
  ptr_discipline lo C vs0 /\ mem_inv dload_headroom_ok C vs0 /\
  ~in_revert_forward fn s /\ MEM inst.inst_opcode [CALL;STATICCALL] /\
  step_inst fuel C' inst t = OK ts /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\
  t.vs_inst_idx = p /\
  active_inst (FST (lower_dload_function_supply f.lf_supply fn)) ti
    (ts with vs_inst_idx := SUC p) ==>
  ?ss H' next. step_inst fuel C inst s = OK ss /\
    ld_sync lo P C vs0 stk PG (step_prov PG G inst ss)
      (step_taint inst s ss tn) fn next
      (ss with vs_inst_idx := SUC s.vs_inst_idx)
      (ts with vs_inst_idx := SUC p) A
      ((f with <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
                 lf_tgt := ts with vs_inst_idx := SUC p;
                 lf_H := H';
                 lf_tv := (step_taint inst s ss tn).t_var|>)::fs) N /\
    ld_global lo A
      ((f with <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
                 lf_tgt := ts with vs_inst_idx := SUC p;
                 lf_H := H';
                 lf_tv := (step_taint inst s ss tn).t_var|>)::fs)
Proof
  strip_tac >>
  drule_all ld_sync_oracle_call_effect >> strip_tac >>
  `f.lf_src = s /\ f.lf_tgt = t /\ f.lf_fn = fn` by
    (drule ld_sync_active >> simp[]) >>
  `ld_envelope f.lf_supply fn ss s.vs_inst_idx [inst] p` by
    (fs[ld_envelope_def] >> qexists_tac `bi` >> simp[]) >>
  `s.vs_current_bb = t.vs_current_bb` by
    (drule ld_sync_current_bb >> simp[]) >>
  `ts.vs_current_bb = ss.vs_current_bb` by simp[] >>
  drule_all ld_envelope_singleton_next >> strip_tac >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    (qpat_x_assum `MEM inst.inst_opcode _` mp_tac >>
     simp[is_terminator_def] >> strip_tac >> gvs[is_terminator_def]) >>
  `ld_vars P A (f with
      <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
        lf_tgt := ts with vs_inst_idx := SUC p; lf_H := H';
        lf_tv := (step_taint inst s ss tn).t_var|>)` by
    (mp_tac (ld_vars_inst_indices |> Q.INST
       [`f` |-> `f with <|lf_src := ss; lf_tgt := ts; lf_H := H';
                         lf_tv := (step_taint inst s ss tn).t_var|>`,
        `i` |-> `SUC s.vs_inst_idx`, `j` |-> `SUC p`]) >> simp[]) >>
  qexistsl_tac [`ss`,`H'`,`next`] >> conj_tac >- first_assum ACCEPT_TAC >>
  mp_tac (ld_sync_ordinary_advance |> Q.INST
    [`G'` |-> `step_prov PG G inst ss`,
     `tn'` |-> `step_taint inst s ss tn`,
     `f'` |-> `f with
       <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
         lf_tgt := ts with vs_inst_idx := SUC p; lf_H := H';
         lf_tv := (step_taint inst s ss tn).t_var|>`]) >>
  (impl_tac >-
    (simp[] >> qexists_tac `Y` >> first_assum ACCEPT_TAC)) >> simp[]
QED

Theorem ld_sync_oracle_call_coverage_ambient:
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
  `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES` by
    (qpat_assum `MEM inst.inst_opcode _` mp_tac >> simp[] >> strip_tac >> gvs[]) >>
  drule_all ld_sync_ordinary_envelope >> strip_tac >>
  `active_inst (FST (lower_dload_function_supply f.lf_supply fn)) ti
     (ts with vs_inst_idx := SUC p)` by metis_tac[] >>
  drule_all ld_sync_oracle_call_advance >> strip_tac >>
  qabbrev_tac `newframe = f with
    <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
      lf_tgt := ts with vs_inst_idx := SUC p; lf_H := H';
      lf_tv := (step_taint inst s ss tn).t_var|>` >>
  `EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (newframe::fs)` by
    (simp[Abbr `newframe`] >> fs[]) >>
  `!j. (EL j (newframe::fs)).lf_fn = (EL j (f::fs)).lf_fn` by
    (gen_tac >> Cases_on `j` >> simp[Abbr `newframe`]) >>
  `!j k. j < k /\ k < LENGTH (newframe::fs) ==>
     list_precedes (EL j (newframe::fs)).lf_fn.fn_name
                   (EL k (newframe::fs)).lf_fn.fn_name names` by
    (simp[] >> metis_tac[]) >>
  `ld_image f = ld_image newframe` by simp[Abbr `newframe`, ld_image_def] >>
  `active_inst (ld_image f) ti (ts with vs_inst_idx := SUC p)` by
    simp[ld_image_def, Abbr `newframe`] >>
  drule_all ld_pair_zero >> simp[]
QED
