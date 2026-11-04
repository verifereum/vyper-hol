(* Synchronized zero-prefix coverage and the grouped write consumer. *)
Theory lowerDloadSafetyWriteCoverage
Ancestors
  lowerDloadSafetyLocations lowerDloadSafetyWriteAdvance lowerDloadSafetyAmbient
  lowerDloadSafetyRelation lowerDloadSafetyKernel ptrDiscipline list

Theorem ld_pair_zero_witness:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  fn' = ld_image f /\ active_inst fn' ti t ==>
  ?X p. ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
    ld_prefix C' fn' X p 0 t t /\ ti = EL 0 X
Proof
  strip_tac >>
  `f.lf_src = s /\ f.lf_tgt = t /\ f.lf_fn = fn` by
    (drule ld_sync_active >> simp[]) >>
  `?X p. ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
         t.vs_inst_idx = p` by
    (qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ld_sync_def] >> simp[] >> strip_tac >>
     qpat_x_assum `!j. _ ==> ?X. ld_envelope _ _ _ _ X _`
       (qspec_then `0` mp_tac) >> simp[]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ld_sync_def] >> simp[] >> strip_tac >> simp[]) >>
  `active_inst (FST (lower_dload_function_supply f.lf_supply fn)) ti t` by
    gvs[ld_image_def] >>
  drule_all ld_envelope_active_head >> strip_tac >>
  qexistsl_tac [`X`,`p`] >>
  simp[ld_prefix_zero] >> Cases_on `X` >> gvs[]
QED

Theorem ld_pair_zero:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
     list_precedes (EL j (f::fs)).lf_fn.fn_name
                   (EL k (f::fs)).lf_fn.fn_name names) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  fn' = ld_image f /\ active_inst fn' ti t ==>
  ld_pair lo P names Sigma C C' vs0 fn' ti t
Proof
  strip_tac >> drule_all ld_pair_zero_witness >>
  disch_then (qspec_then `C'` strip_assume_tac) >>
  simp[ld_pair_def] >>
  qexistsl_tac [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`,`t`,`A`,`f::fs`,`N`,`X`,`p`,`0`] >>
  gvs[]
QED

Theorem ld_sync_memory_write_coverage:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ f.lf_src = s /\ f.lf_tgt = t /\ f.lf_fn = fn /\
  ptr_discipline lo C vs0 /\ fn_shape_ok fn /\ fn_inst_wf fn /\
  s.vs_labels = t.vs_labels /\ ~in_revert_forward fn s /\
  t.vs_alloca_next < dimword(:256) /\
  MEM inst.inst_opcode [MSTORE;MSTORE8;MCOPY] /\
  step_inst fuel C' inst t = OK ts /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
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
  `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES` by
    (qpat_assum `MEM inst.inst_opcode _` mp_tac >> simp[] >> strip_tac >> gvs[]) >>
  drule_all ld_sync_ordinary_envelope >> strip_tac >>
  `active_inst (FST (lower_dload_function_supply f.lf_supply fn)) ti
     (ts with vs_inst_idx := SUC p)` by metis_tac[] >>
  drule_all ld_sync_memory_write_advance >> strip_tac >>
  qabbrev_tac `newframe = f with
    <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
      lf_tgt := ts with vs_inst_idx := SUC p;
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

Theorem ld_sync_memory_write_coverage_ambient:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\
  ptr_discipline lo C vs0 /\ mem_inv dload_headroom_ok C vs0 /\
  ~in_revert_forward fn s /\
  MEM inst.inst_opcode [MSTORE;MSTORE8;MCOPY] /\
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
  drule ld_sync_labels >> strip_tac >>
  drule_all ld_sync_ambient_headroom >> strip_tac >>
  drule_all ld_sync_memory_write_coverage >> simp[]
QED
