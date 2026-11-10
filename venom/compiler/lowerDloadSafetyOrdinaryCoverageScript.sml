(* Opcode-independent assembly of ordinary effects and successor locations. *)
Theory lowerDloadSafetyOrdinaryCoverage
Ancestors
  lowerDloadSafetyWriteCoverage lowerDloadSafetyAdvance lowerDloadSafetyLocations
  lowerDloadSafetyAmbient lowerDloadSafetyRelation lowerDloadSafetyKernel
  ptrDiscipline venomInst finite_map list

Theorem ld_sync_ordinary_witness:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\
  inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C' inst t = OK ts /\
  active_inst (ld_image f) ti (ts with vs_inst_idx := SUC t.vs_inst_idx) /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
    list_precedes (EL j (f::fs)).lf_fn.fn_name
                  (EL k (f::fs)).lf_fn.fn_name names) /\
  step_inst fuel C inst s = OK ss /\
  ld_vars P A (f with <|lf_src := ss; lf_tgt := ts; lf_H := H';
    lf_tv := (step_taint inst s ss tn).t_var|>) /\
  ld_memory lo A (step_taint inst s ss tn) ss ts /\
  ld_nonghost (step_taint inst s ss tn) ss ts /\
  step_prov PG G inst ss = ld_erase A o_f H' /\
  (!a. a IN FRANGE H' ==> a IN FDOM A) /\
  ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
  ss.vs_alloca_next = s.vs_alloca_next /\ ts.vs_alloca_next = t.vs_alloca_next /\
  ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
  ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb ==>
  ?newframe next X p h.
    newframe.lf_fn = f.lf_fn /\ newframe.lf_Q = f.lf_Q /\
    ld_sync lo P C vs0 stk PG (step_prov PG G inst ss)
      (step_taint inst s ss tn) fn next
      (ss with vs_inst_idx := SUC s.vs_inst_idx)
      (ts with vs_inst_idx := SUC t.vs_inst_idx) A (newframe::fs) N /\
    ld_global lo A (newframe::fs) /\
    EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (newframe::fs) /\
    (!j k. j < k /\ k < LENGTH (newframe::fs) ==>
      list_precedes (EL j (newframe::fs)).lf_fn.fn_name
                    (EL k (newframe::fs)).lf_fn.fn_name names) /\
    ld_image f = ld_image (HD (newframe::fs)) /\
    ld_envelope (HD (newframe::fs)).lf_supply fn
      (ss with vs_inst_idx := SUC s.vs_inst_idx) (SUC s.vs_inst_idx) X p /\
    ld_prefix C' (ld_image f) X p h
      (ts with vs_inst_idx := SUC t.vs_inst_idx)
      (ts with vs_inst_idx := SUC t.vs_inst_idx) /\ ti = EL h X
Proof
  strip_tac >>
  `f.lf_src = s /\ f.lf_tgt = t /\ f.lf_fn = fn` by
    (drule ld_sync_active >> simp[]) >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  drule_all ld_sync_ordinary_envelope >> strip_tac >>
  `ld_envelope f.lf_supply fn ss s.vs_inst_idx [inst] p` by
    (fs[ld_envelope_def] >> qexists_tac `bi` >> simp[]) >>
  `ts.vs_current_bb = ss.vs_current_bb` by
    (drule ld_sync_control >> simp[]) >>
  `active_inst (FST (lower_dload_function_supply f.lf_supply fn)) ti
     (ts with vs_inst_idx := SUC p)` by
    (qpat_x_assum `active_inst (ld_image f) _ _` mp_tac >> simp[ld_image_def]) >>
  drule_all (SRULE [GSYM arithmeticTheory.ADD1] (Q.INST [`X` |-> `[inst]`] ld_envelope_expansion_next)) >>
  strip_tac >>
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
    (irule ld_sync_ordinary_advance >> simp[] >>
     goal_assum (drule_at Any) >>
     simp[Abbr `newframe`, Abbr `postframe`] >> metis_tac[]) >>
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
  `active_inst (FST (lower_dload_function_supply f.lf_supply fn)) ti
     (ts with vs_inst_idx := SUC p)` by simp[ld_image_def] >>
  `(ts with vs_inst_idx := SUC p).vs_current_bb =
     (ss with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb /\
   (ts with vs_inst_idx := SUC p).vs_inst_idx = SUC p` by simp[] >>
  drule_all ld_envelope_active_head >> strip_tac >>
  qexistsl_tac [`newframe`,`next`,`Y`,`SUC p`,`0`] >>
  simp[ld_prefix_zero, Abbr `newframe`, Abbr `postframe`] >>
  Cases_on `Y` >> gvs[]
QED

(* Compatibility projection: no reconstruction of successor frames. *)
Theorem ld_sync_ordinary_coverage:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\
  inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C' inst t = OK ts /\
  active_inst (ld_image f) ti (ts with vs_inst_idx := SUC t.vs_inst_idx) /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
    list_precedes (EL j (f::fs)).lf_fn.fn_name
                  (EL k (f::fs)).lf_fn.fn_name names) /\
  step_inst fuel C inst s = OK ss /\
  ld_vars P A (f with <|lf_src := ss; lf_tgt := ts; lf_H := H';
    lf_tv := (step_taint inst s ss tn).t_var|>) /\
  ld_memory lo A (step_taint inst s ss tn) ss ts /\
  ld_nonghost (step_taint inst s ss tn) ss ts /\
  step_prov PG G inst ss = ld_erase A o_f H' /\
  (!a. a IN FRANGE H' ==> a IN FDOM A) /\
  ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
  ss.vs_alloca_next = s.vs_alloca_next /\ ts.vs_alloca_next = t.vs_alloca_next /\
  ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
  ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb ==>
  ld_pair lo P names Sigma C C' vs0 (ld_image f) ti
    (ts with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >> drule_all ld_sync_ordinary_witness >> strip_tac >>
  simp[ld_pair_def] >>
  qexistsl_tac [`stk`,`PG`,`step_prov PG G inst ss`,
    `step_taint inst s ss tn`,`fn`,`next`,
    `ss with vs_inst_idx := SUC s.vs_inst_idx`,
    `ts with vs_inst_idx := SUC t.vs_inst_idx`,
    `A`,`newframe::fs`,`N`,`X`,`p`,`h`] >> gvs[]
QED

Theorem ld_sync_ordinary_owned_coverage:
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) (f::fs) ==>
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\
  inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C' inst t = OK ts /\
  active_inst (ld_image f) ti (ts with vs_inst_idx := SUC t.vs_inst_idx) /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
    list_precedes (EL j (f::fs)).lf_fn.fn_name
                  (EL k (f::fs)).lf_fn.fn_name names) /\
  step_inst fuel C inst s = OK ss /\
  ld_vars P A (f with <|lf_src := ss; lf_tgt := ts; lf_H := H';
    lf_tv := (step_taint inst s ss tn).t_var|>) /\
  ld_memory lo A (step_taint inst s ss tn) ss ts /\
  ld_nonghost (step_taint inst s ss tn) ss ts /\
  step_prov PG G inst ss = ld_erase A o_f H' /\
  (!a. a IN FRANGE H' ==> a IN FDOM A) /\
  ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
  ss.vs_alloca_next = s.vs_alloca_next /\ ts.vs_alloca_next = t.vs_alloca_next /\
  ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
  ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb ==>
  ?stk PG G tn fn inst s t0 A frames N X p h.
    ld_sync lo P C vs0 stk PG G tn fn inst s t0 A frames N /\
    ld_global lo A frames /\
    EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames /\
    (!j k. j < k /\ k < LENGTH frames ==>
      list_precedes (EL j frames).lf_fn.fn_name
                    (EL k frames).lf_fn.fn_name names) /\
    ld_image f = ld_image (HD frames) /\
    ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
    ld_prefix C' (ld_image f) X p h t0
      (ts with vs_inst_idx := SUC t.vs_inst_idx) /\ ti = EL h X /\
    EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
      j IN P f.lf_fn.fn_name) frames
Proof
  rpt strip_tac >> drule_all ld_sync_ordinary_witness >> strip_tac >>
  qexistsl_tac [`stk`,`PG`,`step_prov PG G inst ss`,
    `step_taint inst s ss tn`,`fn`,`next`,
    `ss with vs_inst_idx := SUC s.vs_inst_idx`,
    `ts with vs_inst_idx := SUC t.vs_inst_idx`,
    `A`,`newframe::fs`,`N`,`X`,`p`,`h`] >> gvs[] >> fs[]
QED

(* Forgetting is deliberately at the existential boundary. *)
Theorem ld_owned_coverage_pair:
  (?stk PG G tn fn inst s t0 A frames N X p h.
    ld_sync lo P C vs0 stk PG G tn fn inst s t0 A frames N /\
    ld_global lo A frames /\
    EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames /\
    (!j k. j < k /\ k < LENGTH frames ==>
      list_precedes (EL j frames).lf_fn.fn_name
                    (EL k frames).lf_fn.fn_name names) /\
    fn' = ld_image (HD frames) /\
    ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
    ld_prefix C' fn' X p h t0 t /\ ti = EL h X /\
    EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
      j IN P f.lf_fn.fn_name) frames) ==>
  ld_pair lo P names Sigma C C' vs0 fn' ti t
Proof
  simp[ld_pair_def] >> metis_tac[]
QED
