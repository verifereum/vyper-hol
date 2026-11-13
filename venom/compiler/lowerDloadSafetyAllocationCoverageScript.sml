(* Original ALLOCA coverage only; generated DLOAD scratch is separate. *)
Theory lowerDloadSafetyAllocationCoverage
Ancestors
  lowerDloadSafetyAllocation lowerDloadSafetyOrdinaryCoverage
  lowerDloadSafetyLocations lowerDloadSafetyRelation lowerDloadSafetyKernel
  lowerDloadSafetyAmbient
  ptrDiscipline venomInst finite_map list

Theorem ld_sync_owned_boundary_coverage:
  ld_sync lo P C vs0 stk PG G tn fn next sn tt A (g::fs) N /\
  ld_global lo A (g::fs) /\ o1_ctx_shape C /\
  f.lf_fn = g.lf_fn /\ f.lf_supply = g.lf_supply /\ f.lf_Q = g.lf_Q /\
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) (f::fs) /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
    list_precedes (EL j (f::fs)).lf_fn.fn_name
                  (EL k (f::fs)).lf_fn.fn_name names) /\
  ld_envelope f.lf_supply fn sn sn.vs_inst_idx X tt.vs_inst_idx /\
  active_inst (ld_image f) ti tt ==>
  ?stk PG G tn fn inst s t0 A frames N X p h.
    ld_sync lo P C vs0 stk PG G tn fn inst s t0 A frames N /\
    ld_global lo A frames /\
    EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames /\
    (!j k. j < k /\ k < LENGTH frames ==>
      list_precedes (EL j frames).lf_fn.fn_name
                    (EL k frames).lf_fn.fn_name names) /\
    ld_image f = ld_image (HD frames) /\
    ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
    ld_prefix C' (ld_image f) X p h t0 tt /\ ti = EL h X /\
    EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
      j IN P f.lf_fn.fn_name) frames
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `g.lf_fn = fn /\ g.lf_src = sn /\ g.lf_tgt = tt` by
    (drule ld_sync_active >> simp[]) >>
  `ld_image f = ld_image g` by simp[ld_image_def] >>
  `tt.vs_current_bb = sn.vs_current_bb` by
    (drule ld_sync_control >> simp[]) >>
  `active_inst (FST (lower_dload_function_supply f.lf_supply fn)) ti tt` by
    fs[ld_image_def] >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule lowerDloadSafetyAmbientTheory.o1_fn_shape_components >> strip_tac >>
  `tt.vs_inst_idx = tt.vs_inst_idx` by simp[] >>
  drule_all ld_envelope_active_head >> strip_tac >>
  qexistsl_tac [`stk`,`PG`,`G`,`tn`,`fn`,`next`,`sn`,`tt`,`A`,`g::fs`,
    `N`,`X`,`tt.vs_inst_idx`,`0`] >>
  simp[ld_prefix_zero] >>
  conj_tac >- gvs[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!j k. _` (qspecl_then [`j`,`k`] mp_tac) >>
      Cases_on `j` >> Cases_on `k` >> gvs[]) >>
  conj_tac >- (Cases_on `X` >> gvs[]) >> gvs[]
QED

val _ = List.app (fn (name, th) =>
  if null (hyp th) then () else raise Fail ("nonclosed " ^ name))
  [("ld_cached_alloca_advance", ld_cached_alloca_advance),
   ("ld_fresh_alloca_advance", ld_fresh_alloca_advance),
   ("ld_sync_owned_boundary_coverage", ld_sync_owned_boundary_coverage)];

Theorem ld_sync_alloca_owned_coverage:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  ir_supply_covers_fn f.lf_supply fn /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [Lit sz] /\
  MEM out (fn_ir_vars fn) /\ out IN fn_pv P fn /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\
  t.vs_inst_idx = p /\ step_inst fuel C' inst t = OK ts /\
  (case FLOOKUP s.vs_allocas inst.inst_id of
     NONE => ss = update_var out (n2w s.vs_alloca_next)
       (s with <|vs_allocas := s.vs_allocas |+
         (inst.inst_id,(s.vs_alloca_next,w2n sz));
         vs_alloca_next := s.vs_alloca_next + w2n sz|>)
   | SOME (b,n) => ss = update_var out (n2w b) s) /\
  sn = ss with vs_inst_idx := SUC s.vs_inst_idx /\
  tt = ts with vs_inst_idx := SUC p /\
  active_inst fn next sn /\
  (?Y. ld_envelope f.lf_supply fn sn sn.vs_inst_idx Y (SUC p)) /\
  active_inst (ld_image f) ti tt /\
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) (f::fs) /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
    list_precedes (EL j (f::fs)).lf_fn.fn_name
                  (EL k (f::fs)).lf_fn.fn_name names) ==>
  ?stk PG G tn fn inst s t0 A frames N X p h.
    ld_sync lo P C vs0 stk PG G tn fn inst s t0 A frames N /\
    ld_global lo A frames /\
    EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames /\
    (!j k. j < k /\ k < LENGTH frames ==>
      list_precedes (EL j frames).lf_fn.fn_name
                    (EL k frames).lf_fn.fn_name names) /\
    ld_image f = ld_image (HD frames) /\
    ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
    ld_prefix C' (ld_image f) X p h t0 tt /\ ti = EL h X /\
    EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
      j IN P f.lf_fn.fn_name) frames
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (qabbrev_tac `g = f with <|lf_src := sn; lf_tgt := tt;
        lf_H := f.lf_H |+ (out,(f.lf_serial,inst.inst_id));
        lf_tv := (step_taint inst s ss tn).t_var|>` >>
      fs[optionTheory.option_CLAUSES] >>
      qabbrev_tac `A' = A |+ ((f.lf_serial,inst.inst_id),
        (s.vs_alloca_next,t.vs_alloca_next,w2n sz))` >>
      `step_inst fuel C inst s = OK ss /\
       ld_sync lo P C vs0 stk PG (step_prov PG G inst ss)
         (step_taint inst s ss tn) fn next sn tt A' (g::fs) N /\
       ld_global lo A' (g::fs)` by
        (drule ld_fresh_alloca_advance >> disch_then drule >>
         disch_then drule >> disch_then drule >>
         disch_then irule >> simp[Abbr `g`, Abbr `A'`] >>
         conj_tac >- (qexists_tac `Y` >> gvs[]) >>
         qexistsl_tac [`C'`,`p`,`ts`] >> simp[]) >>
      qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ A' _ _`
        (mp_then Any mp_tac ld_sync_owned_boundary_coverage) >>
      qpat_assum `tt = _` (SUBST1_TAC o SYM) >>
      disch_then irule >> simp[Abbr `g`] >> qexists_tac `Y` >> gvs[]) >>
  PairCases_on `x` >> fs[] >>
  drule_at (Pat `FLOOKUP _ _ = SOME _`)
    (SIMP_RULE bool_ss [] ld_cached_alloca_advance) >>
  disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
  disch_then (qspecl_then [`p`,`next`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac >- gvs[] >> qexists_tac `Y` >> gvs[])) >>
  strip_tac >> gvs[] >>
  qpat_assum `ld_sync _ _ _ _ _ _ _ (step_taint _ _ _ _) _ _ _ _ _ _ _`
    (mp_then Any mp_tac ld_sync_owned_boundary_coverage) >>
  disch_then irule >> simp[] >> qexists_tac `Y` >> first_assum ACCEPT_TAC
QED

val _ = if null (hyp ld_sync_alloca_owned_coverage) then ()
  else raise Fail "nonclosed ld_sync_alloca_owned_coverage";
