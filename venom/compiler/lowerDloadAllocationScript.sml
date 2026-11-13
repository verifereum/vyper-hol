(* Allocation-map accounting only; byte relations and reachability are separate. *)
Theory lowerDloadAllocation
Ancestors
  lowerDloadStackBound lowerDloadRelocation venomExecSemantics finite_map
  pred_set arithmetic

Definition ld_alloc_account_def:
  ld_alloc_account keys d0 A s t <=>
    FINITE keys /\ A SUBSET keys /\ DISJOINT (FDOM s.vs_allocas) keys /\
    FDOM t.vs_allocas = FDOM s.vs_allocas UNION A /\
    t.vs_alloca_next = s.vs_alloca_next + d0 + 32 * CARD A /\
    (!id bs sz. FLOOKUP s.vs_allocas id = SOME (bs,sz) ==>
      ?e. e <= d0 + 32 * CARD A /\
          FLOOKUP t.vs_allocas id = SOME (bs+e,sz)) /\
    (!id. id IN A ==> ?b. FLOOKUP t.vs_allocas id = SOME (b,32))
End

Theorem ld_alloc_account_init:
  s.vs_allocas = FEMPTY /\ t.vs_allocas = FEMPTY /\ FINITE keys /\
  t.vs_alloca_next = s.vs_alloca_next + d0 ==>
  ld_alloc_account keys d0 {} s t
Proof
  simp[ld_alloc_account_def]
QED

Theorem ld_alloc_account_finite:
  ld_alloc_account keys d0 A s t ==> FINITE A
Proof
  simp[ld_alloc_account_def] >> metis_tac[SUBSET_FINITE]
QED

Theorem ld_alloc_account_capacity:
  ld_alloc_account keys d0 A s t ==> FINITE keys /\ A SUBSET keys
Proof
  simp[ld_alloc_account_def]
QED

Theorem ld_alloc_account_disjoint:
  ld_alloc_account keys d0 A s t ==> DISJOINT (FDOM s.vs_allocas) keys
Proof
  simp[ld_alloc_account_def]
QED

Theorem ld_alloc_account_domain:
  ld_alloc_account keys d0 A s t ==>
  FDOM t.vs_allocas = FDOM s.vs_allocas UNION A
Proof
  simp[ld_alloc_account_def]
QED

Theorem ld_alloc_account_frontier:
  ld_alloc_account keys d0 A s t ==>
  t.vs_alloca_next = s.vs_alloca_next + d0 + 32 * CARD A
Proof
  simp[ld_alloc_account_def]
QED

Theorem ld_alloc_account_old_entry:
  ld_alloc_account keys d0 A s t /\
  FLOOKUP s.vs_allocas id = SOME (bs,sz) ==>
  ?e. e <= d0 + 32 * CARD A /\
      FLOOKUP t.vs_allocas id = SOME (bs+e,sz)
Proof
  simp[ld_alloc_account_def] >> metis_tac[]
QED

Theorem ld_alloc_account_scratch_entry:
  ld_alloc_account keys d0 A s t /\ id IN A ==>
  ?b. FLOOKUP t.vs_allocas id = SOME (b,32)
Proof
  simp[ld_alloc_account_def] >> metis_tac[]
QED

Theorem ld_alloc_account_old_absent:
  ld_alloc_account keys d0 A s t /\ id NOTIN keys ==>
  (FLOOKUP s.vs_allocas id = NONE <=> FLOOKUP t.vs_allocas id = NONE)
Proof
  simp[ld_alloc_account_def, FLOOKUP_DEF] >> SET_TAC[]
QED

Theorem ld_alloc_account_scratch_absent:
  ld_alloc_account keys d0 A s t /\ id IN keys ==>
  (FLOOKUP t.vs_allocas id = NONE <=> id NOTIN A)
Proof
  simp[ld_alloc_account_def, FLOOKUP_DEF] >> SET_TAC[]
QED

Theorem ld_alloc_account_ordinary:
  ld_alloc_account keys d0 A s t /\ i.inst_id = j.inst_id /\
  i.inst_id NOTIN keys /\ i.inst_outputs = [out] /\
  j.inst_outputs = [out'] /\
  exec_alloca i s n = OK s' /\ exec_alloca j t n = OK t' ==>
  ld_alloc_account keys d0 A s' t'
Proof
  strip_tac >>
  `FLOOKUP s.vs_allocas i.inst_id = NONE <=>
   FLOOKUP t.vs_allocas i.inst_id = NONE` by
    metis_tac[ld_alloc_account_old_absent] >>
  Cases_on `FLOOKUP s.vs_allocas i.inst_id`
  >- (gvs[exec_alloca_def, venomStateTheory.update_var_def] >>
      gvs[ld_alloc_account_def, FLOOKUP_UPDATE] >>
      conj_tac >- SET_TAC[] >>
      conj_tac
      >- (rpt gen_tac >> Cases_on `j.inst_id = id`
          >- (simp[] >> strip_tac >> gvs[] >>
              qexists_tac `d0 + 32 * CARD A` >> simp[]) >>
          simp[] >> metis_tac[]) >>
      rpt strip_tac >> `j.inst_id <> id` by (gvs[SUBSET_DEF] >> metis_tac[]) >>
      simp[] >> metis_tac[]) >>
  PairCases_on `x` >>
  drule_all ld_alloc_account_old_entry >> strip_tac >>
  gvs[exec_alloca_def, venomStateTheory.update_var_def] >>
  gvs[ld_alloc_account_def]
QED

Theorem ld_alloc_account_scratch:
  ld_alloc_account keys d0 A s t /\ j.inst_id IN keys /\
  j.inst_outputs = [out] /\ exec_alloca j t (32w:bytes32) = OK t' ==>
  ld_alloc_account keys d0 (j.inst_id INSERT A) s t'
Proof
  strip_tac >>
  `FINITE A` by metis_tac[ld_alloc_account_finite] >>
  `FLOOKUP t.vs_allocas j.inst_id = NONE <=> j.inst_id NOTIN A` by
    metis_tac[ld_alloc_account_scratch_absent] >>
  Cases_on `j.inst_id IN A`
  >- (`j.inst_id INSERT A = A` by ASM_SET_TAC[] >>
      `?b. FLOOKUP t.vs_allocas j.inst_id = SOME (b,32)` by
        metis_tac[ld_alloc_account_scratch_entry] >>
      qpat_x_assum `_ INSERT A = A` SUBST1_TAC >>
      gvs[exec_alloca_def, venomStateTheory.update_var_def, ld_alloc_account_def]) >>
  gvs[exec_alloca_def, venomStateTheory.update_var_def] >>
  gvs[ld_alloc_account_def, CARD_INSERT, FLOOKUP_UPDATE] >>
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  simp[wordsTheory.dimword_def, arithmeticTheory.MULT_CLAUSES] >>
  conj_tac >- SET_TAC[] >>
  conj_tac
  >- (rpt strip_tac >>
      `j.inst_id <> id` by
        (gvs[DISJOINT_DEF, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
      simp[] >>
      first_x_assum (drule_then strip_assume_tac) >>
      qexists_tac `e` >> simp[] >> decide_tac) >>
  rpt gen_tac >> disch_tac >> Cases_on `j.inst_id = id`
  >- (pop_assum (fn th => simp[NoAsms, th])) >>
  first_assum (fn th => simp[NoAsms, th]) >>
  first_x_assum irule >> metis_tac[]
QED

(* Both branches return the stored base, or the frontier at a fresh site. *)
Theorem ld_alloc_account_outputs:
  ld_alloc_account keys d0 A s t /\ i.inst_id = j.inst_id /\
  i.inst_id NOTIN keys /\ i.inst_outputs = [out] /\
  j.inst_outputs = [out'] /\
  exec_alloca i s n = OK s' /\ exec_alloca j t n = OK t' ==>
  ?bs bt sz.
    FLOOKUP s'.vs_allocas i.inst_id = SOME (bs,sz) /\
    FLOOKUP t'.vs_allocas j.inst_id = SOME (bt,sz) /\
    lookup_var out s' = SOME (n2w bs) /\
    lookup_var out' t' = SOME (n2w bt) /\
    ld_ptr_rel bs bt (n2w bs) (n2w bt) /\
    bt <= bs + d0 + 32 * CARD A
Proof
  strip_tac >>
  `FLOOKUP s.vs_allocas i.inst_id = NONE <=>
   FLOOKUP t.vs_allocas i.inst_id = NONE` by
    metis_tac[ld_alloc_account_old_absent] >>
  Cases_on `FLOOKUP s.vs_allocas i.inst_id`
  >- (gvs[exec_alloca_def, venomStateTheory.update_var_def,
          venomStateTheory.lookup_var_def, FLOOKUP_UPDATE] >>
      conj_tac
      >- (pure_rewrite_tac[ld_ptr_rel_def] >>
          qabbrev_tac `sw = (n2w s.vs_alloca_next:bytes32)` >>
          qabbrev_tac `tw = (n2w t.vs_alloca_next:bytes32)` >>
          CONV_TAC wordsLib.WORD_ARITH_CONV) >>
      drule ld_alloc_account_frontier >> simp[]) >>
  PairCases_on `x` >>
  drule_all ld_alloc_account_old_entry >> strip_tac >>
  gvs[exec_alloca_def, venomStateTheory.update_var_def,
      venomStateTheory.lookup_var_def, FLOOKUP_UPDATE] >>
  simp[] >> pure_rewrite_tac[ld_ptr_rel_def] >>
  qabbrev_tac `sw = (n2w x0:bytes32)` >>
  qabbrev_tac `tw = (n2w (e+x0):bytes32)` >>
  CONV_TAC wordsLib.WORD_ARITH_CONV
QED

Theorem ld_alloc_account_transport:
  ld_alloc_account keys d0 A s t /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
  t'.vs_allocas = t.vs_allocas /\ t'.vs_alloca_next = t.vs_alloca_next ==>
  ld_alloc_account keys d0 A s' t'
Proof
  simp[ld_alloc_account_def]
QED

Theorem ld_alloc_account_enter:
  ld_alloc_account keys d0 A s t /\
  setup_callee fn args s = SOME u /\
  setup_callee fn' args' t = SOME v /\ FINITE kc ==>
  ld_alloc_account kc (d0 + 32 * CARD A) {} u v
Proof
  simp[setup_callee_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  irule ld_alloc_account_init >> simp[] >>
  drule ld_alloc_account_frontier >> simp[]
QED

Theorem ld_alloc_account_return:
  ld_alloc_account keys d0 A s t ==>
  ld_alloc_account keys d0 A (merge_callee_state s u) (merge_callee_state t v)
Proof
  strip_tac >> irule ld_alloc_account_transport >>
  qexistsl_tac [`s`, `t`] >> simp[merge_callee_state_def]
QED

Theorem ld_alloc_account_card_bound:
  ld_alloc_account keys d0 A s t ==> CARD A <= CARD keys
Proof
  strip_tac >> drule ld_alloc_account_capacity >>
  metis_tac[CARD_SUBSET]
QED

Theorem ld_scratch_sum_bound:
  !xs. EVERY (\x. FINITE (caps x) /\ A x SUBSET caps x /\
                     CARD (caps x) <= w x) xs ==>
    SUM (MAP (\x. CARD (A x)) xs) <= SUM (MAP w xs)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `CARD (A h) <= CARD (caps h)` by (irule pred_setTheory.CARD_SUBSET >> simp[]) >>
  first_x_assum drule >> decide_tac
QED

Theorem ld_alloc_stack_budget:
  callee_first names C.ctx_functions /\ ld_stack_origin vs C stk fn s0 /\
  EVERY (\g. FINITE (caps g) /\ A g SUBSET caps g /\
    CARD (caps g) <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g)))
    (fn :: MAP (\f. f.cf_fn) stk) ==>
  SUM (MAP (\g. CARD (A g)) (fn :: MAP (\f. f.cf_fn) stk)) <=
    ctx_dload_count C
Proof
  strip_tac >>
  `SUM (MAP (\g. CARD (A g)) (fn :: MAP (\f. f.cf_fn) stk)) <=
   SUM (MAP (\g. LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g)))
        (fn :: MAP (\f. f.cf_fn) stk))` by
    (irule ld_scratch_sum_bound >> qexists_tac `caps` >> gvs[]) >>
  drule_all ld_stack_dload_count_bound >> decide_tac
QED

Theorem ld_alloc_account_nowrap:
  ld_alloc_account keys d0 A s t /\
  d0 + 32 * CARD A <= 32 * ctx_dload_count C /\
  dload_headroom_ok C fn inst s ==>
  t.vs_alloca_next < dimword (:256)
Proof
  strip_tac >> drule ld_alloc_account_frontier >>
  gvs[lowerDloadDefsTheory.dload_headroom_ok_def] >> decide_tac
QED
