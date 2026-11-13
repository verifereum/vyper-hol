(* Fresh empty internal-call frames: no semantic setup/PHI claim. *)
Theory lowerDloadReturnInvokeStack
Ancestors
  lowerDloadSafetyRelation lowerDloadReturnInvokeInterface finite_map pred_set list arithmetic
Libs
  lowerDloadReturnPackageLib

Theorem ld_sites_empty_push:
  fc.lf_src.vs_allocas = FEMPTY /\ fc.lf_tgt.vs_allocas = FEMPTY ==>
  ((j,aid,b,n) IN ld_sites (fc::frames) source <=>
   ?k. j = SUC k /\ (k,aid,b,n) IN ld_sites frames source)
Proof
  strip_tac >> Cases_on `j` >> simp[ld_sites_def] >>
  Cases_on `source` >> simp[]
QED

Theorem ld_global_empty_push:
  frames <> [] /\ ld_global lo A frames /\
  fc.lf_src.vs_allocas = FEMPTY /\ fc.lf_tgt.vs_allocas = FEMPTY /\
  fc.lf_src.vs_alloca_next = (HD frames).lf_src.vs_alloca_next /\
  fc.lf_tgt.vs_alloca_next = (HD frames).lf_tgt.vs_alloca_next /\
  fc.lf_H = FEMPTY /\
  (!a. MEM (SOME a) fc.lf_Q ==> a IN FDOM A) ==>
  ld_global lo A (fc::frames)
Proof
  strip_tac >> rewrite_tac[ld_global_def] >> conj_tac
  >- (rpt strip_tac >>
      `?k. j = SUC k /\ (k,aid,b,n) IN ld_sites frames source` by
        metis_tac[ld_sites_empty_push] >>
      drule_all ld_global_bounds >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `?k. j = SUC k /\ (k,aid,b,n) IN ld_sites frames source` by
        metis_tac[ld_sites_empty_push] >>
      `?k'. j' = SUC k' /\ (k',aid',b',n') IN ld_sites frames source` by
        metis_tac[ld_sites_empty_push] >>
      irule ld_global_separate >> metis_tac[pairTheory.PAIR_EQ]) >>
  rpt strip_tac >> gvs[] >> metis_tac[ld_global_selected]
QED

Theorem ld_serials_fresh_push:
  EVERY (\f. f.lf_serial < N) frames /\
  ALL_DISTINCT (MAP (\f. f.lf_serial) frames) /\ fc.lf_serial = N ==>
  ALL_DISTINCT (MAP (\f. f.lf_serial) (fc::frames)) /\
  EVERY (\f. f.lf_serial < SUC N) (fc::frames)
Proof
  strip_tac >>
  `!f. MEM f frames ==> f.lf_serial < N` by gvs[EVERY_MEM] >>
  simp[EVERY_MEM, MEM_MAP] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem ld_order_fresh_push:
  (!j k. j < k /\ k < LENGTH frames ==>
    list_precedes (EL j frames).lf_fn.fn_name
      (EL k frames).lf_fn.fn_name names) /\
  (!f. MEM f frames ==> list_precedes fc.lf_fn.fn_name f.lf_fn.fn_name names) ==>
  !j k. j < k /\ k < LENGTH (fc::frames) ==>
    list_precedes (EL j (fc::frames)).lf_fn.fn_name
      (EL k (fc::frames)).lf_fn.fn_name names
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `j` >> Cases_on `k` >> simp[] >>
  metis_tac[MEM_EL]
QED

(* ld_slots_empty_push, ld_charge_empty_push and ld_frontiers_empty_push
   are reused from lowerDloadSafetyRelation, not duplicated here. *)
val _ = List.app (fn th => if null (hyp th) then ()
          else raise Fail "empty-frame boundary has kernel hypotheses")
  [ld_sites_empty_push, ld_global_empty_push,
   ld_serials_fresh_push, ld_order_fresh_push];

(* Slot membership carries the allocation lookup witness, not just an address. *)
Theorem ld_slots_agree_subset:
  (!a. a IN ld_slots A fs ==> FLOOKUP B a = FLOOKUP A a) ==>
  ld_slots A fs SUBSET ld_slots B fs
Proof
  simp[ld_slots_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ld_saved_slots_restore:
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  ^ld_probe_stable lo P Sigma names (f::fs) fc A Ar (g::f::fs) ==>
  (FDOM A0 INTER ld_slots A0 fs0) SUBSET ld_slots Ar (f::fs) /\
  (!a. a IN FDOM A0 INTER ld_slots A0 fs0 ==>
    FLOOKUP (DRESTRICT Ar (ld_slots Ar (f::fs))) a = FLOOKUP A0 a) /\
  (!h. MEM h fs0 ==> FRANGE h.lf_H SUBSET ld_slots Ar (f::fs) /\
    (!a. MEM (SOME a) h.lf_Q ==> a IN ld_slots Ar (f::fs)))
Proof
  qabbrev_tac `Stable = ^ld_probe_stable` >> strip_tac >>
  `fs0 = fs` by fs[Abbr `Stable`] >>
  `!a. a IN ld_slots A0 fs0 ==> FLOOKUP A a = FLOOKUP A0 a` by
    (fs[Abbr `Stable`] >> rpt strip_tac >>
     first_x_assum irule >> simp[] >>
     fs[ld_slots_def, FLOOKUP_DEF]) >>
  `ld_slots A0 fs0 SUBSET ld_slots A fs0` by
    (irule ld_slots_agree_subset >> simp[]) >>
  `!a. a IN ld_slots A (f::fs) ==> FLOOKUP Ar a = FLOOKUP A a` by
    (fs[Abbr `Stable`] >> rpt strip_tac >>
     first_x_assum irule >> simp[] >>
     fs[ld_slots_def, FLOOKUP_DEF]) >>
  `ld_slots A (f::fs) SUBSET ld_slots Ar (f::fs)` by
    (irule ld_slots_agree_subset >> simp[]) >>
  `ld_slots A fs0 SUBSET ld_slots Ar (f::fs)` by
    (qpat_assum `ld_slots A (f::fs) SUBSET _` mp_tac >>
     qpat_assum `fs0 = fs` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[Once ld_slots_cons, SUBSET_DEF] >> metis_tac[]) >>
  `FDOM A0 INTER ld_slots A0 fs0 SUBSET ld_slots Ar (f::fs)` by
    (fs[SUBSET_DEF] >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac
  >- (match_mp_tac (Q.INST [`A1` |-> `A`] ld_saved_map_restrict_trans) >>
      simp[] >>
      fs[SUBSET_DEF, Once ld_slots_cons] >> metis_tac[]) >>
  `!h. MEM h fs0 ==> FRANGE h.lf_H SUBSET ld_slots A fs0 /\
    (!a. MEM (SOME a) h.lf_Q ==> a IN ld_slots A fs0)` by
    (qpat_assum `Stable lo P Sigma names fs0 f0 A0 A (f::fs)` mp_tac >>
     qunabbrev_tac `Stable` >> rpt (pop_assum kall_tac) >>
     simp[] >> metis_tac[]) >>
  qpat_assum `ld_slots A fs0 SUBSET ld_slots Ar (f::fs)` mp_tac >>
  qpat_assum `!h. MEM h fs0 ==> FRANGE _ SUBSET _ /\ _` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[SUBSET_DEF] >> metis_tac[]
QED

val _ = List.app (fn th => if null (hyp th) then ()
        else raise Fail "saved-slot transport has kernel hypotheses")
  [ld_slots_agree_subset, ld_saved_slots_restore];
