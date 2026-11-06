(* Fresh empty internal-call frames: no semantic setup/PHI claim. *)
Theory lowerDloadReturnInvokeStack
Ancestors
  lowerDloadSafetyRelation finite_map pred_set list arithmetic

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
