Theory o1MakeSsaOwnership
Ancestors
  makeSsaDefs makeSsaCurrentProps irSupply list alist pred_set pair

Definition current_name_owner_def:
  current_name_owner V H s <=>
    (!n v w. (n,v) IN H /\ (n,w) IN H ==> v = w) /\
    (!v. v IN V ==> (v,v) IN H) /\
    (!n v. (n,v) IN H ==> v IN V /\ MEM n s.irs_used_vars)
End

Definition current_stack_owner_def:
  current_stack_owner V H (stacks : (string # string list) list) <=>
    !v ns. MEM (v,ns) stacks ==> v IN V /\
      (!n. MEM n ns ==> (n,v) IN H)
End

Definition current_rename_owner_def:
  current_rename_owner V H s
    (counters : (string # num) list, stacks : (string # string list) list) <=>
    current_name_owner V H s /\ current_stack_owner V H stacks /\
    (!v k. MEM (v,k) counters ==> v IN V)
End

Theorem current_name_owner_unique:
  current_name_owner V H s /\ (n,v) IN H /\ (n,w) IN H ==> v = w
Proof simp[current_name_owner_def] >> metis_tac[]
QED

Theorem current_name_owner_identity:
  current_name_owner V H s /\ v IN V ==> (v,v) IN H
Proof simp[current_name_owner_def] >> metis_tac[]
QED

Theorem current_name_owner_covered:
  current_name_owner V H s /\ (n,v) IN H ==> MEM n s.irs_used_vars
Proof simp[current_name_owner_def] >> metis_tac[]
QED

Theorem current_name_owner_fresh:
  current_name_owner V H s /\ v IN V /\ fresh_ir_var s = (n,s') ==>
  current_name_owner V ((n,v) INSERT H) s'
Proof
  strip_tac >> drule fresh_ir_var_contract >> strip_tac >>
  gvs[current_name_owner_def] >> rpt conj_tac >> rpt strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem current_stack_owner_mono:
  current_stack_owner V H stacks /\ H SUBSET H' ==>
  current_stack_owner V H' stacks
Proof
  simp[current_stack_owner_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem current_stack_owner_lookup:
  current_stack_owner V H stacks /\ ALOOKUP stacks v = SOME ns ==>
  v IN V /\ (!n. MEM n ns ==> (n,v) IN H)
Proof
  strip_tac >> drule ALOOKUP_MEM >>
  gvs[current_stack_owner_def] >> metis_tac[]
QED

Theorem current_rename_owner_latest:
  current_rename_owner V H s rs /\ v IN V ==>
  (latest_current_name rs v,v) IN H
Proof
  PairCases_on `rs` >>
  simp[current_rename_owner_def, latest_current_name_def] >> strip_tac >>
  Cases_on `ALOOKUP rs1 v`
  >- (simp[] >> drule_all current_name_owner_identity >> simp[]) >>
  rename1 `ALOOKUP rs1 v = SOME ns` >> Cases_on `ns` >> simp[]
  >- (simp[] >> drule_all current_name_owner_identity >> simp[]) >>
  drule_all current_stack_owner_lookup >> simp[]
QED

Theorem current_stack_owner_push:
  current_stack_owner V H stacks /\ v IN V /\ (n,v) IN H ==>
  current_stack_owner V H
    ((v,n::(case ALOOKUP stacks v of SOME ns => ns | NONE => []))::
     FILTER (\(w,_). w <> v) stacks)
Proof
  strip_tac >> simp[current_stack_owner_def, MEM_FILTER, FORALL_PROD] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `ALOOKUP stacks v` >> gvs[] >>
      drule_all current_stack_owner_lookup >> metis_tac[]) >>
  gvs[current_stack_owner_def] >> metis_tac[]
QED

Theorem current_rename_owner_push:
  current_rename_owner V H s rs /\ v IN V /\
  push_current_name s rs v = (rs',s',n) ==>
  ?H'. H SUBSET H' /\ current_rename_owner V H' s' rs' /\ (n,v) IN H'
Proof
  PairCases_on `rs` >>
  simp[current_rename_owner_def, push_current_name_def] >>
  Cases_on `ALOOKUP rs0 v` >> simp[] >>
  TRY (rename1 `ALOOKUP rs0 v = SOME k` >> Cases_on `k = 0` >> simp[]) >>
  rpt strip_tac >> gvs[]
  >- (`(n,n) IN H` by (drule_all current_name_owner_identity >> simp[]) >>
      qexists_tac `H` >> simp[current_rename_owner_def, SUBSET_REFL] >>
      rpt conj_tac
      >- (irule current_stack_owner_push >>
          drule_all current_name_owner_identity >> simp[]) >>
      simp[MEM_FILTER, FORALL_PROD] >> rpt strip_tac >> gvs[] >>
      first_x_assum drule >> simp[]) 
  >- (`(n,n) IN H` by (drule_all current_name_owner_identity >> simp[]) >>
      qexists_tac `H` >> simp[current_rename_owner_def, SUBSET_REFL] >>
      rpt conj_tac
      >- (irule current_stack_owner_push >>
          drule_all current_name_owner_identity >> simp[]) >>
      simp[MEM_FILTER, FORALL_PROD] >> rpt strip_tac >> gvs[] >>
      first_x_assum drule >> simp[]) >>
  Cases_on `fresh_ir_var s` >> gvs[] >>
  rename1 `fresh_ir_var s = (name,t)` >>
  qexists_tac `(name,v) INSERT H` >>
  simp[current_rename_owner_def, SUBSET_DEF] >>
  conj_tac >- (drule_all current_name_owner_fresh >> simp[]) >>
  conj_tac
  >- (irule current_stack_owner_push >> simp[] >>
      irule current_stack_owner_mono >> qexists_tac `H` >> simp[SUBSET_DEF]) >>
  simp[MEM_FILTER, FORALL_PROD] >> rpt strip_tac >> gvs[] >>
      first_x_assum drule >> simp[]
QED

Theorem current_rename_owner_nonclobber:
  current_rename_owner V H s rs /\ v IN V /\ w IN V /\ w <> v /\
  push_current_name s rs v = (rs',s',n) ==>
  latest_current_name rs w <> n
Proof
  strip_tac >> drule_all current_rename_owner_latest >> strip_tac >>
  drule_all current_rename_owner_push >> strip_tac >>
  ` (latest_current_name rs w,w) IN H'` by fs[SUBSET_DEF] >>
  PairCases_on `rs'` >> gvs[current_rename_owner_def] >>
  metis_tac[current_name_owner_unique]
QED

Theorem current_rename_owner_restore:
  current_rename_owner V H s (counters,stacks) /\ H SUBSET H' /\
  current_rename_owner V H' s' (counters',stacks') ==>
  current_rename_owner V H' s' (counters',stacks)
Proof
  simp[current_rename_owner_def] >>
  metis_tac[current_stack_owner_mono]
QED

Theorem current_rename_owner_init:
  (!v. v IN V ==> MEM v s.irs_used_vars) /\
  (!v. MEM v (MAP FST defs) ==> v IN V) ==>
  current_rename_owner V {(v,v) | v IN V} s (init_current_rename_state defs)
Proof
  simp[init_current_rename_state_def, current_rename_owner_def,
       current_name_owner_def, current_stack_owner_def, MEM_MAP] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem current_rename_owner_extend_supply:
  current_rename_owner V H s rs /\
  (!n. MEM n s.irs_used_vars ==> MEM n s'.irs_used_vars) ==>
  current_rename_owner V H s' rs
Proof
  PairCases_on `rs` >>
  simp[current_rename_owner_def, current_name_owner_def] >> metis_tac[]
QED

Theorem current_rename_owner_init_function:
  ssa_vars_covered s (fn_ir_vars fn) ==>
  current_rename_owner (set (fn_ir_vars fn))
    {(v,v) | MEM v (fn_ir_vars fn)} s
    (init_current_rename_state
      (compute_defs (MAP THE (FILTER IS_SOME
        (MAP (\lbl. lookup_block lbl fn.fn_blocks) labels)))))
Proof
  strip_tac >> irule current_rename_owner_init >> conj_tac
  >- gvs[ssa_vars_covered_def, EVERY_MEM] >>
  rpt strip_tac >>
  drule compute_defs_key_MEM_block_ir_vars >>
  rewrite_tac[MEM_FLAT] >> strip_tac >>
  qpat_x_assum `MEM l (MAP block_ir_vars _)` mp_tac >>
  once_rewrite_tac[MEM_MAP] >> strip_tac >> gvs[] >>
  drule lookup_blocks_filter_MEM >> strip_tac >>
  simp[fn_ir_vars_def, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED
