Theory frameRelocationLocal
Ancestors frameRelocationValues frameRelocationOpaque frameRelocationMemory
  frameRelocationDemand venomState finite_map words

Definition local_values_def:
  local_values ptr_rel B s t <=>
  !v x y. lookup_var v s = SOME x /\ lookup_var v t = SOME y ==>
    ptr_rel v x y /\ B v x y
End

Definition local_rel_def:
  local_rel P ptr_rel B R Obs s t <=>
  variable_domains s t /\ variables_agree_on P s t /\ local_values ptr_rel B s t /\
  demand_agree R (\a. read_byte a s.vs_memory) (\b. read_byte b t.vs_memory) /\
  Obs s t
End

Theorem local_rel_domains:
  local_rel P ptr_rel B R Obs s t ==> variable_domains s t
Proof
  simp[local_rel_def]
QED

Theorem local_rel_scalars:
  local_rel P ptr_rel B R Obs s t ==> variables_agree_on P s t
Proof
  simp[local_rel_def]
QED

Theorem local_rel_pointer:
  local_rel P ptr_rel B R Obs s t /\ lookup_var v s = SOME x /\
  lookup_var v t = SOME y ==> ptr_rel v x y
Proof
  metis_tac[local_rel_def, local_values_def]
QED

Theorem local_rel_bytes:
  local_rel P ptr_rel B R Obs s t /\ lookup_var v s = SOME x /\
  lookup_var v t = SOME y ==> B v x y
Proof
  metis_tac[local_rel_def, local_values_def]
QED

Theorem local_rel_demand:
  local_rel P ptr_rel B R Obs s t ==>
  demand_agree R (\a. read_byte a s.vs_memory) (\b. read_byte b t.vs_memory)
Proof
  simp[local_rel_def]
QED

Theorem local_rel_observation:
  local_rel P ptr_rel B R Obs s t ==> Obs s t
Proof
  simp[local_rel_def]
QED

Theorem local_rel_update:
  local_rel P ptr_rel B R Obs s t /\
  (!u. u <> v ==> (P' u ==> P u) /\
    (!a b. ptr_rel u a b ==> ptr_rel' u a b) /\
    (!a b. B u a b ==> B' u a b)) /\
  (P' v ==> x = y) /\ ptr_rel' v x y /\ B' v x y /\
  Obs (update_var v x s) (update_var v y t) ==>
  local_rel P' ptr_rel' B' R Obs (update_var v x s) (update_var v y t)
Proof
  strip_tac >> simp[local_rel_def] >>
  conj_tac >- metis_tac[local_rel_domains, variable_domains_update] >>
  conj_tac
  >- (fs[local_rel_def, variables_agree_on_def, lookup_var_def] >>
      simp[variables_agree_on_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  conj_tac
  >- (fs[local_rel_def, local_values_def, lookup_var_def] >>
      simp[local_values_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> Cases_on `v' = v` >> gvs[] >> metis_tac[]) >>
  fs[local_rel_def] >> simp[update_var_def]
QED

Theorem local_rel_update_observation_invariant:
  local_rel P ptr_rel B R Obs s t /\
  (!u. u <> v ==> (P' u ==> P u) /\
    (!a b. ptr_rel u a b ==> ptr_rel' u a b) /\
    (!a b. B u a b ==> B' u a b)) /\
  (P' v ==> x = y) /\ ptr_rel' v x y /\ B' v x y /\
  (!a b. Obs a b ==> Obs (update_var v x a) (update_var v y b)) ==>
  local_rel P' ptr_rel' B' R Obs (update_var v x s) (update_var v y t)
Proof
  strip_tac >> drule local_rel_observation >> strip_tac >>
  irule local_rel_update >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Neither a relocated pointer nor an opaque value has to be equal.
   The pointer equation constrains only the selected variable. *)
Theorem local_rel_modular_write_probe:
  local_rel P (\u a c. u = v ==> a - b = c - d) (\u a c. T) R Obs s t /\
  ~P v /\ x - b = y - d /\
  Obs (update_var v x s) (update_var v y t) ==>
  local_rel P (\u a c. u = v ==> a - b = c - d) (\u a c. T) R Obs
    (update_var v x s) (update_var v y t)
Proof
  strip_tac >> irule local_rel_update >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem local_rel_opaque_write_probe:
  local_rel P (\u a c. T) (\u a c. T) R Obs s t /\ ~P v /\
  Obs (update_var v x s) (update_var v y t) ==>
  local_rel P (\u a c. T) (\u a c. T) R Obs
    (update_var v x s) (update_var v y t)
Proof
  strip_tac >> irule local_rel_update >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
