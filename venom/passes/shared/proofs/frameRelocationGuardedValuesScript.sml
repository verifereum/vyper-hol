Theory frameRelocationGuardedValues
Ancestors frameRelocationGhostCopy frameRelocationOpaque frameRelocationLocal
  frameRelocationValues frameOriginUpdates ptrDiscipline finite_map words

Definition guarded_ptr_def:
  guarded_ptr Opaque L rv v x y <=> (~Opaque v ==> copy_ptr L rv v x y)
End

Definition guarded_bytes_def:
  guarded_bytes Opaque rv tn v x y <=> (~Opaque v ==> copy_bytes rv tn v x y)
End

Definition clean_scalar_def:
  clean_scalar Opaque rv tn v <=>
    ~Opaque v /\ FLOOKUP rv v = NONE /\ op_taint tn (Var v) = {}
End

Theorem word_agree_except_empty:
  word_agree_except {} (x:bytes32) y ==> x = y
Proof
  simp[word_agree_except_bits, fcpTheory.CART_EQ]
QED

Theorem word_agree_except_selector_mul:
  word_agree_except m (x:bytes32) (x':bytes32) /\ word_agree_except n y y' /\
  (m = {} \/ (n = {} /\ (y = 0w \/ y = 1w))) /\
  (n = {} \/ (m = {} /\ (x = 0w \/ x = 1w))) ==>
  word_agree_except
    ((if x = 1w then n else {}) UNION (if y = 1w then m else {}))
    (x * y) (x' * y')
Proof
  strip_tac >>
  `m = {} ==> x = x'` by
    (strip_tac >> irule word_agree_except_empty >> gvs[]) >>
  `n = {} ==> y = y'` by
    (strip_tac >> irule word_agree_except_empty >> gvs[]) >>
  Cases_on `m = {}` >> Cases_on `n = {}` >>
  gvs[wordsTheory.WORD_MULT_CLAUSES, word_agree_except_def]
QED

Theorem guarded_ptr_output:
  (~Opaque v ==> ~Opaque w) /\ guarded_ptr Opaque L rv w x y ==>
  guarded_ptr Opaque L (origin_set rv [v] (FLOOKUP rv w)) v x y
Proof
  simp[guarded_ptr_def] >> metis_tac[copy_ptr_output]
QED

Theorem guarded_bytes_output:
  (~Opaque v ==> ~Opaque w) /\ guarded_bytes Opaque rv tn w x y ==>
  guarded_bytes Opaque (origin_set rv [v] (FLOOKUP rv w))
    (tn with t_var := tn.t_var |+ (v,op_taint tn (Var w))) v x y
Proof
  simp[guarded_bytes_def] >> metis_tac[copy_bytes_output]
QED

Theorem guarded_ptr_other:
  u <> v ==>
  (guarded_ptr Opaque L (origin_set rv [v] p) u x y <=> guarded_ptr Opaque L rv u x y)
Proof
  simp[guarded_ptr_def, copy_ptr_other]
QED

Theorem guarded_bytes_other:
  u <> v ==>
  (guarded_bytes Opaque (origin_set rv [v] p)
    (tn with t_var := tn.t_var |+ (v,m)) u x y <=> guarded_bytes Opaque rv tn u x y)
Proof
  simp[guarded_bytes_def, copy_bytes_other]
QED

Theorem clean_scalar_output:
  ~Opaque v /\ clean_scalar Opaque rv tn w ==>
  clean_scalar Opaque (origin_set rv [v] (FLOOKUP rv w))
    (tn with t_var := tn.t_var |+ (v,op_taint tn (Var w))) v
Proof
  simp[clean_scalar_def, origin_set_lookup, op_taint_def, FLOOKUP_UPDATE]
QED

Theorem clean_scalar_other:
  u <> v ==>
  (clean_scalar Opaque (origin_set rv [v] p)
    (tn with t_var := tn.t_var |+ (v,m)) u <=> clean_scalar Opaque rv tn u)
Proof
  simp[clean_scalar_def, origin_set_lookup, op_taint_def, FLOOKUP_UPDATE]
QED

Theorem guarded_scalar_agreement:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t ==>
  variables_agree_on (clean_scalar Opaque rv tn) s t
Proof
  strip_tac >> simp[variables_agree_on_def] >> rpt strip_tac >>
  `variable_domains s t` by metis_tac[local_rel_domains] >>
  Cases_on `lookup_var v s`
  >- (fs[variable_domains_def] >> metis_tac[]) >>
  `?y. lookup_var v t = SOME y` by
    (qpat_x_assum `variable_domains s t` mp_tac >>
     simp[variable_domains_def] >>
     disch_then (qspec_then `v` mp_tac) >>
     Cases_on `lookup_var v t` >> simp[]) >>
  `guarded_bytes Opaque rv tn v x y` by metis_tac[local_rel_bytes] >>
  gvs[guarded_bytes_def, clean_scalar_def, copy_bytes_def] >>
  metis_tac[word_agree_except_empty]
QED

Theorem guarded_scalar_operand:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  s.vs_labels = t.vs_labels /\
  (!v. op = Var v ==> clean_scalar Opaque rv tn v) ==>
  eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule guarded_scalar_agreement >> strip_tac >>
  irule scalar_operand_agreement >> simp[] >>
  qexists_tac `clean_scalar Opaque rv tn` >> simp[]
QED
