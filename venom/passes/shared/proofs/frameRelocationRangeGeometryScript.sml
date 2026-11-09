Theory frameRelocationRangeGeometry
Ancestors frameRelocationGuardedValues frameRelocationCompareSteps
  frameRelocationBinding frameRelocationLocal frameRelocationValues
  frameRelocationGhostCopy venomExecSemantics venomState words

Theorem guarded_pointer_range:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  ~Opaque v /\ FLOOKUP rv v = SOME (tok,(b,sz)) /\
  eval_operand (Var v) s = SOME x /\
  b <= w2n x /\ w2n x + len <= b+sz /\
  b+sz < dimword (:256) /\ L tok+sz < dimword (:256) ==>
  ?y. eval_operand (Var v) t = SOME y /\
      w2n y = L tok + (w2n x-b) /\
      L tok <= w2n y /\ w2n y + len <= L tok+sz
Proof
  strip_tac >>
  `variable_domains s t` by metis_tac[local_rel_domains] >>
  `?y. lookup_var v t = SOME y` by
    (fs[variable_domains_def, eval_operand_def] >>
     Cases_on `lookup_var v t` >> metis_tac[]) >>
  `guarded_ptr Opaque L rv v x y` by
    (irule local_rel_pointer >> fs[eval_operand_def] >> metis_tac[]) >>
  `x - n2w b = y - n2w (L tok)` by
    metis_tac[guarded_ptr_def, copy_ptr_def] >>
  `w2n y = L tok + (w2n x-b)` by
    (irule displacement_natural_address >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
      arithmeticTheory.LESS_EQ_ADD]) >>
  qexists_tac `y` >> simp[eval_operand_def] >> decide_tac
QED

Theorem cached_range_relocation:
  activation_cache q depth owner aid (b,sz) /\
  lo <= b /\ b <= off /\ off+len <= b+sz /\
  target = positions owner aid + (off-b) ==>
  !k. k < len ==> relocation_pair lo positions q (off+k) (target+k)
Proof
  rpt strip_tac >> simp[relocation_pair_def] >>
  qexistsl_tac [`depth`, `owner`, `aid`, `b`, `sz`] >>
  simp[] >> decide_tac
QED
