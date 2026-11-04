Theory lowerDloadPairedBoundary
Ancestors
  lowerDloadOperand lowerDloadLifetime lowerDloadOwnership lowerDloadRelocation
  ptrDiscipline venomState finite_map pred_set list words

Definition ld_owned_selection_def:
  ld_owned_selection E ps pt <=>
    (ps = NONE /\ pt = NONE) \/
    ?owner bs bt sz. ps = SOME (owner,(bs,sz)) /\
      pt = SOME (owner,(bt,sz)) /\ ld_site_entry E owner bs bt sz
End

Definition ld_owned_value_def:
  ld_owned_value E ps pt Ms Mt (x:bytes32) y <=>
    case ps of
      NONE => pt = NONE /\ ld_mask_word Ms Mt x y
    | SOME (owner,(bs,sz)) =>
        ?bt. ld_site_entry E owner bs bt sz /\
          pt = SOME (owner,(bt,sz)) /\ Mt SUBSET Ms /\
          ld_ptr_rel bs bt x y
End

Definition ld_owned_vars_def:
  ld_owned_vars V E AG AH tn un s t <=>
    s.vs_labels = t.vs_labels /\
    !v. v IN V ==>
      (lookup_var v s = NONE <=> lookup_var v t = NONE) /\
      (!x y. lookup_var v s = SOME x /\ lookup_var v t = SOME y ==>
        ld_owned_value E (FLOOKUP AG v) (FLOOKUP AH v)
          (op_taint tn (Var v)) (op_taint un (Var v)) x y)
End

Theorem ld_owned_operand_defined:
  ld_owned_vars V E AG AH tn un s t /\ (!v. op = Var v ==> v IN V) ==>
  (eval_operand op s = NONE <=> eval_operand op t = NONE)
Proof
  Cases_on `op` >> simp[eval_operand_def, ld_owned_vars_def] >> metis_tac[]
QED

Theorem ld_owned_operand_value:
  ld_owned_vars V E AG AH tn un s t /\ (!v. op = Var v ==> v IN V) /\
  eval_operand op s = SOME x /\ eval_operand op t = SOME y ==>
  ld_owned_value E (ld_op_prov AG op) (ld_op_prov AH op)
    (op_taint tn op) (op_taint un op) x y
Proof
  Cases_on `op` >>
  simp[eval_operand_def, ld_op_prov_def, op_taint_def, ld_owned_vars_def] >>
  rpt strip_tac >> gvs[ld_owned_value_def, ld_mask_word_def] >> metis_tac[]
QED

Theorem ld_owned_operand_clean:
  ld_owned_vars V E AG AH tn un s t /\ (!v. op = Var v ==> v IN V) /\
  ld_op_prov AG op = NONE /\ op_taint tn op = {} ==>
  eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `eval_operand op s = NONE <=> eval_operand op t = NONE` by
    metis_tac[ld_owned_operand_defined] >>
  Cases_on `eval_operand op s` >> Cases_on `eval_operand op t` >> gvs[] >>
  drule_all ld_owned_operand_value >>
  simp[ld_owned_value_def] >> metis_tac[ld_mask_word_clean]
QED

Theorem ld_owned_value_compare:
  ld_owned_value E (SOME(owner,(bs,sz))) px Ms Mt x x' /\
  ld_owned_value E (SOME(owner,(bs,sz))) py Ns Nt y y' /\
  ld_site_entry E owner bs bt sz /\
  bs <= w2n x /\ w2n x <= bs+sz /\
  bs <= w2n y /\ w2n y <= bs+sz /\
  bs+sz < dimword(:256) /\ bt+sz < dimword(:256) ==>
  ((x <+ y <=> x' <+ y') /\ (y <+ x <=> y' <+ x') /\ (x=y <=> x'=y'))
Proof
  strip_tac >> gvs[ld_owned_value_def, ld_site_entry_def] >>
  irule ld_ptr_rel_compare >>
  qexistsl [`bs`, `bt`, `sz`] >> simp[]
QED

Theorem ld_owned_empty_aliases:
  let E = FEMPTY |+ ((0,0),(0,0,0)) |+ ((0,1),(0,32,0)) in
    ld_owned_value E (SOME ((0,0),(0,0))) (SOME ((0,0),(0,0)))
      {} {} (0w:bytes32) 0w /\
    ld_owned_value E (SOME ((0,1),(0,0))) (SOME ((0,1),(32,0)))
      {} {} (0w:bytes32) 32w
Proof
  simp[ld_owned_value_def, ld_site_entry_def, FLOOKUP_UPDATE, ld_ptr_rel_def]
QED
