(* Original-name operand relations: scalar bytes and site-relative pointers. *)
Theory lowerDloadOperand
Ancestors
  lowerDloadRelocation accountsRelProps venomState ptrDiscipline byte
  finite_map pred_set list

Definition ld_mask_word_def:
  ld_mask_word Ms Mt (x:bytes32) y <=>
    Mt SUBSET Ms /\
    !k. k < 32 /\ k NOTIN Ms ==>
      EL k (word_to_bytes x T) = EL k (word_to_bytes y T)
End

Definition ld_value_def:
  ld_value B ps pt Ms Mt (x:bytes32) y <=>
    case ps of
      NONE => pt = NONE /\ ld_mask_word Ms Mt x y
    | SOME (bs,sz) => pt = SOME (B (bs,sz),sz) /\ Mt SUBSET Ms /\
                     ld_ptr_rel bs (B (bs,sz)) x y
End

Definition ld_vars_def:
  ld_vars V B G H tn un s t <=>
    s.vs_labels = t.vs_labels /\
    !v. v IN V ==>
      (lookup_var v s = NONE <=> lookup_var v t = NONE) /\
      (!x y. lookup_var v s = SOME x /\ lookup_var v t = SOME y ==>
        ld_value B (FLOOKUP G v) (FLOOKUP H v)
          (op_taint tn (Var v)) (op_taint un (Var v)) x y)
End

Theorem ld_mask_word_identity:
  ld_mask_word M M x x
Proof
  simp[ld_mask_word_def]
QED

Theorem ld_mask_word_clean:
  ld_mask_word {} Mt x y ==> Mt = {} /\ x = y
Proof
  simp[ld_mask_word_def] >> strip_tac >>
  irule word_to_bytes_EL_eq >> simp[]
QED

Theorem ld_operand_defined:
  ld_vars V B G H tn un s t /\ (!v. op = Var v ==> v IN V) ==>
  (eval_operand op s = NONE <=> eval_operand op t = NONE)
Proof
  Cases_on `op` >> simp[eval_operand_def, ld_vars_def] >> metis_tac[]
QED

Theorem ld_operand_value:
  ld_vars V B G H tn un s t /\ (!v. op = Var v ==> v IN V) /\
  eval_operand op s = SOME x /\ eval_operand op t = SOME y ==>
  ld_value B (op_prov G op) (op_prov H op)
    (op_taint tn op) (op_taint un op) x y
Proof
  Cases_on `op` >>
  simp[eval_operand_def, op_prov_def, op_taint_def, ld_vars_def] >>
  rpt strip_tac >> gvs[ld_value_def, ld_mask_word_def] >> metis_tac[]
QED

Theorem ld_operand_clean:
  ld_vars V B G H tn un s t /\ (!v. op = Var v ==> v IN V) /\
  op_prov G op = NONE /\ op_taint tn op = {} ==>
  eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `eval_operand op s = NONE <=> eval_operand op t = NONE` by
    metis_tac[ld_operand_defined] >>
  Cases_on `eval_operand op s` >> Cases_on `eval_operand op t` >> gvs[] >>
  drule_all ld_operand_value >>
  simp[ld_value_def] >> metis_tac[ld_mask_word_clean]
QED

Theorem ld_operands_clean:
  !ops. ld_vars V B G H tn un s t /\
  EVERY (\op. (!v. op = Var v ==> v IN V) /\
              op_prov G op = NONE /\ op_taint tn op = {}) ops ==>
  eval_operands ops s = eval_operands ops t
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  `eval_operand h s = eval_operand h t` by metis_tac[ld_operand_clean] >>
  `eval_operands ops s = eval_operands ops t` by metis_tac[] >> simp[]
QED

Theorem ld_value_compare:
  ld_value B (SOME (bs,sz)) px Ms Mt x x' /\
  ld_value B (SOME (bs,sz)) py Ns Nt y y' /\
  bs <= w2n x /\ w2n x <= bs+sz /\
  bs <= w2n y /\ w2n y <= bs+sz /\
  bs+sz < dimword(:256) /\ B (bs,sz)+sz < dimword(:256) ==>
  ((x <+ y <=> x' <+ y') /\
   (y <+ x <=> y' <+ x') /\ (x = y <=> x' = y'))
Proof
  strip_tac >> gvs[ld_value_def] >>
  `B (bs,sz) + sz < dimword (:256)` by decide_tac >>
  irule ld_ptr_rel_compare >>
  qexistsl [`bs`, `B (bs,sz)`, `sz`] >> simp[]
QED

Theorem ld_vars_update:
  ld_vars V B G H tn un s t /\ ld_value B ps pt Ms Mt x y ==>
  ld_vars V B (set_prov G [out] ps) (set_prov H [out] pt)
    (tn with t_var := set_var_taint tn.t_var [out] Ms)
    (un with t_var := set_var_taint un.t_var [out] Mt)
    (update_var out x s) (update_var out y t)
Proof
  simp[ld_vars_def] >> rpt strip_tac >>
  Cases_on `v = out` >>
  gvs[update_var_def, lookup_var_def, op_taint_def, set_var_taint_def,
      FLOOKUP_UPDATE] >>
  Cases_on `ps` >> Cases_on `pt` >>
  gvs[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem ld_value_add:
  ld_value B (SOME (bs,sz)) pt Ms Mt x y ==>
  ld_value B (SOME (bs,sz)) pt Ms Mt (x+k) (y+k)
Proof
  simp[ld_value_def] >> metis_tac[ld_ptr_rel_add]
QED

Theorem ld_value_sub:
  ld_value B (SOME (bs,sz)) pt Ms Mt x y ==>
  ld_value B (SOME (bs,sz)) pt Ms Mt (x-k) (y-k)
Proof
  simp[ld_value_def] >> metis_tac[ld_ptr_rel_sub]
QED

Theorem ld_vars_update_untracked:
  ld_vars V B G H tn un s t /\ out NOTIN V ==>
  ld_vars V B (set_prov G [out] ps) (set_prov H [out] pt)
    (tn with t_var := set_var_taint tn.t_var [out] Ms)
    (un with t_var := set_var_taint un.t_var [out] Mt)
    (update_var out x s) (update_var out y t)
Proof
  simp[ld_vars_def, update_var_def] >> rpt strip_tac >>
  `v <> out` by metis_tac[] >>
  gvs[lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `ps` >> Cases_on `pt` >>
  gvs[update_var_def, lookup_var_def, op_taint_def, set_var_taint_def,
      set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >> metis_tac[]
QED
