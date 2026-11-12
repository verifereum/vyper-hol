Theory lowerDloadPairedBoundary
Ancestors
  lowerDloadOperand lowerDloadLifetime lowerDloadOwnership lowerDloadRelocation
  ptrDiscipline venomState venomExecSemantics finite_map pred_set list words

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

(* Returning keeps the current callee memory, including writes through inherited
   pointers. Only the live-owner domain is restricted. *)
Theorem ld_owned_return_memory:
  ld_byte_rel (ld_site_bytes E live) Ts Tt
    (\a. read_memory a 1 u) (\b. read_memory b 1 v) /\
  survivors SUBSET live ==>
  ld_byte_rel (ld_site_bytes (DRESTRICT E survivors) survivors) Ts Tt
    (\a. read_memory a 1 (merge_callee_state s u))
    (\b. read_memory b 1 (merge_callee_state t v))
Proof
  simp[read_memory_def, merge_callee_state_def] >>
  metis_tac[ld_site_bytes_pop, read_memory_def]
QED

Theorem ld_owned_op_selection:
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP AH v)) ==>
  ld_owned_selection E (ld_op_prov AG op) (ld_op_prov AH op)
Proof
  Cases_on `op` >> simp[ld_op_prov_def, ld_owned_selection_def]
QED

Theorem ld_owned_phi_selection:
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP AH v)) ==>
  ld_owned_selection E (ld_phi_prov prev AG i) (ld_phi_prov prev AH i)
Proof
  strip_tac >> Cases_on `prev` >> simp[ld_phi_prov_def, ld_owned_selection_def] >>
  Cases_on `resolve_phi x i.inst_operands` >>
  simp[ld_owned_selection_def] >>
  metis_tac[ld_owned_op_selection, ld_owned_selection_def]
QED

Theorem ld_owned_set_selection:
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP AH v)) /\
  ld_owned_selection E ps pt ==>
  !v. ld_owned_selection E (FLOOKUP (ld_set_prov AG outs ps) v)
    (FLOOKUP (ld_set_prov AH outs pt) v)
Proof
  simp[ld_owned_selection_def] >> rpt strip_tac >>
  Cases_on `outs` >> simp[ld_set_prov_def, FLOOKUP_DRESTRICT] >>
  Cases_on `t` >> simp[ld_set_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem ld_owned_phis_selection:
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP AH v)) ==>
  !phis v. ld_owned_selection E (FLOOKUP (ld_phis_prov prev AG phis) v)
    (FLOOKUP (ld_phis_prov prev AH phis) v)
Proof
  strip_tac >> Induct >> simp[ld_phis_prov_def] >> gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  irule ld_owned_set_selection >> simp[] >>
  metis_tac[ld_owned_phi_selection]
QED

(* Resolved PHI values use ld_owned_operand_value directly: resolution only
   identifies the operand and adds no further value hypothesis. *)

Theorem ld_positive_site_owner_unique:
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s /\
  ld_live astk L AP AG (oa,(bs,sz)) /\
  ld_live astk L AP AG (ob,(bs,sz)) /\ 0 < sz ==> oa = ob
Proof
  strip_tac >> spose_not_then assume_tac >>
  drule ld_annotated_owner_separation >>
  disch_then (qspecl_then [`(oa,(bs,sz))`, `(ob,(bs,sz))`] mp_tac) >> simp[]
QED

Theorem ld_owned_operands_defined:
  ld_owned_vars V E AG AH tn un s t /\
  (!v. MEM (Var v) ops ==> v IN V) ==>
  ((!op. MEM op ops ==> ?x. eval_operand op s = SOME x) <=>
   (!op. MEM op ops ==> ?y. eval_operand op t = SOME y))
Proof
  strip_tac >>
  `!op. MEM op ops ==> (eval_operand op s = NONE <=> eval_operand op t = NONE)` by
    (rpt strip_tac >> irule ld_owned_operand_defined >> simp[] >> metis_tac[]) >>
  eq_tac >> rpt strip_tac >>
  Cases_on `eval_operand op s` >> Cases_on `eval_operand op t` >>
  gvs[] >> metis_tac[optionTheory.option_CLAUSES]
QED

Theorem ld_owned_operands_values:
  !ops. ld_owned_vars V E AG AH tn un s t /\
    (!v. MEM (Var v) ops ==> v IN V) ==>
    (eval_operands ops s = NONE <=> eval_operands ops t = NONE) /\
    (!xs ys. eval_operands ops s = SOME xs /\
      eval_operands ops t = SOME ys ==>
      LIST_REL (\(op,x) y. ld_owned_value E (ld_op_prov AG op)
        (ld_op_prov AH op) (op_taint tn op) (op_taint un op) x y)
        (ZIP (ops,xs)) ys)
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >> strip_tac >>
  `eval_operand h s = NONE <=> eval_operand h t = NONE` by
    (irule ld_owned_operand_defined >> simp[] >> metis_tac[]) >>
  first_x_assum (mp_tac) >> simp[] >> strip_tac >>
  Cases_on `eval_operand h s` >> Cases_on `eval_operand h t` >> gvs[] >>
  Cases_on `eval_operands ops s` >> Cases_on `eval_operands ops t` >>
  gvs[] >> rpt strip_tac >> gvs[] >>
  metis_tac[ld_owned_operand_value]
QED

Theorem ld_owned_operands_source:
  ld_owned_vars V E AG AH tn un s t /\
  (!v. MEM (Var v) ops ==> v IN V) /\
  eval_operands ops s = SOME xs ==>
  ?ys. eval_operands ops t = SOME ys /\
    LIST_REL (\(op,x) y. ld_owned_value E (ld_op_prov AG op)
      (ld_op_prov AH op) (op_taint tn op) (op_taint un op) x y)
      (ZIP (ops,xs)) ys
Proof
  strip_tac >> drule_all ld_owned_operands_values >> strip_tac >>
  Cases_on `eval_operands ops t` >> gvs[] >>
  metis_tac[optionTheory.option_CLAUSES]
QED

Theorem ld_owned_operands_target:
  ld_owned_vars V E AG AH tn un s t /\
  (!v. MEM (Var v) ops ==> v IN V) /\
  eval_operands ops t = SOME ys ==>
  ?xs. eval_operands ops s = SOME xs /\
    LIST_REL (\(op,x) y. ld_owned_value E (ld_op_prov AG op)
      (ld_op_prov AH op) (op_taint tn op) (op_taint un op) x y)
      (ZIP (ops,xs)) ys
Proof
  strip_tac >> drule_all ld_owned_operands_values >> strip_tac >>
  Cases_on `eval_operands ops s` >> gvs[] >>
  metis_tac[optionTheory.option_CLAUSES]
QED

Theorem ld_owned_vars_update:
  ld_owned_vars V E AG AH tn un s t /\ ld_owned_value E ps pt Ms Mt x y ==>
  ld_owned_vars V E (ld_set_prov AG [out] ps) (ld_set_prov AH [out] pt)
    (tn with t_var := set_var_taint tn.t_var [out] Ms)
    (un with t_var := set_var_taint un.t_var [out] Mt)
    (update_var out x s) (update_var out y t)
Proof
  simp[ld_owned_vars_def] >> rpt strip_tac >>
  Cases_on `v = out` >>
  gvs[update_var_def, lookup_var_def, op_taint_def, set_var_taint_def,
      FLOOKUP_UPDATE] >>
  Cases_on `ps` >> Cases_on `pt` >>
  gvs[ld_set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem ld_owned_value_offset_add:
  ld_owned_value E ps pt {} {} x y ==>
  ld_owned_value E ps pt {} {} (x+k) (y+k)
Proof
  Cases_on `ps` >> simp[ld_owned_value_def]
  >- metis_tac[ld_mask_word_clean, ld_mask_word_def] >>
  PairCases_on `x'` >> simp[] >> metis_tac[ld_ptr_rel_add]
QED

Theorem ld_owned_value_offset_sub:
  ld_owned_value E ps pt {} {} x y ==>
  ld_owned_value E ps pt {} {} (x-k) (y-k)
Proof
  Cases_on `ps` >> simp[ld_owned_value_def]
  >- metis_tac[ld_mask_word_clean, ld_mask_word_def] >>
  PairCases_on `x'` >> simp[] >> metis_tac[ld_ptr_rel_sub]
QED
