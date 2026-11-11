Theory concretizePtrValueTransport
Ancestors concretizePtrStagePlacements ptrDiscipline venomState venomInst
  words finite_map list pred_set option

Definition ptr_value_transport_def:
  ptr_value_transport births positions tag mask (x:bytes32) y <=>
    case tag of
      NONE => word_agree_except mask x y
    | SOME (token,aid) =>
        ?base size pos.
          FLOOKUP births (token,aid) = SOME (base,size) /\
          FLOOKUP positions (Allocation aid) = SOME (pos,size) /\
          y = x - n2w base + n2w pos
End

Definition ptr_lookup_transport_def:
  ptr_lookup_transport births positions tag mask x y <=>
    case (x,y) of
      (NONE,NONE) => T
    | (SOME a,SOME b) => ptr_value_transport births positions tag mask a b
    | _ => F
End

Definition ptr_vars_transport_def:
  ptr_vars_transport births positions TG tn s t <=>
    !v. ptr_lookup_transport births positions (FLOOKUP TG v)
      (op_taint tn (Var v)) (lookup_var v s) (lookup_var v t)
End

Definition ptr_args_transport_def:
  ptr_args_transport births positions tags masks xs ys <=>
    LENGTH tags = LENGTH xs /\ LENGTH masks = LENGTH xs /\
    LIST_REL (\(tag,mask,x) y. ptr_value_transport births positions tag mask x y)
      (ZIP (tags,ZIP (masks,xs))) ys
End

Theorem ptr_value_transport_scalar_empty:
  ptr_value_transport births positions NONE {} x y <=> x = y
Proof
  simp[ptr_value_transport_def, word_agree_except_bits,
    GSYM wordsTheory.WORD_EQ, wordsTheory.word_bit_def]
QED

Theorem ptr_value_transport_refl:
  ptr_value_transport births positions NONE mask x x
Proof
  simp[ptr_value_transport_def, word_agree_except_def]
QED

Theorem ptr_value_transport_add_right:
  ptr_value_transport births positions (SOME tag) mask x y ==>
  ptr_value_transport births positions (SOME tag) mask (x+k) (y+k)
Proof
  PairCases_on `tag` >> simp[ptr_value_transport_def] >> rpt strip_tac >>
  rpt (goal_assum (drule_at Any)) >> wordsLib.WORD_DECIDE_TAC
QED

Theorem ptr_value_transport_add_left:
  ptr_value_transport births positions (SOME tag) mask x y ==>
  ptr_value_transport births positions (SOME tag) mask (k+x) (k+y)
Proof
  once_rewrite_tac[WORD_ADD_COMM] >>
  MATCH_ACCEPT_TAC ptr_value_transport_add_right
QED

Theorem ptr_value_transport_sub_right:
  ptr_value_transport births positions (SOME tag) mask x y ==>
  ptr_value_transport births positions (SOME tag) mask (x-k) (y-k)
Proof
  PairCases_on `tag` >> simp[ptr_value_transport_def] >> rpt strip_tac >>
  rpt (goal_assum (drule_at Any)) >> wordsLib.WORD_DECIDE_TAC
QED

Theorem ptr_lookup_transport_some:
  ptr_lookup_transport births positions tag mask (SOME x) y <=>
  ?z. y = SOME z /\ ptr_value_transport births positions tag mask x z
Proof
  Cases_on `y` >> simp[ptr_lookup_transport_def]
QED

Theorem ptr_lookup_transport_none:
  ptr_lookup_transport births positions tag mask NONE y <=> y = NONE
Proof
  Cases_on `y` >> simp[ptr_lookup_transport_def]
QED

Theorem ptr_vars_transport_eval:
  ptr_vars_transport births positions TG tn s t /\
  ((?v. op = Var v) \/ (?w. op = Lit w)) ==>
  ptr_lookup_transport births positions (op_prov TG op) (op_taint tn op)
    (eval_operand op s) (eval_operand op t)
Proof
  simp[ptr_vars_transport_def] >> strip_tac >>
  gvs[eval_operand_def, op_prov_def, op_taint_def, ptr_lookup_transport_def,
      ptr_value_transport_refl]
QED

Theorem ptr_vars_transport_eval_all:
  ptr_vars_transport births positions TG tn s t /\
  s.vs_labels = t.vs_labels ==>
  ptr_lookup_transport births positions (op_prov TG op) (op_taint tn op)
    (eval_operand op s) (eval_operand op t)
Proof
  strip_tac >> Cases_on `op`
  >- (irule ptr_vars_transport_eval >> simp[])
  >- (irule ptr_vars_transport_eval >> simp[]) >>
  simp[eval_operand_def, op_prov_def, op_taint_def] >>
  Cases_on `FLOOKUP t.vs_labels s'` >>
  simp[ptr_lookup_transport_def, ptr_value_transport_refl]
QED

Theorem ptr_args_transport_lengths:
  ptr_args_transport births positions tags masks xs ys ==>
  LENGTH tags = LENGTH xs /\ LENGTH masks = LENGTH xs /\ LENGTH ys = LENGTH xs
Proof
  simp[ptr_args_transport_def] >> strip_tac >>
  drule LIST_REL_LENGTH >> simp[]
QED

Theorem ptr_args_transport_el:
  ptr_args_transport births positions tags masks xs ys /\ i < LENGTH xs ==>
  ptr_value_transport births positions (EL i tags) (EL i masks) (EL i xs) (EL i ys)
Proof
  simp[ptr_args_transport_def, LIST_REL_EL_EQN] >> rpt strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[EL_ZIP]
QED

Theorem ptr_lookup_transport_some_right:
  ptr_lookup_transport births positions tag mask x (SOME y) <=>
  ?z. x = SOME z /\ ptr_value_transport births positions tag mask z y
Proof
  Cases_on `x` >> simp[ptr_lookup_transport_def]
QED

Theorem ptr_lookup_transport_none_right:
  ptr_lookup_transport births positions tag mask x NONE <=> x = NONE
Proof
  Cases_on `x` >> simp[ptr_lookup_transport_def]
QED

(* Both branches of label resolution, including simultaneous failure. *)
Theorem ptr_label_lookup_probe:
  eval_operand (Label "code_end")
    ((init_venom_state "entry") with
      vs_labels := FEMPTY |+ ("code_end", 64w)) = SOME 64w /\
  eval_operand (Label "missing")
    ((init_venom_state "entry") with
      vs_labels := FEMPTY |+ ("code_end", 64w)) = NONE
Proof
  EVAL_TAC
QED

Theorem ptr_vars_transport_eval_source:
  ptr_vars_transport births positions TG tn s t /\
  s.vs_labels = t.vs_labels /\ eval_operand op t = SOME y ==>
  ?x. eval_operand op s = SOME x /\
    ptr_value_transport births positions (op_prov TG op) (op_taint tn op) x y
Proof
  strip_tac >> drule_all ptr_vars_transport_eval_all >>
  disch_then (qspec_then `op` mp_tac) >>
  simp[ptr_lookup_transport_some_right]
QED
