Theory frameRelocationValues
Ancestors venomExecSemantics venomState finite_map list words

(* Definedness and value agreement are deliberately independent. *)
Definition variable_domains_def:
  variable_domains s t <=> !v. (lookup_var v s = NONE <=> lookup_var v t = NONE)
End

Definition variables_agree_on_def:
  variables_agree_on P s t <=> !v. P v ==> lookup_var v s = lookup_var v t
End

Theorem variable_domains_update:
  variable_domains s t ==>
  variable_domains (update_var v x s) (update_var v y t)
Proof
  simp[variable_domains_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem variable_domains_bind_fold:
  !outs xs ys s t.
  variable_domains s t /\ LENGTH xs = LENGTH outs /\ LENGTH ys = LENGTH outs ==>
  variable_domains
    (FOLDL (\st (v,w). update_var v w st) s (ZIP (outs,xs)))
    (FOLDL (\st (v,w). update_var v w st) t (ZIP (outs,ys)))
Proof
  Induct >> Cases_on `xs` >> Cases_on `ys` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[variable_domains_update]
QED

Theorem variable_domains_bind_outputs:
  variable_domains s t /\ LENGTH xs = LENGTH outs /\ LENGTH ys = LENGTH outs ==>
  ?s' t'. bind_outputs outs xs s = SOME s' /\ bind_outputs outs ys t = SOME t' /\
    variable_domains s' t'
Proof
  simp[bind_outputs_def] >> metis_tac[variable_domains_bind_fold]
QED

(* P selects the nonopaque, untainted scalar variables at a use site. *)
Theorem scalar_operand_agreement:
  variables_agree_on P s t /\ s.vs_labels = t.vs_labels /\
  (!v. op = Var v ==> P v) ==>
  eval_operand op s = eval_operand op t
Proof
  Cases_on `op` >> simp[eval_operand_def, variables_agree_on_def]
QED

Theorem operand_domain_agreement:
  variable_domains s t /\ s.vs_labels = t.vs_labels ==>
  (eval_operand op s = NONE <=> eval_operand op t = NONE)
Proof
  Cases_on `op` >> simp[eval_operand_def, variable_domains_def]
QED

(* One group identity supports both copy and affine displacement.  It does
   not assert natural containment of intermediate pointer values. *)
Theorem word_displacement_affine:
  !x y b d c:'a word.
    x - b = y - d ==>
    (x + c) - b = (y + c) - d
Proof
  rpt strip_tac >>
  `!w a z:'a word. (w + z) - a = (w - a) + z` by
    (simp[word_sub_def] >> metis_tac[WORD_ADD_COMM, WORD_ADD_ASSOC]) >>
  simp[]
QED

Theorem word_displacement_sub_scalar:
  !x y b d c:'a word.
    x - b = y - d ==> (x - c) - b = (y - c) - d
Proof
  simp[Once word_sub_def] >> metis_tac[word_displacement_affine, word_sub_def]
QED

Theorem word_displacement_scalar_sub:
  !x y b d c:'a word.
    x - b = y - d ==> (c - x) - -b = (c - y) - -d
Proof
  rpt strip_tac >>
  `!w a z:'a word. (z - w) - -a = z - (w - a)` by
    simp[word_sub_def, WORD_NEG_ADD, WORD_ADD_ASSOC] >>
  simp[]
QED
