Theory frameIndexedCertificates
Ancestors venomExecSemantics venomState venomInst

(* Abstract indices may contain a saved-caller stack and demand handles.
   Entry and exit indices are distinct; no target execution is hidden here. *)
Definition indexed_entry_def:
  indexed_entry A R g s t <=> A g s /\ R g s t
End

Definition indexed_outcome_shape_def:
  indexed_outcome_shape Q <=> !(g:'g) (h:'g) r r'. Q g h r r' ==>
    ((?s t. r = OK s /\ r' = OK t) \/
     (?s t. r = Halt s /\ r' = Halt t) \/
     (?a b s t. r = Abort a s /\ r' = Abort b t) \/
     (?v w s t. r = IntRet v s /\ r' = IntRet w t))
End

Definition indexed_ok_exit_def:
  indexed_ok_exit A R Q <=> !(g:'g) (h:'g) s t.
    Q g h (OK s) (OK t) ==> indexed_entry A R h s t
End

Definition indexed_base_def:
  indexed_base A R InstPair Q <=> !(g:'g) i j s t r.
    indexed_entry A R g s t /\ InstPair g i j /\
    i.inst_opcode <> INVOKE /\ step_inst_base i s = r /\
    (!e. r <> Error e) ==>
    j.inst_opcode <> INVOKE /\
    ?(h:'g) r'. step_inst_base j t = r' /\ Q g h r r'
End

Definition indexed_push_def:
  indexed_push C C' A R FnPair InstPair PushRel <=>
    !(g:'g) i j s t name ops fn args cs.
    indexed_entry A R g s t /\ InstPair g i j /\
    i.inst_opcode = INVOKE /\ decode_invoke i = SOME (name,ops) /\
    lookup_function name C.ctx_functions = SOME fn /\
    eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs ==>
    ?name' ops' fn' args' ct (c:'g).
    j.inst_opcode = INVOKE /\ decode_invoke j = SOME (name',ops') /\
    lookup_function name' C'.ctx_functions = SOME fn' /\
    eval_operands ops' t = SOME args' /\ setup_callee fn' args' t = SOME ct /\
    PushRel g i j s t fn fn' cs ct c /\ FnPair c fn fn' /\
    indexed_entry A R c cs ct
End

Definition indexed_pop_def:
  indexed_pop A R Q PushRel <=>
    !(g:'g) i j s t fn fn' cs ct (c:'g) (d:'g) ret post ret' post' out.
    indexed_entry A R g s t /\ PushRel g i j s t fn fn' cs ct c /\
    Q c d (IntRet ret post) (IntRet ret' post') /\
    bind_outputs i.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state s post)) = SOME out ==>
    ?(h:'g) out'. bind_outputs j.inst_outputs ret'.iret_values
      (adopt_return_fmp ret' (merge_callee_state t post')) = SOME out' /\
    Q g h (OK out) (OK out')
End

Definition indexed_call_exit_def:
  indexed_call_exit A R Q PushRel <=> !(g:'g) i j s t fn fn' cs ct (c:'g) (d:'g) r r'.
    indexed_entry A R g s t /\ PushRel g i j s t fn fn' cs ct c /\
    Q c d r r' /\ ((?p. r = Halt p) \/ (?a p. r = Abort a p)) ==>
    ?(h:'g). Q g h r r'
End

Definition indexed_edge_def:
  indexed_edge A R Edge U V <=> !(g:'g) (h:'g) s t.
    indexed_entry A R g s t /\ Edge g h s (U s) ==>
    indexed_entry A R h (U s) (V t)
End

Definition indexed_phi_def:
  indexed_phi A R FnPair Block <=> !g fn fn' s t bb phi.
    indexed_entry A R g s t /\ FnPair g fn fn' /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK phi ==>
    ?(h:'g) bb' phi'. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    eval_phis t bb'.bb_instructions = OK phi' /\ Block h bb bb' /\
    indexed_entry A R h
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
End

Theorem indexed_push_elim:
  indexed_push C C' A R FnPair InstPair PushRel /\
  indexed_entry A R g s t /\ InstPair g i j /\
  i.inst_opcode = INVOKE /\ decode_invoke i = SOME (name,ops) /\
  lookup_function name C.ctx_functions = SOME fn /\
  eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs ==>
  ?name' ops' fn' args' ct (c:'g).
  j.inst_opcode = INVOKE /\ decode_invoke j = SOME (name',ops') /\
  lookup_function name' C'.ctx_functions = SOME fn' /\
  eval_operands ops' t = SOME args' /\ setup_callee fn' args' t = SOME ct /\
  PushRel g i j s t fn fn' cs ct c /\ FnPair c fn fn' /\
  indexed_entry A R c cs ct
Proof
  simp[indexed_push_def] >> metis_tac[]
QED

Theorem indexed_pop_elim:
  indexed_pop A R Q PushRel /\ indexed_entry A R g s t /\
  PushRel g i j s t fn fn' cs ct c /\
  Q c d (IntRet ret post) (IntRet ret' post') /\
  bind_outputs i.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s post)) = SOME out ==>
  ?(h:'g) out'. bind_outputs j.inst_outputs ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state t post')) = SOME out' /\
  Q g h (OK out) (OK out')
Proof
  simp[indexed_pop_def] >> metis_tac[]
QED

Theorem indexed_call_exit_elim:
  indexed_call_exit A R Q PushRel /\ indexed_entry A R g s t /\
  PushRel g i j s t fn fn' cs ct c /\ Q c d r r' /\
  ((?p. r = Halt p) \/ (?a p. r = Abort a p)) ==>
  ?(h:'g). Q g h r r'
Proof
  simp[indexed_call_exit_def] >> metis_tac[]
QED

Theorem indexed_edge_elim:
  indexed_edge A R Edge U V /\ indexed_entry A R g s t /\
  Edge g h s (U s) ==> indexed_entry A R h (U s) (V t)
Proof
  simp[indexed_edge_def] >> metis_tac[]
QED

Theorem indexed_phi_elim:
  indexed_phi A R FnPair Block /\ indexed_entry A R g s t /\
  FnPair g fn fn' /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK phi ==>
  ?(h:'g) bb' phi'. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  eval_phis t bb'.bb_instructions = OK phi' /\ Block h bb bb' /\
  indexed_entry A R h
    (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
    (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
Proof
  simp[indexed_phi_def] >> metis_tac[]
QED

(* Equality relocation validates the certificate boundary, not any concrete
   saved-demand invariant. Unit indices carry no saved obligations. *)
Definition identity_outcome_def:
  identity_outcome (g:unit) (h:unit) r r' <=>
    r = r' /\ (!e. r <> Error e)
End

Definition identity_push_def:
  identity_push (g:unit) i j s t fn fn' cs ct (c:unit) <=>
    i = j /\ s = t /\ fn = fn' /\ cs = ct
End

Theorem indexed_identity_shape:
  indexed_outcome_shape identity_outcome
Proof
  rw[indexed_outcome_shape_def, identity_outcome_def] >>
  Cases_on `r` >> gvs[]
QED

Theorem indexed_identity_ok_exit:
  indexed_ok_exit (\g s. T) (\g s t. s = t) identity_outcome
Proof
  simp[indexed_ok_exit_def, identity_outcome_def, indexed_entry_def]
QED

Theorem indexed_identity_base:
  indexed_base (\g s. T) (\g s t. s = t)
    (\g i j. i = j) identity_outcome
Proof
  simp[indexed_base_def, indexed_entry_def, identity_outcome_def] >>
  metis_tac[]
QED

Theorem indexed_identity_push:
  indexed_push C C (\g s. T) (\g s t. s = t)
    (\g fn fn'. fn = fn') (\g i j. i = j) identity_push
Proof
  simp[indexed_push_def, indexed_entry_def, identity_push_def] >>
  metis_tac[]
QED

Theorem indexed_identity_pop:
  indexed_pop (\g s. T) (\g s t. s = t)
    identity_outcome identity_push
Proof
  simp[indexed_pop_def, indexed_entry_def, identity_outcome_def,
       identity_push_def] >> metis_tac[]
QED

Theorem indexed_identity_call_exit:
  indexed_call_exit (\g s. T) (\g s t. s = t)
    identity_outcome identity_push
Proof
  simp[indexed_call_exit_def, indexed_entry_def, identity_outcome_def,
       identity_push_def]
QED

Theorem indexed_identity_phi:
  indexed_phi (\(g:unit) s. T) (\g s t. s = t)
    (\g fn fn'. fn = fn') (\g bb bb'. bb = bb')
Proof
  simp[indexed_phi_def, indexed_entry_def] >> metis_tac[]
QED

val _ = export_theory();
