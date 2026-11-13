Theory frameIndexedComposition
Ancestors frameIndexedCertificates frameFiniteExecution

Definition indexed_lookup_def:
  indexed_lookup A R BlockPair InstPair <=> !bb bb' g s t i.
    BlockPair bb bb' /\ indexed_entry A R g s t /\
    get_instruction bb s.vs_inst_idx = SOME i ==>
    ?j. get_instruction bb' t.vs_inst_idx = SOME j /\ InstPair g i j /\
        (is_terminator i.inst_opcode <=> is_terminator j.inst_opcode)
End

Definition indexed_admin_entry_def:
  indexed_admin_entry A R Admin <=> !(h:'g) (k:'g) p q p' q'.
    Admin h k p q p' q' /\ indexed_entry A R h p q ==>
    indexed_entry A R k p' q'
End

Definition indexed_admin_refl_def:
  indexed_admin_refl Admin <=> !(h:'g) p q. Admin h h p q p q
End

Definition indexed_splice_def:
  indexed_splice Q Admin <=> !(g:'g) (h:'g) (k:'g) (d:'g) p q p' q' r r'.
    Q g h (OK p) (OK q) /\ Admin h k p q p' q' /\ Q k d r r' ==>
    Q g d r r'
End

Definition indexed_halted_def:
  indexed_halted Q <=> !(g:'g) (h:'g) p q.
    Q g h (OK p) (OK q) ==> (p.vs_halted <=> q.vs_halted)
End

Definition indexed_halt_def:
  indexed_halt Q <=> !(g:'g) (h:'g) p q.
    Q g h (OK p) (OK q) /\ p.vs_halted ==> Q g h (Halt p) (Halt q)
End

Definition indexed_increment_def:
  indexed_increment A R BlockPair InstPair Q Admin <=>
    !bb bb' (g:'g) (h:'g) s t i j p q.
    BlockPair bb bb' /\ indexed_entry A R g s t /\
    get_instruction bb s.vs_inst_idx = SOME i /\
    get_instruction bb' t.vs_inst_idx = SOME j /\ InstPair g i j /\
    ~is_terminator i.inst_opcode /\ Q g h (OK p) (OK q) ==>
    ?(k:'g). Admin h k p q
      (p with vs_inst_idx := SUC s.vs_inst_idx)
      (q with vs_inst_idx := SUC t.vs_inst_idx)
End

(* Unlike indexed_phi, this boundary also accounts for the outcome prefix. *)
Definition indexed_phi_prefix_def:
  indexed_phi_prefix A R FnPair BlockPair Q <=>
    !(g:'g) fn fn' s t bb phi.
    indexed_entry A R g s t /\ FnPair fn fn' /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK phi ==>
    ?(h:'g) bb' phi'.
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    eval_phis t bb'.bb_instructions = OK phi' /\ BlockPair bb bb' /\
    indexed_entry A R h
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) /\
    (!(d:'g) r r'. Q h d r r' ==> Q g d r r')
End

Theorem indexed_lookup_elim:
  indexed_lookup A R BlockPair InstPair /\ BlockPair bb bb' /\
  indexed_entry A R g s t /\ get_instruction bb s.vs_inst_idx = SOME i ==>
  ?j. get_instruction bb' t.vs_inst_idx = SOME j /\ InstPair g i j /\
      (is_terminator i.inst_opcode <=> is_terminator j.inst_opcode)
Proof
  simp[indexed_lookup_def] >> metis_tac[]
QED

Theorem indexed_admin_entry_elim:
  indexed_admin_entry A R Admin /\ Admin h k p q p' q' /\
  indexed_entry A R h p q ==> indexed_entry A R k p' q'
Proof
  simp[indexed_admin_entry_def] >> metis_tac[]
QED

Theorem indexed_admin_refl_elim:
  indexed_admin_refl Admin ==> Admin h h p q p q
Proof
  simp[indexed_admin_refl_def]
QED

Theorem indexed_splice_elim:
  indexed_splice Q Admin /\ Q g h (OK p) (OK q) /\
  Admin h k p q p' q' /\ Q k d r r' ==> Q g d r r'
Proof
  simp[indexed_splice_def] >> metis_tac[]
QED

Theorem indexed_halted_elim:
  indexed_halted Q /\ Q g h (OK p) (OK q) ==>
  (p.vs_halted <=> q.vs_halted)
Proof
  simp[indexed_halted_def] >> metis_tac[]
QED

Theorem indexed_halt_elim:
  indexed_halt Q /\ Q g h (OK p) (OK q) /\ p.vs_halted ==>
  Q g h (Halt p) (Halt q)
Proof
  simp[indexed_halt_def] >> metis_tac[]
QED

Theorem indexed_increment_elim:
  indexed_increment A R BlockPair InstPair Q Admin /\
  BlockPair bb bb' /\ indexed_entry A R g s t /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  get_instruction bb' t.vs_inst_idx = SOME j /\ InstPair g i j /\
  ~is_terminator i.inst_opcode /\ Q g h (OK p) (OK q) ==>
  ?k. Admin h k p q (p with vs_inst_idx := SUC s.vs_inst_idx)
    (q with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  simp[indexed_increment_def] >> metis_tac[]
QED

Theorem indexed_phi_prefix_elim:
  indexed_phi_prefix A R FnPair BlockPair Q /\ indexed_entry A R g s t /\
  FnPair fn fn' /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK phi ==>
  ?h bb' phi'. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  eval_phis t bb'.bb_instructions = OK phi' /\ BlockPair bb bb' /\
  indexed_entry A R h
    (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
    (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) /\
  (!d r r'. Q h d r r' ==> Q g d r r')
Proof
  simp[indexed_phi_prefix_def] >> metis_tac[]
QED

(* On related input pairs this requires equality of the updated states.
   On unrelated pairs it is unconstrained: administrative reflexivity is
   deliberately required even outside the entry invariant. *)
Definition identity_admin_def:
  identity_admin (h:unit) (k:unit) p q p' q' <=> (p = q ==> p' = q')
End

Theorem indexed_identity_lookup:
  indexed_lookup (\g s. T) (\(g:unit) s t. s = t)
    (\bb bb'. bb = bb') (\g i j. i = j)
Proof
  simp[indexed_lookup_def, indexed_entry_def]
QED

Theorem indexed_identity_admin_entry:
  indexed_admin_entry (\g s. T) (\g s t. s = t) identity_admin
Proof
  simp[indexed_admin_entry_def, indexed_entry_def, identity_admin_def]
QED

Theorem indexed_identity_admin_refl:
  indexed_admin_refl identity_admin
Proof
  simp[indexed_admin_refl_def, identity_admin_def]
QED

Theorem indexed_identity_splice:
  indexed_splice identity_outcome identity_admin
Proof
  simp[indexed_splice_def, identity_outcome_def]
QED

Theorem indexed_identity_halted:
  indexed_halted identity_outcome
Proof
  simp[indexed_halted_def, identity_outcome_def]
QED

Theorem indexed_identity_halt:
  indexed_halt identity_outcome
Proof
  simp[indexed_halt_def, identity_outcome_def]
QED

Theorem indexed_identity_increment:
  indexed_increment (\g s. T) (\g s t. s = t)
    (\bb bb'. bb = bb') (\g i j. i = j) identity_outcome identity_admin
Proof
  simp[indexed_increment_def, indexed_entry_def, identity_outcome_def,
       identity_admin_def]
QED

Theorem indexed_identity_phi_prefix:
  indexed_phi_prefix (\g s. T) (\g s t. s = t)
    (\fn fn'. fn = fn') (\bb bb'. bb = bb') identity_outcome
Proof
  simp[indexed_phi_prefix_def, indexed_entry_def, identity_outcome_def] >>
  metis_tac[]
QED

Definition indexed_composition_def:
  indexed_composition A R FnPair BlockPair InstPair Q Admin <=>
    indexed_lookup A R BlockPair InstPair /\
    indexed_admin_entry A R Admin /\ indexed_admin_refl Admin /\
    indexed_splice Q Admin /\ indexed_halted Q /\ indexed_halt Q /\
    indexed_increment A R BlockPair InstPair Q Admin /\
    indexed_phi_prefix A R FnPair BlockPair Q
End

Theorem indexed_identity_complete:
  indexed_outcome_shape identity_outcome /\
  indexed_ok_exit (\g s. T) (\g s t. s = t) identity_outcome /\
  indexed_base (\g s. T) (\g s t. s = t)
    (\g i j. i = j) identity_outcome /\
  indexed_push C C (\g s. T) (\g s t. s = t)
    (\g fn fn'. fn = fn') (\g i j. i = j) identity_push /\
  indexed_pop (\g s. T) (\g s t. s = t) identity_outcome identity_push /\
  indexed_call_exit (\g s. T) (\g s t. s = t)
    identity_outcome identity_push /\
  indexed_composition (\g s. T) (\g s t. s = t)
    (\fn fn'. fn = fn') (\bb bb'. bb = bb') (\g i j. i = j)
    identity_outcome identity_admin
Proof
  simp[indexed_identity_shape, indexed_identity_ok_exit,
       indexed_identity_base, indexed_identity_push, indexed_identity_pop,
       indexed_identity_call_exit, indexed_composition_def,
       indexed_identity_lookup, indexed_identity_admin_entry,
       indexed_identity_admin_refl, indexed_identity_splice,
       indexed_identity_halted, indexed_identity_halt,
       indexed_identity_increment, indexed_identity_phi_prefix]
QED

val _ = export_theory();
