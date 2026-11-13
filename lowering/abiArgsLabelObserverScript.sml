Theory abiArgsLabelObserver
Ancestors
  abiArgsCompilerImage abiArgsObservation

Theorem abi_lower_value_label_observer:
  lower_value compile_expr ce ty e sa = (Label l,sb) /\
  frag_exec ctx sa sb P Q (\r. F) /\ fn_has_code sa sb fn /\
  P s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t.vs_labels = s.vs_labels
Proof
  strip_tac >>
  irule abi_frag_halting_observer >> simp[] >>
  qexistsl_tac [`P`, `ctx`, `fn with fn_blocks :=
    <|bb_label := sb.cs_current_bb;
      bb_instructions := sb.cs_current_insts ++ [mk_inst 0 STOP [] []]|> :: fn.fn_blocks`, `sa`] >>
  simp[] >> conj_tac
  >- metis_tac[abi_stop_observer_endpoint] >>
  irule abi_stop_observer_contains >> simp[] >>
  metis_tac[abi_image_lower_value_label_no_collision]
QED
