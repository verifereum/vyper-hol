Theory deadStoreElimPositional
Ancestors
  deadStoreElimStructure deadStoreElimLiveness

Theorem all_dead_stores_suffix:
  wf_function fn /\ all_dead_stores ids cfg aliases bp sp fn /\
  MEM bb fn.fn_blocks /\ get_instruction bb idx = SOME inst /\
  inst.inst_id IN ids ==>
  dse_suffix_dead cfg aliases bp (bp_get_write_location bp inst sp)
    sp fn bb (SUC idx)
Proof
  strip_tac >> rewrite_tac[dse_suffix_dead_after_store] >>
  drule_all all_dead_stores_at >> simp_tac bool_ss []
QED
