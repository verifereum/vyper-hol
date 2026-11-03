(*
 * Where a tuple's elements lie in memory, from the element types alone.
 *
 * TOP-LEVEL:
 *   tuple_in_memory_element — element i lies at its offset
 *   tuple_element_interval — element i's interval within the tuple
 *)
Theory tupleMemoryLayout
Ancestors
  list rich_list arithmetic valueEncoding exprSim vyperTyping valueTypingMemoryProps

Theorem tuple_in_memory_element:
  !vs tvs base mem i.
    LENGTH vs = LENGTH tvs /\ tuple_in_memory vs tvs base mem /\
    i < LENGTH tvs ==>
    val_in_memory (EL i tvs) (EL i vs)
      (base + SUM (MAP type_memory_size (TAKE i tvs))) mem
Proof
  Induct >> Cases_on `tvs` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `i` >> gvs[val_in_memory_def] >>
  rename1 `tuple_in_memory rest_vals rest_types
    (start + type_memory_size first_type) memory` >>
  first_x_assum (qspec_then `rest_types` mp_tac) >> simp[] >>
  disch_then drule_all >> rewrite_tac[GSYM ADD_ASSOC] >> metis_tac[ADD_COMM]
QED

Theorem tuple_element_interval:
  !tvs i.
    i < LENGTH tvs ==>
    SUM (MAP type_memory_size (TAKE i tvs)) + type_memory_size (EL i tvs) <=
    SUM (MAP type_memory_size tvs)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `i` >> gvs[] >> first_x_assum drule >> simp[]
QED

Theorem tuple_element_footprint:
  !tvs vs i.
    values_have_types tvs vs /\ i < LENGTH tvs ==>
    val_footprint (EL i tvs) (EL i vs) <= type_memory_size (EL i tvs)
Proof
  Induct >> Cases_on `vs` >> simp[value_has_type_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `i` >> gvs[] >>
  metis_tac[val_footprint_le, value_has_type_memory_wf]
QED
