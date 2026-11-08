(* Small-context indexed geometry for unread robust members. Typing itself
   uses vyperTypeDefaults.values_have_types_LIST_REL, not a duplicate conversion. *)
Theory assignTuplePtrUnreadBounds
Ancestors
  tupleMemoryLayout valueTypingMemoryProps valueEncoding valueEncodingProps
  vyperTypeDefaults list arithmetic valueEncodingProofs

Theorem tuple_unread_element_bounds_ptr:
  values_have_types tvs vs /\ i < LENGTH tvs /\
  a = addr + type_memory_size head + SUM (MAP type_memory_size (TAKE i tvs)) /\
  addr + type_memory_size_list (head::tvs) <= b + sz ==>
  addr + type_memory_size head <= a /\
  a + val_footprint (EL i tvs) (EL i vs) <= b + sz
Proof
  strip_tac >>
  drule tuple_element_interval >> strip_tac >>
  drule_all tuple_element_footprint >> strip_tac >>
  fs[type_memory_size_def, type_memory_size_list_sum] >> decide_tac
QED

(* Probe the exported conversion in precisely the consumer's small context;
   this combined resource boundary also supplies wf without unfolding val_wf. *)
Theorem tuple_unread_element_resources_ptr:
  values_have_types tvs vs /\ i < LENGTH tvs /\
  a = addr + type_memory_size head + SUM (MAP type_memory_size (TAKE i tvs)) /\
  addr + type_memory_size_list (head::tvs) <= b + sz ==>
  val_wf (EL i tvs) (EL i vs) /\
  addr + type_memory_size head <= a /\
  a + val_footprint (EL i tvs) (EL i vs) <= b + sz
Proof
  strip_tac >> drule_all tuple_unread_element_bounds_ptr >> strip_tac >> simp[] >>
  irule value_has_type_memory_wf >>
  fs[values_have_types_LIST_REL, LIST_REL_EL_EQN]
QED
