Theory lowerDloadPtrMemoryWrite
Ancestors
  lowerDloadPtrRel regularCallEmitSim venomState ptrDiscipline
  list pred_set words arithmetic

Theorem dload_clean_write_byte_pair[local]:
  (p IN tn.t_mem <=> q IN un.t_mem) /\
  (p NOTIN tn.t_mem ==> read_byte p s.vs_memory = read_byte q t.vs_memory) /\
  ((a <= p /\ p < a + LENGTH bs) <=> (z <= q /\ q < z + LENGTH bs)) /\
  ((a <= p /\ p < a + LENGTH bs) ==> p-a = q-z) ==>
  (p IN (tn with t_mem := tn.t_mem DIFF {i | a <= i /\ i < a+LENGTH bs}).t_mem <=>
   q IN (un with t_mem := un.t_mem DIFF {i | z <= i /\ i < z+LENGTH bs}).t_mem) /\
  (p NOTIN (tn with t_mem := tn.t_mem DIFF {i | a <= i /\ i < a+LENGTH bs}).t_mem ==>
   read_byte p (write_memory_with_expansion a bs s).vs_memory =
   read_byte q (write_memory_with_expansion z bs t).vs_memory)
Proof
  strip_tac >> Cases_on `a <= p /\ p < a + LENGTH bs` >>
  gvs[read_byte_write_memory_with_expansion]
QED

Theorem dload_memory_match_clean_write:
  dload_memory_match lo fs tn un s t /\
  (!p q. ((p = q /\ p < lo) \/
    (?owner id b c n k. dload_live_site fs owner id b c n /\ k < n /\ p = b+k /\ q = c+k)) ==>
    ((a <= p /\ p < a + LENGTH bs) <=> (z <= q /\ q < z + LENGTH bs)) /\
    ((a <= p /\ p < a + LENGTH bs) ==> p-a = q-z)) ==>
  dload_memory_match lo fs
    (tn with t_mem := tn.t_mem DIFF {p | a <= p /\ p < a + LENGTH bs})
    (un with t_mem := un.t_mem DIFF {q | z <= q /\ q < z + LENGTH bs})
    (write_memory_with_expansion a bs s)
    (write_memory_with_expansion z bs t)
Proof
  pure_rewrite_tac [dload_memory_match_def] >> strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule dload_clean_write_byte_pair >>
      first_x_assum (qspecl_then [`i`,`i`] mp_tac) >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> irule dload_clean_write_byte_pair >>
  first_x_assum (qspecl_then [`b+k`,`c+k`] mp_tac) >>
  metis_tac[]
QED
