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

Theorem dload_write_sites_separate[local]:
  dload_live_layout lo sf tf fs /\
  dload_live_site fs owner id b c n /\
  dload_live_site fs owner' id' b' c' n' /\
  (owner <> owner' \/ id <> id') /\ 0 < n /\ 0 < n' ==>
  (b+n <= b' \/ b'+n' <= b) /\
  (c+n <= c' \/ c'+n' <= c)
Proof
  simp[dload_live_layout_def, dload_live_site_def] >>
  metis_tac[]
QED

Theorem dload_write_range_geometry:
  dload_live_layout lo sf tf fs /\
  ((a = z /\ a + len <= lo) \/
   (?owner id b c n d.
      dload_live_site fs owner id b c n /\
      a = b+d /\ z = c+d /\ d+len <= n)) ==>
  !p q. ((p = q /\ p < lo) \/
    (?owner id b c n k.
      dload_live_site fs owner id b c n /\ k < n /\
      p = b+k /\ q = c+k)) ==>
   (((a <= p /\ p < a+len) <=> (z <= q /\ q < z+len)) /\
    ((a <= p /\ p < a+len) ==> p-a = q-z))
Proof
  Cases_on `len = 0` >- simp[] >>
  strip_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >- (drule_all dload_live_site_bounds >> strip_tac >> decide_tac)
  >- (drule_all dload_live_site_bounds >> strip_tac >> decide_tac) >>
  rename1 `dload_live_site fs owner' id' b' c' n'` >>
  Cases_on `owner = owner' /\ id = id'`
  >- (gvs[] >>
      qpat_x_assum `dload_live_site fs owner id b c n`
        (mp_then Any mp_tac dload_live_site_target_unique) >>
      disch_then drule >> strip_tac >> gvs[] >> decide_tac) >>
  `0 < n /\ 0 < n'` by decide_tac >>
  `(b+n <= b' \/ b'+n' <= b) /\
   (c+n <= c' \/ c'+n' <= c)` by
    metis_tac[dload_write_sites_separate] >>
  decide_tac
QED

Theorem dload_memory_match_clean_write_region:
  dload_memory_match lo fs tn un s t /\
  dload_live_layout lo sf tf fs /\
  ((a = z /\ a + LENGTH bs <= lo) \/
   (?owner id b c n d.
      dload_live_site fs owner id b c n /\
      a = b+d /\ z = c+d /\ d+LENGTH bs <= n)) ==>
  dload_memory_match lo fs
    (tn with t_mem := tn.t_mem DIFF {p | a <= p /\ p < a + LENGTH bs})
    (un with t_mem := un.t_mem DIFF {q | z <= q /\ q < z + LENGTH bs})
    (write_memory_with_expansion a bs s)
    (write_memory_with_expansion z bs t)
Proof
  disch_tac >> irule dload_memory_match_clean_write >> conj_tac
  >- (match_mp_tac dload_write_range_geometry >> metis_tac[]) >>
  metis_tac[]
QED
