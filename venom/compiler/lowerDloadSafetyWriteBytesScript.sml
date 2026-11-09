(* Masked byte-list overwrite transport. *)
Theory lowerDloadSafetyWriteBytes
Ancestors
  lowerDloadSafetyBytes lowerDloadSafetyKernel venomState regularCallEmitSim
  finite_map pred_set list arithmetic

Theorem ld_write_interval[local]:
  (!(off:num) n i. (?j. i = j+off /\ j < n) <=> off <= i /\ i < off+n) /\
  (!(off:num) n i M. (?j. i = j+off /\ j < n /\ j IN M) <=>
    off <= i /\ i < off+n /\ i-off IN M)
Proof
  conj_tac
  >- (rpt gen_tac >> eq_tac >- (strip_tac >> gvs[] >> decide_tac) >>
      strip_tac >> qexists_tac `i-off` >> decide_tac) >>
  rpt gen_tac >> eq_tac
  >- (strip_tac >> gvs[] >> decide_tac) >>
  strip_tac >> qexists_tac `i-off` >> simp[] >> decide_tac
QED

Theorem ld_memory_write_low:
  ld_memory lo A tn s t /\ off+n <= lo /\
  LENGTH xs = n /\ LENGTH ys = n /\
  (!j. j < n /\ j NOTIN M ==> EL j xs = EL j ys) /\
  (!a u v z. FLOOKUP A a = SOME (u,v,z) ==> lo <= u /\ lo <= v) /\
  tn'.t_mem = (tn.t_mem DIFF {off+j | j < n}) UNION
                         {off+j | j < n /\ j IN M} ==>
  ld_memory lo A tn'
    (write_memory_with_expansion off xs s)
    (write_memory_with_expansion off ys t)
Proof
  strip_tac >> irule ld_memory_transport >>
  qexistsl_tac [`{off+j | j < n}`, `s`, `t`, `tn`] >>
  simp[ld_write_interval] >> conj_tac
  >- (rpt strip_tac >> simp[read_byte_write_memory_with_expansion] >>
      Cases_on `off <= i /\ i < off+n` >> gvs[ld_write_interval] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `lo <= b /\ lo <= c` by metis_tac[] >>
  `~(off <= b+j /\ b+j < off+n) /\
   ~(off <= c+j /\ c+j < off+n)` by decide_tac >>
  gvs[read_byte_write_memory_with_expansion, ld_write_interval] >> decide_tac
QED

Theorem ld_memory_write_slot:
  ld_memory lo A tn s t /\
  FLOOKUP A k = SOME (b,c,sz) /\ delta+n <= sz /\
  LENGTH xs = n /\ LENGTH ys = n /\
  (!j. j < n /\ j NOTIN M ==> EL j xs = EL j ys) /\
  (!a u v z. FLOOKUP A a = SOME (u,v,z) ==> lo <= u /\ lo <= v) /\
  (!a u v z. FLOOKUP A a = SOME (u,v,z) /\ a <> k /\ 0 < z /\ 0 < sz ==>
    (u+z <= b \/ b+sz <= u) /\ (v+z <= c \/ c+sz <= v)) /\
  tn'.t_mem = (tn.t_mem DIFF {b+delta+j | j < n}) UNION
                         {b+delta+j | j < n /\ j IN M} ==>
  ld_memory lo A tn'
    (write_memory_with_expansion (b+delta) xs s)
    (write_memory_with_expansion (c+delta) ys t)
Proof
  strip_tac >> Cases_on `n = 0`
  >- (gvs[ld_memory_def, read_byte_write_memory_with_expansion] >> metis_tac[]) >>
  `lo <= b /\ lo <= c` by metis_tac[] >>
  irule ld_memory_transport >>
  qexistsl_tac [`{b+delta+j | j < n}`, `s`, `t`, `tn`] >>
  simp[ld_write_interval] >> conj_tac
  >- (rpt strip_tac >>
      `~(b+delta <= i /\ i < b+delta+n) /\
       ~(c+delta <= i /\ i < c+delta+n)` by decide_tac >>
      gvs[read_byte_write_memory_with_expansion, ld_write_interval]) >>
  map_every qx_gen_tac [`a`, `u`, `v`, `z`, `j`] >> strip_tac >>
  (Cases_on `a = k`
  >- (gvs[] >> simp[read_byte_write_memory_with_expansion] >>
      (Cases_on `delta <= j /\ j < delta+LENGTH xs`
      >- (`j = delta+(j-delta) /\ j-delta < LENGTH xs` by decide_tac >>
          `j-delta NOTIN M` by metis_tac[] >>
          `?h. j = delta+h /\ h < LENGTH xs` by
            (qexists_tac `j-delta` >> simp[]) >>
          simp[]) >>
      `~(?h. j = delta+h /\ h < LENGTH xs)` by
        (strip_tac >> decide_tac) >> simp[])) >>
  `0 < z /\ 0 < sz` by decide_tac >>
  `((u+z <= b \/ b+sz <= u) /\ (v+z <= c \/ c+sz <= v))` by metis_tac[] >>
  `~(b+delta <= u+j /\ u+j < b+delta+n) /\
   ~(c+delta <= v+j /\ v+j < c+delta+n)` by decide_tac >>
  gvs[read_byte_write_memory_with_expansion, ld_write_interval] >>
  decide_tac)
QED

(* Private target writes have no corresponding source allocation. *)
Theorem ld_memory_write_private:
  ld_memory lo A tn s t /\ lo <= dst /\
  (!k b c n. FLOOKUP A k = SOME (b,c,n) /\ 0 < n ==>
     c+n <= dst \/ dst+LENGTH bytes <= c) ==>
  ld_memory lo A tn s (write_memory_with_expansion dst bytes t)
Proof
  strip_tac >> fs[ld_memory_def] >> conj_tac
  >- (rpt strip_tac >>
      `~(dst <= i /\ i < dst+LENGTH bytes)` by decide_tac >>
      simp[read_byte_write_memory_with_expansion, ld_write_interval]) >>
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  `c+n <= dst \/ dst+LENGTH bytes <= c` by metis_tac[] >>
  `~(dst <= c+j /\ c+j < dst+LENGTH bytes)` by decide_tac >>
  simp[read_byte_write_memory_with_expansion, ld_write_interval] >>
  metis_tac[]
QED

val _ = if null (hyp ld_memory_write_private) then ()
  else raise Fail "private memory theorem has hypotheses";
