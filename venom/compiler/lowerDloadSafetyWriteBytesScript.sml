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

(* A same-address write above lo and above every selected allocation
   leaves the projection alone: it lands in the dynamic region. *)
Theorem ld_memory_write_high:
  ld_memory lo A tn s t /\ lo <= off /\
  LENGTH xs = len /\ LENGTH ys = len /\
  (!a u v z. FLOOKUP A a = SOME (u,v,z) ==> u+z <= off /\ v+z <= off) /\
  tn'.t_mem = (tn.t_mem DIFF {off+j | j < len}) UNION
                         {off+j | j < len /\ j IN M} ==>
  ld_memory lo A tn'
    (write_memory_with_expansion off xs s)
    (write_memory_with_expansion off ys t)
Proof
  strip_tac >> irule ld_memory_transport >>
  qexistsl_tac [`{off+j | j < len}`, `s`, `t`, `tn`] >>
  simp[ld_write_interval] >> conj_tac
  >- (rpt strip_tac >> `~(off <= i)` by decide_tac >>
      gvs[read_byte_write_memory_with_expansion, ld_write_interval]) >>
  rpt strip_tac >>
  `b+n <= off /\ c+n <= off` by metis_tac[] >>
  `~(off <= b+j) /\ ~(off <= c+j)` by decide_tac >>
  gvs[read_byte_write_memory_with_expansion, ld_write_interval]
QED

(* The dynamic region stays in agreement after an empty write, a write of
   the same unmasked bytes at the same address, or writes below the floor
   on both sides. *)
Theorem ld_dyn_agree_write:
  ld_dyn_agree fl tn.t_mem s.vs_memory t.vs_memory /\
  LENGTH xs = len /\ LENGTH ys = len /\
  tm' = (tn.t_mem DIFF {ro+j | j < len}) UNION {ro+j | j < len /\ j IN M} /\
  (len = 0 \/
   (ro = rt /\ !j. j < len /\ j NOTIN M ==> EL j xs = EL j ys) \/
   (ro + len <= fl /\ rt + len <= fl)) ==>
  ld_dyn_agree fl tm' (write_memory_with_expansion ro xs s).vs_memory
    (write_memory_with_expansion rt ys t).vs_memory
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `ld_dyn_agree _ _ _ _` mp_tac >>
  rewrite_tac[ptrDisciplineTheory.ld_dyn_agree_def] >> strip_tac >>
  qx_gen_tac `i` >> strip_tac >>
  `(i IN {ro + j | j < len} <=> ro <= i /\ i < ro + len) /\
   (i IN {ro + j | j < len /\ j IN M} <=>
      ro <= i /\ i < ro + len /\ i - ro IN M)` by simp[ld_write_interval] >>
  `(~(ro <= i /\ i < ro + len) ==> i NOTIN tn.t_mem) /\
   (ro <= i /\ i < ro + len ==> i - ro NOTIN M)` by
    (qpat_x_assum `i NOTIN tm'` mp_tac >>
     qpat_x_assum `tm' = _` (fn th => rewrite_tac[th, IN_UNION, IN_DIFF]) >>
     rpt (qpat_x_assum `_ <=> _` (fn th => rewrite_tac[th])) >>
     metis_tac[]) >>
  rewrite_tac[read_byte_write_memory_with_expansion] >>
  qpat_assum `LENGTH xs = len` (fn th => rewrite_tac[th]) >>
  qpat_assum `LENGTH ys = len` (fn th => rewrite_tac[th]) >>
  `(ro = rt /\ ro <= i /\ i < ro + len /\
    !j. j < len /\ j NOTIN M ==> EL j xs = EL j ys) \/
   (~(ro <= i /\ i < ro + len) /\ ~(rt <= i /\ i < rt + len))` by
    (qpat_x_assum `len = 0 \/ _` strip_assume_tac
     >- (disj2_tac >> decide_tac)
     >- (Cases_on `ro <= i /\ i < ro + len`
         >- (disj1_tac >> fs[]) >>
         disj2_tac >> fs[]) >>
     disj2_tac >> decide_tac) >>
  pop_assum strip_assume_tac
  >- (qpat_x_assum `ro = rt` SUBST_ALL_TAC >>
      `i - rt < len` by decide_tac >>
      `i - rt NOTIN M` by metis_tac[] >>
      `EL (i - rt) xs = EL (i - rt) ys` by metis_tac[] >>
      asm_rewrite_tac[]) >>
  qpat_assum `~(ro <= i /\ _)` (fn th => rewrite_tac[th]) >>
  qpat_assum `~(rt <= i /\ _)` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `!i. _` irule >> simp[] >> metis_tac[]
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
