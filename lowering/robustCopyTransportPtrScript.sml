(* Copied-window witnesses preserve arbitrary robust representations. *)
Theory robustCopyTransportPtr
Ancestors
  representationCleanPtr exprSimMemoryTransport valueEncoding valueEncodingProofs
  valueEncodingProps bodyPtrDefs venomMemProofs list arithmetic

Theorem copied_window_agree_witness:
  !tn tn' mem mem' src dst n m.
    mem_bytes_at dst n mem' = mem_bytes_at src n mem /\
    (!i. i < n ==> (dst+i IN tn' <=> src+i IN tn)) /\
    mem_agree_outside tn' mem' m ==>
    ?mix. mem_agree_outside tn mem mix /\
          mem_bytes_at src n mix = mem_bytes_at dst n m
Proof
  rpt strip_tac >>
  qabbrev_tac `s = (ARB:venom_state) with vs_memory := mem` >>
  qabbrev_tac `mix =
    (write_memory_with_expansion src (mem_bytes_at dst n m) s).vs_memory` >>
  `mem_bytes_at src n mix = mem_bytes_at dst n m` by
    (qspecl_then [`src`, `mem_bytes_at dst n m`, `s`] mp_tac
       write_memory_mem_bytes_at_same >> simp[Abbr `mix`]) >>
  qexists_tac `mix` >> simp[] >>
  simp[mem_agree_outside_def] >> rpt strip_tac >>
  Cases_on `src <= i /\ i < src+n`
  >- (`i-src < n /\ src+(i-src) = i` by decide_tac >>
      `dst+(i-src) NOTIN tn'` by metis_tac[] >>
      `EL (i-src) (mem_bytes_at src n mix) =
       EL (i-src) (mem_bytes_at dst n m)` by simp[] >>
      `EL (i-src) (mem_bytes_at dst n mem') =
       EL (i-src) (mem_bytes_at src n mem)` by simp[] >>
      `mem_bytes_at (dst+(i-src)) 1 mem' =
       mem_bytes_at (dst+(i-src)) 1 m` by
        metis_tac[mem_agree_outside_def] >>
      `EL 0 (mem_bytes_at (dst+(i-src)) 1 mem') =
       EL 0 (mem_bytes_at (dst+(i-src)) 1 m)` by simp[] >>
      `i-src < n` by decide_tac >>
      gvs[EL_mem_bytes_at] >>
      irule LIST_EQ >> simp[EL_mem_bytes_at] >> metis_tac[]) >>
  sym_tac >> simp[Abbr `mix`] >>
  irule EQ_TRANS >> qexists_tac `mem_bytes_at i 1 s.vs_memory` >>
  conj_tac
  >- (irule write_memory_mem_bytes_at_disjoint >> simp[] >> decide_tac) >>
  simp[Abbr `s`]
QED

Theorem robust_val_in_memory_copy_transport:
  !tv v src dst n tn tn' mem mem'.
    val_wf tv v /\ val_footprint tv v <= n /\
    mem_bytes_at dst n mem' = mem_bytes_at src n mem /\
    (!i. i < n ==> (dst+i IN tn' <=> src+i IN tn)) /\
    (!m. mem_agree_outside tn mem m ==> val_in_memory tv v src m) ==>
    !m. mem_agree_outside tn' mem' m ==> val_in_memory tv v dst m
Proof
  rpt strip_tac >> drule_all copied_window_agree_witness >>
  disch_then (qx_choose_then `mix` strip_assume_tac) >>
  `val_in_memory tv v src mix` by metis_tac[] >>
  irule val_in_memory_relocate_footprint >>
  conj_tac >- simp[] >>
  qexistsl_tac [`mix`, `src`] >> simp[] >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `i < val_footprint tv v` >>
  `i < n` by decide_tac >>
  `EL i (mem_bytes_at src n mix) = EL i (mem_bytes_at dst n m)` by simp[] >>
  gvs[EL_mem_bytes_at]
QED

Theorem robust_val_in_memory_exterior_frame:
  !tn tn' mem mem' writes tv v p.
    val_wf tv v /\
    (!i. p <= i /\ i < p + val_footprint tv v ==> i NOTIN writes) /\
    (!i. i NOTIN writes ==> mem_bytes_at i 1 mem' = mem_bytes_at i 1 mem) /\
    (!i. i NOTIN writes ==> (i IN tn' <=> i IN tn)) /\
    (!m. mem_agree_outside tn mem m ==> val_in_memory tv v p m) ==>
    !m. mem_agree_outside tn' mem' m ==> val_in_memory tv v p m
Proof
  rpt gen_tac >> strip_tac >>
  rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
  conj_tac >- simp[] >>
  qexistsl_tac [`mem`, `mem'`, `val_footprint tv v`, `p`, `tn`, `tn'`] >> simp[] >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `j < val_footprint tv v` >>
  `p+j NOTIN writes` by (first_x_assum irule >> decide_tac) >>
  `mem_bytes_at (p+j) 1 mem' = mem_bytes_at (p+j) 1 mem` by metis_tac[] >>
  pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

(* A later child may clean more bytes; robustness needs only monotone taint,
   not equality of the old and new taint on the preserved value window. *)
Theorem calldata_member_robust_window_frame:
  val_wf tv v /\
  mem_bytes_at p (val_footprint tv v) newmem =
    mem_bytes_at p (val_footprint tv v) oldmem /\
  newtaint SUBSET oldtaint /\
  (!mem. mem_agree_outside oldtaint oldmem mem ==> val_in_memory tv v p mem) ==>
  !mem. mem_agree_outside newtaint newmem mem ==> val_in_memory tv v p mem
Proof
  strip_tac >>
  `!mem. mem_agree_outside oldtaint newmem mem ==> val_in_memory tv v p mem` by
    (rpt strip_tac >> irule robust_val_in_memory_copy_transport >> simp[] >>
     qexistsl_tac [`oldmem`, `newmem`, `val_footprint tv v`, `p`, `oldtaint`, `oldtaint`] >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >>
  qpat_x_assum `mem_agree_outside _ _ _` mp_tac >>
  qpat_x_assum `newtaint SUBSET oldtaint` mp_tac >>
  simp[mem_agree_outside_def, pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED
