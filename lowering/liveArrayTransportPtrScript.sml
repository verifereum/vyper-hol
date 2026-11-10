(* Dynamic-array copying transports live elements, not unused capacity. *)
Theory liveArrayTransportPtr
Ancestors robustCopyTransportPtr exprSimMemoryTransport valueEncoding valueEncodingDefs valueEncodingProps
  valueEncodingProofs list arithmetic

Theorem elems_in_memory_relocate_window:
  !vs tv src dst n mem mem'.
    EVERY (\v. val_wf tv v /\ val_footprint tv v <= type_memory_size tv) vs /\
    LENGTH vs * type_memory_size tv <= n /\
    elems_in_memory vs src tv mem /\
    mem_bytes_at dst n mem' = mem_bytes_at src n mem ==>
    elems_in_memory vs dst tv mem'
Proof
  Induct >> simp[val_in_memory_def, arithmeticTheory.MULT_CLAUSES] >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (irule val_in_memory_relocate_footprint >> simp[] >>
      qexistsl_tac [`mem`, `src`] >> simp[] >>
      irule LIST_EQ >> simp[] >> rpt strip_tac >>
      rename1 `i < val_footprint tv h` >>
      `i < n` by decide_tac >>
      `EL i (mem_bytes_at dst n mem') = EL i (mem_bytes_at src n mem)` by simp[] >>
      gvs[EL_mem_bytes_at]) >>
  first_x_assum irule >> conj_tac >- simp[] >>
  qexistsl_tac [`mem`, `n - type_memory_size tv`, `src + type_memory_size tv`] >>
  simp[] >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `i < n - type_memory_size tv` >>
  `type_memory_size tv + i < n` by decide_tac >>
  `EL (type_memory_size tv + i) (mem_bytes_at dst n mem') =
   EL (type_memory_size tv + i) (mem_bytes_at src n mem)` by simp[] >>
  pop_assum mp_tac >>
  qpat_x_assum `mem_bytes_at dst n mem' = _` kall_tac >>
  asm_simp_tac bool_ss [EL_mem_bytes_at] >>
  rewrite_tac[arithmeticTheory.ADD_ASSOC]
QED

Theorem robust_elems_in_memory_copy_transport:
  !vs tv src dst n tn tn' mem mem'.
    EVERY (\v. val_wf tv v /\ val_footprint tv v <= type_memory_size tv) vs /\
    LENGTH vs * type_memory_size tv <= n /\
    mem_bytes_at dst n mem' = mem_bytes_at src n mem /\
    (!i. i < n ==> (dst+i IN tn' <=> src+i IN tn)) /\
    (!m. mem_agree_outside tn mem m ==> elems_in_memory vs src tv m) ==>
    !m. mem_agree_outside tn' mem' m ==> elems_in_memory vs dst tv m
Proof
  rpt strip_tac >> drule_all copied_window_agree_witness >>
  disch_then (qx_choose_then `mix` strip_assume_tac) >>
  irule elems_in_memory_relocate_window >> conj_tac >- simp[] >>
  qexistsl_tac [`mix`, `n`, `src`] >> simp[] >> metis_tac[]
QED

Theorem robust_dynarray_memory_assemble:
  !tn mem dst vs tv cap.
    (!m. mem_agree_outside tn mem m ==>
      mem_word_at dst m = n2w (LENGTH vs)) /\
    (!m. mem_agree_outside tn mem m ==>
      elems_in_memory vs (dst+32) tv m) ==>
    !m. mem_agree_outside tn mem m ==>
      val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) dst m
Proof
  simp[val_in_memory_def]
QED
