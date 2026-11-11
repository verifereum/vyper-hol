(* Runtime semantic continuation at the very same copy endpoint. *)
Theory bodyPtrMakeArrayStoreFrame
Ancestors
  exprSimLiteralBuffer bodyPtrMakeArrayCopyStateFrame compileEnv loweringStateRelDefs venomState
  valueEncodingProofs list

Theorem literal_store_local_bytes:
  (!name p n i. local_region ce es.scopes s name p n /\
    p <= i /\ i < p+n ==> ~(b <= i /\ i < b+k)) /\
  (!i. ~(b <= i /\ i < b+k) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) ==>
  !name p n. local_region ce es.scopes s name p n ==>
    mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory
Proof
  rpt strip_tac >> irule LIST_EQ >> simp[EL_mem_bytes_at] >>
  rpt strip_tac >> rename1 `i < n` >>
  `mem_bytes_at (p+i) 1 t.vs_memory = mem_bytes_at (p+i) 1 s.vs_memory` by
    (first_x_assum irule >> metis_tac[arithmeticTheory.LESS_EQ_ADD,
       arithmeticTheory.LT_ADD_LCANCEL]) >>
  pop_assum (mp_tac o AP_TERM ``EL 0 : word8 list -> word8``) >>
  simp[EL_mem_bytes_at]
QED

Theorem literal_store_runtime_frame:
  stmt_state_rel ctx func ce cx es s /\ ~ce.ce_is_ctor /\
  local_ptrs_reserved ce sa /\
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!name p n i. local_region ce es.scopes s name p n /\
    p <= i /\ i < p+n ==> ~(b <= i /\ i < b+k)) /\
  (!i. ~(b <= i /\ i < b+k) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) ==>
  stmt_state_rel ctx func ce cx es t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!name p n. local_region ce es.scopes s name p n ==>
    mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory` by
    (metis_tac[literal_store_local_bytes]) >>
  `stmt_state_rel ctx func ce cx es (t with vs_inst_idx := s.vs_inst_idx)`
    suffices_by simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
  irule literal_state_memory_frame >> simp[] >>
  qexists `s` >> simp[local_ptrs_reserved_def] >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  conj_tac >- (gvs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
  conj_tac >- (gvs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
  qpat_x_assum `(t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>) = s`
    mp_tac >> simp[venom_state_component_equality]
QED
