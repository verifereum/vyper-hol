(* Boundary between tuple loading and pointer-safe member stores. *)
Theory assignTuplePtrBoundary
Ancestors
  bodyPtrDefs typedCopyLayoutPtr tupleMemoryLayout exprSimProps
  valueTypingMemoryProps robustCopyTransportPtr list finite_map arithmetic

Theorem tuple_loaded_member_ptr_mem_ok:
  !cx ty vs tvs base s G tn i p w b sz.
    LENGTH vs = LENGTH tvs /\ i < LENGTH tvs /\
    evaluate_type (get_tenv cx) ty = SOME (EL i tvs) /\
    val_wf (EL i tvs) (EL i vs) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
         tuple_in_memory vs tvs base m) /\
    eval_operand (Var p) s = SOME w /\
    w2n w = base + SUM (MAP type_memory_size (TAKE i tvs)) /\
    FLOOKUP G p = SOME (b,sz) /\ b <= base /\
    base + SUM (MAP type_memory_size tvs) <= b + sz ==>
    ptr_mem_ok cx ty (EL i vs) (Var p) G tn s
Proof
  rpt strip_tac >>
  drule_all tuple_element_interval >> strip_tac >>
  drule val_store_size_le >> strip_tac >>
  simp[ptr_mem_ok_def] >> rpt strip_tac >>
  irule tuple_in_memory_element >> simp[]
QED

Theorem ptr_mem_ok_exterior_frame:
  !cx ty v op G tn s G' tn' s' writes.
    ptr_mem_ok cx ty v op G tn s /\
    eval_operand op s' = eval_operand op s /\
    (!p. op = Var p ==> FLOOKUP G' p = FLOOKUP G p) /\
    (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==> val_wf tv v) /\
    (!tv w i. evaluate_type (get_tenv cx) ty = SOME tv /\
      eval_operand op s = SOME w /\
      w2n w <= i /\ i < w2n w + val_footprint tv v ==> i NOTIN writes) /\
    (!i. i NOTIN writes ==>
      mem_bytes_at i 1 s'.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. i NOTIN writes ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) ==>
    ptr_mem_ok cx ty v op G' tn' s'
Proof
  rpt gen_tac >> strip_tac >>
  simp[ptr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
  simp[ptr_mem_ok_def] >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >> irule robust_val_in_memory_exterior_frame >> simp[] >>
      qexistsl [`s.vs_memory`, `s'.vs_memory`, `tn.t_mem`, `tn'.t_mem`, `writes`] >> simp[] >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem ptr_val_ok_exterior_frame:
  !cx ty v op G tn s G' tn' s' writes.
    ptr_val_ok cx ty v op G tn s /\
    eval_operand op s' = eval_operand op s /\
    op_taint tn' op = op_taint tn op /\
    op_prov G' op = op_prov G op /\
    (!p. op = Var p ==> FLOOKUP G' p = FLOOKUP G p) /\
    (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==> val_wf tv v) /\
    (!tv w i. evaluate_type (get_tenv cx) ty = SOME tv /\
      eval_operand op s = SOME w /\
      w2n w <= i /\ i < w2n w + val_footprint tv v ==> i NOTIN writes) /\
    (!i. i NOTIN writes ==>
      mem_bytes_at i 1 s'.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. i NOTIN writes ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) ==>
    ptr_val_ok cx ty v op G' tn' s'
Proof
  rpt gen_tac >> strip_tac >>
  fs[ptr_val_ok_def] >> strip_tac >>
  irule ptr_mem_ok_exterior_frame >> conj_tac >- simp[] >>
  qexistsl_tac [`G`, `s`, `tn`, `writes`] >> simp[]
QED
