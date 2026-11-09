(* Unread robust members survive a bounded write into a tuple container.
   Unlike whole-tuple preservation this allows repeated local destinations. *)
Theory assignTuplePtrUnread
Ancestors
  assignTuplePtrBoundary tupleMemoryFrame compileEnv arithmetic
  bodyPtrDefs venomExecSemantics ptrDiscipline list venomState

Theorem tuple_unread_point_outside_write_ptr:
  b <= addr /\ addr + elem <= a /\ a <= i /\ i < b + sz /\
  written <= elem /\ written <= dsz /\
  (dst <= addr \/ regions_disjoint b sz dst dsz) ==>
  ~(dst <= i /\ i < dst + written)
Proof
  simp[regions_disjoint_def] >> rpt strip_tac >> decide_tac
QED

Theorem tuple_container_unread_point_ptr:
  alloca_inv s /\ local_ptrs_rel func cenv scopes s /\
  ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
   (?name. local_region cenv scopes s name b sz)) /\
  local_region cenv scopes s dest dst dsz /\
  b <= addr /\ addr + elem <= a /\ a <= i /\ i < b + sz /\
  written <= elem /\ written <= dsz ==>
  ~(dst <= i /\ i < dst + written)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all tuple_container_write_position >> strip_tac >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem tuple_unread_value_frame_ptr:
  ptr_val_ok cx ty v op G tn s /\
  eval_operand op t = eval_operand op s /\
  op_taint tn' op = op_taint tn op /\ op_prov G' op = op_prov G op /\
  (!p. op = Var p ==> FLOOKUP G' p = FLOOKUP G p) /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==> val_wf tv v) /\
  b <= addr /\ written <= elem /\ written <= dsz /\
  (dst <= addr \/ regions_disjoint b sz dst dsz) /\
  (~is_word_type ty ==>
    !tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
      eval_operand op s = SOME w ==>
      addr + elem <= w2n w /\ w2n w + val_footprint tv v <= b + sz) /\
  (!i. ~(dst <= i /\ i < dst + written) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tn'.t_mem <=> i IN tn.t_mem)) ==>
  ptr_val_ok cx ty v op G' tn' t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `is_word_type ty`
  >- gvs[ptr_val_ok_def] >>
  irule ptr_val_ok_exterior_frame >> simp[] >>
  qexistsl_tac [`G`, `s`, `tn`, `{i | dst <= i /\ i < dst + written}`] >>
  simp[] >> rpt strip_tac >>
  gvs[regions_disjoint_def] >>
  first_x_assum (qspecl_then [`tv`, `w`] mp_tac) >> simp[] >> decide_tac
QED

Theorem tuple_unread_operands_frame_ptr:
  EVERY (\op. ?p. op = Var p /\ not_fresh_at sa p) ops /\
  (!p. not_fresh_at sa p ==>
    lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
    op_taint tn' (Var p) = op_taint tn (Var p)) /\
  (!i. i < LENGTH ops ==>
    ptr_val_ok cx (EL i tys) (EL i vs) (EL i ops) G tn s /\
    (!tv. evaluate_type (get_tenv cx) (EL i tys) = SOME tv ==>
      val_wf tv (EL i vs)) /\
    (~is_word_type (EL i tys) ==>
      !tv w. evaluate_type (get_tenv cx) (EL i tys) = SOME tv /\
        eval_operand (EL i ops) s = SOME w ==>
        addr + elem <= w2n w /\
        w2n w + val_footprint tv (EL i vs) <= b + sz)) /\
  b <= addr /\ written <= elem /\ written <= dsz /\
  (dst <= addr \/ regions_disjoint b sz dst dsz) /\
  (!i. ~(dst <= i /\ i < dst + written) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tn'.t_mem <=> i IN tn.t_mem)) ==>
  !i. i < LENGTH ops ==>
    ptr_val_ok cx (EL i tys) (EL i vs) (EL i ops) G' tn' t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt strip_tac >>
  `?p. EL i ops = Var p /\ not_fresh_at sa p` by
    (fs[EVERY_EL] >> metis_tac[]) >>
  qpat_x_assum `!i. i < LENGTH ops ==> _` (qspec_then `i` mp_tac) >>
  simp[] >> strip_tac >>
  `lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
   op_taint tn' (Var p) = op_taint tn (Var p)` by metis_tac[] >>
  `eval_operand (Var p) t = eval_operand (Var p) s /\
   op_prov G' (Var p) = op_prov G (Var p)` by
    simp[eval_operand_def, op_prov_def] >>
  `!q. Var p = Var q ==> FLOOKUP G' q = FLOOKUP G q` by simp[] >>
  drule_all tuple_unread_value_frame_ptr >> simp[]
QED
