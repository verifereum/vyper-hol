(* Robust array invariants for the counted typed-copy loop. *)
Theory annAssignTypedCopyArrayTraversalPtr
Ancestors
  typedCopyRobustTransportPtr typedMemoryCopy fragGasPathPtr
  bodyPtrDefs valueEncodingDefs valueEncoding arithmetic

Theorem annassign_robust_index_prefix_step:
  !f tv dst N k tn tn' mem mem'.
    k < N /\ (!i. i < N ==> val_wf tv (f i)) /\
    (!m. mem_agree_outside tn mem m ==>
      typed_copy_index_prefix f tv dst N k m) /\
    (!i. ~(dst + k * type_memory_size tv <= i /\
           i < dst + k * type_memory_size tv + type_memory_size tv) ==>
      mem_bytes_at i 1 mem' = mem_bytes_at i 1 mem /\
      (i IN tn' <=> i IN tn)) /\
    (!m. mem_agree_outside tn' mem' m ==>
      val_in_memory tv (f k) (dst + k * type_memory_size tv) m) ==>
    !m. mem_agree_outside tn' mem' m ==>
      typed_copy_index_prefix f tv dst N (SUC k) m
Proof
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  irule typed_copy_index_prefix_step >> simp[] >>
  simp[typed_copy_index_prefix_def] >> rpt strip_tac >>
  irule robust_representation_exterior_frame >>
  conj_tac >- (first_x_assum irule >> decide_tac) >>
  qexistsl_tac [`dst + k * type_memory_size tv`, `mem`, `mem'`,
    `type_memory_size tv`, `tn`, `tn'`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!m. _ ==> typed_copy_index_prefix _ _ _ _ _ _` drule >>
      simp[typed_copy_index_prefix_def]) >>
  disj1_tac >> drule typed_copy_array_subinterval >>
  disch_then (qspecl_then [`dst`, `type_memory_size tv`] mp_tac) >> simp[]
QED

Theorem annassign_robust_index_source_frame:
  !f stv dtv src dst N k tn tn' mem mem'.
    k < N /\ (!i. i < N ==> val_wf stv (f i)) /\
    (src + N * type_memory_size stv <= dst \/
     dst + N * type_memory_size dtv <= src) /\
    (!i. i < N ==> !m. mem_agree_outside tn mem m ==>
      val_in_memory stv (f i) (src + i * type_memory_size stv) m) /\
    (!i. ~(dst + k * type_memory_size dtv <= i /\
           i < dst + k * type_memory_size dtv + type_memory_size dtv) ==>
      mem_bytes_at i 1 mem' = mem_bytes_at i 1 mem /\
      (i IN tn' <=> i IN tn)) ==>
    !i. i < N ==> !m. mem_agree_outside tn' mem' m ==>
      val_in_memory stv (f i) (src + i * type_memory_size stv) m
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  rpt gen_tac >> disch_tac >> gen_tac >> disch_tac >>
  irule robust_representation_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`dst + k * type_memory_size dtv`, `mem`, `mem'`,
    `type_memory_size dtv`, `tn`, `tn'`] >> simp[] >>
  `src <= src + i * type_memory_size stv /\
   src + i * type_memory_size stv + type_memory_size stv <=
     src + N * type_memory_size stv` by
    metis_tac[typed_copy_array_subinterval] >>
  `dst <= dst + k * type_memory_size dtv /\
   dst + k * type_memory_size dtv + type_memory_size dtv <=
     dst + N * type_memory_size dtv` by
    metis_tac[typed_copy_array_subinterval] >>
  decide_tac
QED

(* Logical iteration only: concrete segment preservation is proved separately. *)
Theorem annassign_counted_iteration[local]:
  !D ctx fn PG N Inv Q.
    (!k G tn s. k < N /\ Inv k G tn s ==>
      ?G' tn' s'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK s') /\
        Inv (SUC k) G' tn' s') /\
    (!G tn s. Inv N G tn s ==>
      ?G' tn' s'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK s') /\
        Q G' tn' s') ==>
    !k G tn s. k <= N /\ Inv k G tn s ==>
      ?G' tn' s'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK s') /\
        Q G' tn' s'
Proof
  rpt gen_tac >> strip_tac >>
  `!r k G tn s. N-k = r /\ k <= N /\ Inv k G tn s ==>
    ?G' tn' s'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK s') /\
      Q G' tn' s'` suffices_by metis_tac[] >>
  Induct >> rpt gen_tac >> strip_tac
  >- (`k = N` by decide_tac >> gvs[] >> metis_tac[]) >>
  rename1 `N - k = SUC r` >>
  `k < N /\ N - SUC k = r /\ SUC k <= N` by decide_tac >>
  qpat_x_assum `!k G tn s. k < N /\ _ ==> _` drule >>
  disch_then drule >> strip_tac >>
  first_x_assum drule >> disch_then drule >> disch_then drule >>
  strip_tac >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

(* The child update preserves the concrete semantic and memory-frame portion
   of the loop invariant.  Control/register transitions are independent. *)
Theorem annassign_robust_index_child_update:
  !sa f stv dtv src dst N k G0 tn0 s0 G tn s H tm t.
    k < N /\
    (!i. i < N ==> val_wf stv (f i) /\ val_wf dtv (f i)) /\
    (src + N * type_memory_size stv <= dst \/
     dst + N * type_memory_size dtv <= src) /\
    (!i. i < N ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv (f i) (src + i * type_memory_size stv) m) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      typed_copy_index_prefix f dtv dst N k m) /\
    typed_copy_state_frame sa dst (N * type_memory_size dtv) s0 s /\
    (!i. ~(dst <= i /\ i < dst + N * type_memory_size dtv) ==>
      mem_bytes_at i 1 s.vs_memory = mem_bytes_at i 1 s0.vs_memory /\
      (i IN tn.t_mem <=> i IN tn0.t_mem)) /\
    tn.t_stor = tn0.t_stor /\ tn.t_trans = tn0.t_trans /\
    tn.t_imm = tn0.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x s = lookup_var x s0 /\ FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    typed_copy_state_frame sa (dst + k * type_memory_size dtv)
      (type_memory_size dtv) s t /\
    (!i. ~(dst + k * type_memory_size dtv <= i /\
           i < dst + k * type_memory_size dtv + type_memory_size dtv) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      val_in_memory dtv (f k) (dst + k * type_memory_size dtv) m) ==>
    (!i. i < N ==> !m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      val_in_memory stv (f i) (src + i * type_memory_size stv) m) /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      typed_copy_index_prefix f dtv dst N (SUC k) m) /\
    typed_copy_state_frame sa dst (N * type_memory_size dtv) s0 t /\
    (!i. ~(dst <= i /\ i < dst + N * type_memory_size dtv) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s0.vs_memory /\
      (i IN tm.t_mem <=> i IN tn0.t_mem)) /\
    tm.t_stor = tn0.t_stor /\ tm.t_trans = tn0.t_trans /\
    tm.t_imm = tn0.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s0 /\ FLOOKUP H x = FLOOKUP G0 x /\
      op_taint tm (Var x) = op_taint tn0 (Var x))
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  conj_tac
  >- (rpt strip_tac >> irule annassign_robust_index_source_frame >>
      qexistsl_tac [`N`, `dst`, `dtv`, `k`] >>
      qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tm.t_mem`] >>
      simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule annassign_robust_index_prefix_step >>
      conj_tac >- simp[] >> conj_tac >- simp[] >>
      qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tm.t_mem`] >>
      simp[]) >>
  `dst <= dst + k * type_memory_size dtv /\
   dst + k * type_memory_size dtv + type_memory_size dtv <=
     dst + N * type_memory_size dtv` by
    metis_tac[typed_copy_array_subinterval] >>
  conj_tac
  >- (irule typed_copy_state_frame_trans >> qexists_tac `s` >> simp[] >>
      irule typed_copy_state_frame_subinterval >>
      qexistsl_tac [`dst + k * type_memory_size dtv`, `type_memory_size dtv`] >>
      simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `~(dst + k * type_memory_size dtv <= i /\
         i < dst + k * type_memory_size dtv + type_memory_size dtv)` by
        decide_tac >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED
