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

(* Register-only segments transport the accumulated concrete frame.  This
   deliberately says nothing about the control cursor or the loop counter. *)
Theorem annassign_index_nowrite_frame[local]:
  !sa dst len G0 tn0 s0 G tn s H tm t.
    typed_copy_state_frame sa dst len s0 s /\
    (!i. ~(dst <= i /\ i < dst + len) ==>
      mem_bytes_at i 1 s.vs_memory = mem_bytes_at i 1 s0.vs_memory /\
      (i IN tn.t_mem <=> i IN tn0.t_mem)) /\
    tn.t_stor = tn0.t_stor /\ tn.t_trans = tn0.t_trans /\
    tn.t_imm = tn0.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x s = lookup_var x s0 /\ FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    typed_copy_state_frame sa dst len s t /\
    t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\
    tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) ==>
    typed_copy_state_frame sa dst len s0 t /\
    (!i. ~(dst <= i /\ i < dst + len) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s0.vs_memory /\
      (i IN tm.t_mem <=> i IN tn0.t_mem)) /\
    tm.t_stor = tn0.t_stor /\ tm.t_trans = tn0.t_trans /\
    tm.t_imm = tn0.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s0 /\ FLOOKUP H x = FLOOKUP G0 x /\
      op_taint tm (Var x) = op_taint tn0 (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >- metis_tac[typed_copy_state_frame_trans] >>
  simp[] >> metis_tac[]
QED

(* Predicate names below are only abbreviations, fixed by explicit equations.
   In particular the segment contracts preserve concrete resources, not Inv. *)
Theorem annassign_index_counted_traversal:
  !D ctx fn PG sa f stv dtv src dst N sr dr ctr sp dp
    cb ci ab ai eb ei rb ri xb xi G0 tn0 s0 Frame Rep Roots NW Inv.
    Frame = (\G tn s.
      typed_copy_state_frame sa dst (N * type_memory_size dtv) s0 s /\
      (!i. ~(dst <= i /\ i < dst + N * type_memory_size dtv) ==>
        mem_bytes_at i 1 s.vs_memory = mem_bytes_at i 1 s0.vs_memory /\
        (i IN tn.t_mem <=> i IN tn0.t_mem)) /\
      tn.t_stor = tn0.t_stor /\ tn.t_trans = tn0.t_trans /\
      tn.t_imm = tn0.t_imm /\
      (!x. not_fresh_at sa x ==>
        lookup_var x s = lookup_var x s0 /\ FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x))) /\
    Rep = (\k tn s.
      (!i. i < N ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory stv (f i) (src + i * type_memory_size stv) m) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        typed_copy_index_prefix f dtv dst N k m)) /\
    Roots = (\G tn s.
      lookup_var sr s = SOME (n2w src) /\
      lookup_var dr s = SOME (n2w dst) /\
      ptr_covers G tn sr s (N * type_memory_size stv) /\
      ptr_covers G tn dr s (N * type_memory_size dtv)) /\
    NW = (\G tn s H tm t.
      typed_copy_state_frame sa dst (N * type_memory_size dtv) s t /\
      t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\
      tm.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x \/ x = sr \/ x = dr ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tm (Var x) = op_taint tn (Var x))) /\
    Inv = (\k G tn s. k <= N /\ s.vs_current_bb = cb /\
      s.vs_inst_idx = ci /\ ~s.vs_halted /\
      lookup_var ctr s = SOME (n2w k) /\ op_taint tn (Var ctr) = {} /\
      Roots G tn s /\ Rep k tn s /\ Frame G tn s) /\
    (!i. i < N ==> val_wf stv (f i) /\ val_wf dtv (f i)) /\
    (src + N * type_memory_size stv <= dst \/
     dst + N * type_memory_size dtv <= src) /\
    (* True/false condition test. *)
    (!k G tn s. k <= N /\ s.vs_current_bb = cb /\ s.vs_inst_idx = ci /\
      ~s.vs_halted /\ lookup_var ctr s = SOME (n2w k) /\
      op_taint tn (Var ctr) = {} ==>
      ?H tm t. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
        t.vs_current_bb = (if k < N then ab else xb) /\
        t.vs_inst_idx = (if k < N then ai else xi) /\ ~t.vs_halted /\
        lookup_var ctr t = SOME (n2w k) /\ op_taint tm (Var ctr) = {} /\
        NW G tn s H tm t) /\
    (* Address segment, including the two child operand resources. *)
    (!k G tn s. k < N /\ s.vs_current_bb = ab /\ s.vs_inst_idx = ai /\
      ~s.vs_halted /\ lookup_var ctr s = SOME (n2w k) /\
      op_taint tn (Var ctr) = {} /\ Roots G tn s ==>
      ?H tm t. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
        t.vs_current_bb = eb /\ t.vs_inst_idx = ei /\ ~t.vs_halted /\
        lookup_var ctr t = SOME (n2w k) /\ op_taint tm (Var ctr) = {} /\
        lookup_var sp t = SOME (n2w (src + k * type_memory_size stv)) /\
        lookup_var dp t = SOME (n2w (dst + k * type_memory_size dtv)) /\
        ptr_covers H tm sp t (type_memory_size stv) /\
        ptr_covers H tm dp t (type_memory_size dtv) /\ NW G tn s H tm t) /\
    (* Recursive child.  Control flow may change, including prev_bb. *)
    (!k G tn s. k < N /\ s.vs_current_bb = eb /\ s.vs_inst_idx = ei /\
      ~s.vs_halted /\
      lookup_var sp s = SOME (n2w (src + k * type_memory_size stv)) /\
      lookup_var dp s = SOME (n2w (dst + k * type_memory_size dtv)) /\
      ptr_covers G tn sp s (type_memory_size stv) /\
      ptr_covers G tn dp s (type_memory_size dtv) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory stv (f k) (src + k * type_memory_size stv) m) ==>
      ?H tm t. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
        t.vs_current_bb = rb /\ t.vs_inst_idx = ri /\ ~t.vs_halted /\
        typed_copy_state_frame sa (dst + k * type_memory_size dtv)
          (type_memory_size dtv) s t /\
        (!i. ~(dst + k * type_memory_size dtv <= i /\
               i < dst + k * type_memory_size dtv + type_memory_size dtv) ==>
          mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
          (i IN tm.t_mem <=> i IN tn.t_mem)) /\
        tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
        (!x. not_fresh_at sa x \/ x = sr \/ x = dr \/ x = ctr ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
          op_taint tm (Var x) = op_taint tn (Var x)) /\
        (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
          val_in_memory dtv (f k) (dst + k * type_memory_size dtv) m)) /\
    (* Increment and backedge, starting at the child's actual exit. *)
    (!k G tn s. k < N /\ s.vs_current_bb = rb /\ s.vs_inst_idx = ri /\
      ~s.vs_halted /\ lookup_var ctr s = SOME (n2w k) /\
      op_taint tn (Var ctr) = {} ==>
      ?H tm t. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
        t.vs_current_bb = cb /\ t.vs_inst_idx = ci /\ ~t.vs_halted /\
        lookup_var ctr t = SOME (n2w (SUC k)) /\
        op_taint tm (Var ctr) = {} /\ NW G tn s H tm t) ==>
    !k G tn s. k <= N /\ Inv k G tn s ==>
      ?H tm t. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
        t.vs_current_bb = xb /\ t.vs_inst_idx = xi /\ ~t.vs_halted /\
        Roots H tm t /\ Rep N tm t /\ Frame H tm t
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!G tn s H tm t. NW G tn s H tm t ==>
    (Frame G tn s ==> Frame H tm t) /\
    (Roots G tn s ==> Roots H tm t) /\
    (!k. Rep k tn s ==> Rep k tm t)` by
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (disch_tac >> pure_asm_rewrite_tac [] >> BETA_TAC >>
         irule annassign_index_nowrite_frame >>
         qexistsl_tac [`G`, `s`, `tn`] >>
         qpat_x_assum `NW _ _ _ _ _ _` mp_tac >>
         qpat_x_assum `Frame _ _ _` mp_tac >>
         pure_asm_rewrite_tac [] >> BETA_TAC >>
         POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     conj_tac
     >- (qpat_x_assum `NW _ _ _ _ _ _` mp_tac >>
         pure_asm_rewrite_tac [ptr_covers_def] >> BETA_TAC >>
         POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     qpat_x_assum `NW _ _ _ _ _ _` mp_tac >> simp[]) >>
  ho_match_mp_tac annassign_counted_iteration >>
  conj_tac
  >- suspend "successor" >>
  suspend "exit"
QED

Resume annassign_index_counted_traversal[successor]:
  map_every qx_gen_tac [`k`, `G`, `tn`, `s`] >> strip_tac >>
  qpat_x_assum `Inv k G tn s` mp_tac >>
  qpat_assum `Inv = _` (fn th => rewrite_tac[th]) >> BETA_TAC >> strip_tac >>
  qpat_assum `!k G tn s. _ /\ s.vs_current_bb = cb /\ _ ==> _`
    (qspecl_then [`k`, `G`, `tn`, `s`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `G1` (qx_choose_then `tn1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `Frame G1 tn1 s1 /\ Roots G1 tn1 s1 /\ Rep k tn1 s1` by
    (qpat_x_assum `!G tn s H tm t. NW _ _ _ _ _ _ ==> _` drule >>
     disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> simp[]) >>
  qpat_assum `!k G tn s. _ /\ s.vs_current_bb = ab /\ _ ==> _`
    (qspecl_then [`k`, `G1`, `tn1`, `s1`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `G2` (qx_choose_then `tn2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  `Frame G2 tn2 s2 /\ Roots G2 tn2 s2 /\ Rep k tn2 s2` by
    (qpat_x_assum `!G tn s H tm t. NW _ _ _ _ _ _ ==> _` drule >>
     disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> simp[]) >>
  qpat_assum `!k G tn s. _ /\ s.vs_current_bb = eb /\ _ ==> _`
    (qspecl_then [`k`, `G2`, `tn2`, `s2`] mp_tac) >>
  (impl_tac >-
    (simp[] >> qpat_x_assum `Rep k tn2 s2` mp_tac >>
     qpat_assum `Rep = _` (fn th => rewrite_tac[th]) >> simp[])) >>
  disch_then (qx_choose_then `G3` (qx_choose_then `tn3`
    (qx_choose_then `s3` strip_assume_tac))) >>
  suspend "child_frame"

QED

Resume annassign_index_counted_traversal[exit]:
  map_every qx_gen_tac [`G`, `tn`, `s`] >> disch_tac >>
  qpat_x_assum `Inv N G tn s` mp_tac >>
  qpat_assum `Inv = _` (fn th => rewrite_tac[th]) >> BETA_TAC >> strip_tac >>
  qpat_assum `!k G tn s. _ /\ s.vs_current_bb = cb /\ _ ==> _`
    (qspecl_then [`N`, `G`, `tn`, `s`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `H` (qx_choose_then `tm`
    (qx_choose_then `t` strip_assume_tac))) >>
  qpat_x_assum `!G tn s H tm t. NW _ _ _ _ _ _ ==> _` drule >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `Frame _ _ _ ==> _` drule >> disch_then assume_tac >>
  qpat_x_assum `Roots _ _ _ ==> _` drule >> disch_then assume_tac >>
  qpat_x_assum `!k. Rep _ _ _ ==> _` drule >> disch_then assume_tac >>
  qexistsl_tac [`H`, `tm`, `t`] >> simp[]
QED

Resume annassign_index_counted_traversal[child_frame]:
  `Rep (SUC k) tn3 s3 /\ Frame G3 tn3 s3` by
    (qpat_assum `Rep = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `Frame = _` (fn th => rewrite_tac[th]) >> BETA_TAC >>
     rewrite_tac[CONJ_ASSOC] >>
     irule (REWRITE_RULE [CONJ_ASSOC] annassign_robust_index_child_update) >>
     simp[] >> qexistsl_tac [`G2`, `s2`, `tn2`] >>
     qpat_x_assum `Frame G2 tn2 s2` mp_tac >>
     qpat_x_assum `Rep k tn2 s2` mp_tac >>
     pure_asm_rewrite_tac [] >> BETA_TAC >>
     rpt strip_tac >> simp[] >> metis_tac[]) >>
  suspend "backedge"
QED

Resume annassign_index_counted_traversal[backedge]:
  qpat_assum `!x. not_fresh_at sa x \/ x = sr \/ x = dr \/ x = ctr ==> _`
    (qspec_then `sr` (mp_tac o SRULE [])) >> strip_tac >>
  qpat_assum `!x. not_fresh_at sa x \/ x = sr \/ x = dr \/ x = ctr ==> _`
    (qspec_then `dr` (mp_tac o SRULE [])) >> strip_tac >>
  qpat_assum `!x. not_fresh_at sa x \/ x = sr \/ x = dr \/ x = ctr ==> _`
    (qspec_then `ctr` (mp_tac o SRULE [])) >> strip_tac >>
  `Roots G3 tn3 s3` by
    (qpat_x_assum `Roots G2 tn2 s2` mp_tac >>
     qpat_assum `Roots = _` (fn th => rewrite_tac[th]) >> BETA_TAC >>
     map_every (fn q => qpat_x_assum q kall_tac)
       [`Frame = _`, `Rep = _`, `Roots = _`, `NW = _`, `Inv = _`] >>
     simp[ptr_covers_def] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  qpat_assum `!k G tn s. _ /\ s.vs_current_bb = rb /\ _ ==> _`
    (qspecl_then [`k`, `G3`, `tn3`, `s3`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `G4` (qx_choose_then `tn4`
    (qx_choose_then `s4` strip_assume_tac))) >>
  `Frame G4 tn4 s4 /\ Roots G4 tn4 s4 /\ Rep (SUC k) tn4 s4` by
    (qpat_x_assum `!G tn s H tm t. NW _ _ _ _ _ _ ==> _` drule >>
     disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> simp[]) >>
  qexistsl_tac [`G4`, `tn4`, `s4`] >> conj_tac
  >- metis_tac[gas_path_ptr_then, ADD_CLAUSES] >>
  qpat_assum `Inv = _` (fn th => rewrite_tac[th]) >> BETA_TAC >> simp[]
QED

Finalise annassign_index_counted_traversal
