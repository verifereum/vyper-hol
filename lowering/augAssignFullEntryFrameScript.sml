(* Pointwise entry-origin frames; no execution endpoint is selected here. *)
Theory augAssignFullEntryFrame
Ancestors
  stmtSimAugAssignPlaceMemory bodySimFull stmtSimDefs bodyMemoryDefs
  bodyPtrDefs loweringPosts freshWrites compileEnv venomState
  finite_map pred_set list arithmetic

(* Shared suffix: the prefix may be a real target or the identity prefix. *)
Theorem augassign_prefix_operator_frame[local]:
  alloca_frame cenv es0 sa0 s0 cenv st u /\
  (!x z. not_fresh_at sa0 x /\ lookup_var x s0 = SOME z ==>
    lookup_var x u = SOME z) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP u.vs_allocas aid = SOME b) /\
  ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 Gu tnu /\
  stmt_state_rel H ctx func cenv cx st u /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\
  sa0.cs_next_var <= sc.cs_next_var /\ sc.cs_next_var <= sd.cs_next_var /\
  sd.cs_next_var <= se.cs_next_var /\
  sa0.cs_next_id <= sc.cs_next_id /\ sc.cs_next_id <= sd.cs_next_id /\
  MAP FDOM ee.scopes = MAP FDOM st.scopes /\
  expr_post H ctx func cenv cx e st sc sd u ee v op q /\
  ghost_kept_at lo cenv st sc Gu tnu u Gq tnq /\
  ghost_kept_at lo cenv ee sd Gq tnq q Gw tnw /\
  (!x z. not_fresh_at sd x /\ lookup_var x q = SOME z ==>
    lookup_var x w = SOME z) /\
  w.vs_memory = q.vs_memory /\ w.vs_allocas = q.vs_allocas /\
  w.vs_alloca_next = q.vs_alloca_next /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  u.vs_alloca_next <= q.vs_alloca_next /\
  return_buf_frame d cenv sd q /\ alloca_history func w /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp w) ==>
  return_buf_frame d cenv se w /\ alloca_history func w /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp w) /\
  s0.vs_alloca_next <= w.vs_alloca_next /\
  (!x z. not_fresh_at sa0 x /\ lookup_var x s0 = SOME z ==>
    lookup_var x w = SOME z) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP w.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa0 x ==> FLOOKUP Gw x = FLOOKUP G0 x /\
    op_taint tnw (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame cenv es0 sa0 s0 cenv ee w /\
  (!aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
    (!n b sz'. local_region cenv es0.scopes s0 n b sz' ==>
      off + sz <= b \/ b + sz' <= off) /\
    off <= i /\ i < off + sz /\ i IN tnw.t_mem ==> i IN tn0.t_mem)
Proof
  strip_tac >>
  qpat_assum `alloca_frame _ _ _ _ _ _ _` (mk_asm "prefix") >>
  drule_all expr_post_alloca_frame >> strip_tac >>
  `alloca_frame cenv es0 sa0 s0 cenv ee q` by
    (irule alloca_frame_trans >>
     goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ u`)) >>
     goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ q`)) >> simp[]) >>
  `(!x z. not_fresh_at sc x /\ lookup_var x u = SOME z ==>
      lookup_var x q = SOME z) /\
   (!aid b. FLOOKUP u.vs_allocas aid = SOME b ==>
      FLOOKUP q.vs_allocas aid = SOME b) /\
   stmt_state_rel H ctx func cenv cx ee q` by fs[expr_post_def] >>
  conj_tac >- (irule return_buf_frame_frame >>
    qexistsl_tac [`cenv`, `q`, `sd`] >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (gvs[] >> decide_tac) >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (fs[ghost_kept_at_def] >>
    metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  conj_tac >- suspend "frame" >>
  suspend "taint"
QED

Resume augassign_prefix_operator_frame[frame]:
  `alloca_frame cenv ee sd q cenv ee w` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx ee q`
       (mp_then Any mp_tac alloca_frame_of_mem_frame) >>
     disch_then irule >> simp[]) >>
  irule alloca_frame_trans >>
  goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ q`)) >>
  goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ w`)) >>
  conj_tac >- decide_tac >> metis_tac[]
QED

Resume augassign_prefix_operator_frame[taint]:
  `!aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
    (!n b sz'. local_region cenv es0.scopes s0 n b sz' ==>
      off + sz <= b \/ b + sz' <= off) /\
    off <= i /\ i < off + sz /\ i IN tnq.t_mem ==> i IN tn0.t_mem` by
    (match_mp_tac (GEN_ALL alloca_taint_kept_trans) >>
     asm "prefix" (irule_at Any) >>
     qexistsl_tac [`tnu`, `sc`] >> fs[ghost_kept_at_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  match_mp_tac (GEN_ALL alloca_taint_kept_trans) >>
  goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ q`)) >>
  qexistsl_tac [`tnq`, `sd`] >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >> fs[ghost_kept_at_def]
QED

Finalise augassign_prefix_operator_frame

Theorem augassign_entry_operator_frame:
  target_post H ctx func cenv cx es0 sa0 sb s0 st pv vt r t /\
  stmt_state_rel H ctx func cenv cx es0 s0 /\
  stmt_state_rel H ctx func cenv cx st u /\
  local_ptrs_reserved cenv sa0 /\ local_ptrs_reserved cenv sb /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\
  sa0.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= sc.cs_next_var /\
  sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= se.cs_next_var /\
  sa0.cs_next_id <= sb.cs_next_id /\ sb.cs_next_id <= sc.cs_next_id /\
  sc.cs_next_id <= sd.cs_next_id /\
  MAP FDOM st.scopes = MAP FDOM es0.scopes /\
  MAP FDOM ee.scopes = MAP FDOM st.scopes /\
  u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas /\
  u.vs_alloca_next = t.vs_alloca_next /\
  (!x z. not_fresh_at sb x /\ lookup_var x t = SOME z ==>
    lookup_var x u = SOME z) /\
  ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 Gu tnu /\
  expr_post H ctx func cenv cx e st sc sd u ee v op q /\
  ghost_kept_at lo cenv st sc Gu tnu u Gq tnq /\
  ghost_kept_at lo cenv ee sd Gq tnq q Gw tnw /\
  (!x z. not_fresh_at sd x /\ lookup_var x q = SOME z ==>
    lookup_var x w = SOME z) /\
  w.vs_memory = q.vs_memory /\ w.vs_allocas = q.vs_allocas /\
  w.vs_alloca_next = q.vs_alloca_next /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  u.vs_alloca_next <= q.vs_alloca_next /\
  return_buf_frame d cenv sd q /\ alloca_history func w /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp w) ==>
  return_buf_frame d cenv se w /\ alloca_history func w /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp w) /\
  s0.vs_alloca_next <= w.vs_alloca_next /\
  (!x z. not_fresh_at sa0 x /\ lookup_var x s0 = SOME z ==>
    lookup_var x w = SOME z) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP w.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa0 x ==> FLOOKUP Gw x = FLOOKUP G0 x /\
    op_taint tnw (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame cenv es0 sa0 s0 cenv ee w /\
  (!aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
    (!n b sz'. local_region cenv es0.scopes s0 n b sz' ==>
      off + sz <= b \/ b + sz' <= off) /\
    off <= i /\ i < off + sz /\ i IN tnw.t_mem ==> i IN tn0.t_mem)
Proof
  strip_tac >>
  drule_all target_post_alloca_frame >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx st t /\
   (!x z. not_fresh_at sa0 x /\ lookup_var x s0 = SOME z ==>
     lookup_var x t = SOME z) /\
   (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
     FLOOKUP t.vs_allocas aid = SOME b)` by fs[target_post_def] >>
  `alloca_frame cenv st sb t cenv st u` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx st t`
       (mp_then Any mp_tac alloca_frame_of_mem_frame) >>
     disch_then irule >> simp[]) >>
  `alloca_frame cenv es0 sa0 s0 cenv st u` by
    (irule alloca_frame_trans >>
     goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ t`)) >>
     goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ u`)) >> simp[]) >>
  `!x z. not_fresh_at sa0 x /\ lookup_var x s0 = SOME z ==>
    lookup_var x u = SOME z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP u.vs_allocas aid = SOME b` by metis_tac[] >>
  `sa0.cs_next_var <= sc.cs_next_var /\ sa0.cs_next_id <= sc.cs_next_id /\
   s0.vs_alloca_next <= u.vs_alloca_next` by (gvs[] >> decide_tac) >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
       mp_tac augassign_prefix_operator_frame) >>
  disch_then match_mp_tac >> simp[] >> FAIL_TAC "remaining suffix inputs"
QED

Theorem augassign_immutable_entry_operator_frame:
  stmt_state_rel H ctx func cenv cx es0 s0 /\
  stmt_state_rel H ctx func cenv cx es0 u /\
  local_ptrs_reserved cenv sa0 /\ local_ptrs_reserved cenv sc /\
  local_ptrs_reserved cenv sd /\
  sa0.cs_next_var <= sc.cs_next_var /\ sc.cs_next_var <= sd.cs_next_var /\
  sd.cs_next_var <= se.cs_next_var /\
  sa0.cs_next_id <= sc.cs_next_id /\ sc.cs_next_id <= sd.cs_next_id /\
  u.vs_memory = s0.vs_memory /\ u.vs_allocas = s0.vs_allocas /\
  u.vs_alloca_next = s0.vs_alloca_next /\
  (!x z. not_fresh_at sa0 x /\ lookup_var x s0 = SOME z ==>
    lookup_var x u = SOME z) /\
  ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 Gu tnu /\
  MAP FDOM ee.scopes = MAP FDOM es0.scopes /\
  expr_post H ctx func cenv cx e es0 sc sd u ee v op q /\
  ghost_kept_at lo cenv es0 sc Gu tnu u Gq tnq /\
  ghost_kept_at lo cenv ee sd Gq tnq q Gw tnw /\
  (!x z. not_fresh_at sd x /\ lookup_var x q = SOME z ==>
    lookup_var x w = SOME z) /\
  w.vs_memory = q.vs_memory /\ w.vs_allocas = q.vs_allocas /\
  w.vs_alloca_next = q.vs_alloca_next /\
  u.vs_alloca_next <= q.vs_alloca_next /\
  return_buf_frame d cenv sd q /\ alloca_history func w /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp w) ==>
  return_buf_frame d cenv se w /\ alloca_history func w /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp w) /\
  s0.vs_alloca_next <= w.vs_alloca_next /\
  (!x z. not_fresh_at sa0 x /\ lookup_var x s0 = SOME z ==>
    lookup_var x w = SOME z) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP w.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa0 x ==> FLOOKUP Gw x = FLOOKUP G0 x /\
    op_taint tnw (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame cenv es0 sa0 s0 cenv ee w /\
  (!aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
    (!n b sz'. local_region cenv es0.scopes s0 n b sz' ==>
      off + sz <= b \/ b + sz' <= off) /\
    off <= i /\ i < off + sz /\ i IN tnw.t_mem ==> i IN tn0.t_mem)
Proof
  strip_tac >>
  `alloca_frame cenv es0 sa0 s0 cenv es0 u` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es0 s0`
       (mp_then Any mp_tac alloca_frame_of_mem_frame) >>
     disch_then irule >> simp[]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP u.vs_allocas aid = SOME b` by metis_tac[] >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by simp[] >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
       mp_tac augassign_prefix_operator_frame) >>
  disch_then match_mp_tac >> simp[] >> FAIL_TAC "remaining suffix inputs"
QED
