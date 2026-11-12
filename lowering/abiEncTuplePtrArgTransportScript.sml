(* ABI captures retain robustness of their represented footprint, not
   cleanliness of padding.  Reuse the general pointer footprint boundary. *)
Theory abiEncTuplePtrArgTransport
Ancestors
  abiEncodeArgsSim logValueFramePtr wordArgsPtr ghostObservationPtr
  bodyPtrDefs exprSimHypsDefs exprSimProps loweringPosts
  valueEncodingProofs valueEncodingProps ptrDiscipline finite_map words arithmetic

Theorem abi_args_operand_footprint_taint_kept:
  expr_val_at ce cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w /\
  ghost_kept ce es st G tn s H tm /\ sb.cs_next_id <= st.cs_next_id /\
  w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tm.t_mem ==>
  i IN tn.t_mem
Proof
  strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_val_at_def]) >>
  disch_then (qspec_then `tv` mp_tac) >> simp[] >> strip_tac >>
  gvs[ghost_kept_def]
  >- (qpat_x_assum `!aid off sz i. FLOOKUP _ _ = _ /\ _ ==> _` irule >>
      simp[] >> qexistsl [`aid`, `b`, `sz`] >> simp[] >>
      metis_tac[])
  >- (qpat_x_assum `!n b sz i. _` irule >>
      simp[] >> qexistsl [`b`, `n`, `sz`] >> simp[] >> decide_tac) >>
  decide_tac
QED

Theorem abi_args_operand_footprint_kept:
  expr_sim_inv ce cx env es /\
  stmt_state_rel ctx func ce cx es s /\
  stmt_state_rel ctx func ce cx es' t /\ es'.scopes = es.scopes /\
  local_ptrs_reserved ce st /\ wb_frame ce es es' st s t /\
  sb.cs_next_id <= st.cs_next_id /\
  expr_val_at ce cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w ==>
  mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac
  >- (`mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (gvs[wb_frame_def] >> first_x_assum irule >>
         conj_tac >- (rpt strip_tac >> metis_tac[]) >>
         qexists `aid` >> simp[]) >>
      drule mem_bytes_at_agree_window >> simp[])
  >- (irule abi_args_local_window_kept >> metis_tac[]) >>
  simp[valueEncodingDefsTheory.mem_bytes_at_def]
QED

Theorem abi_args_uncaptured_operand_ptr_transport:
  ptr_val_ok cx ty v op G tn s /\ expr_val_rel cx ty v op s /\
  expr_val_at ce cx ty sa sb es v op s /\
  expr_sim_inv ce cx env es /\
  stmt_state_rel ctx func ce cx es s /\
  stmt_state_rel ctx func ce cx es' t /\ es'.scopes = es.scopes /\
  local_ptrs_reserved ce st /\ wb_frame ce es es' st s t /\
  ghost_kept ce es st G tn s H tm /\ sb.cs_next_id <= st.cs_next_id /\
  (!x. op = Var x ==> not_fresh_at st x) /\ (!l. op <> Label l) ==>
  ptr_val_ok cx ty v op H tm t
Proof
  strip_tac >> irule ptr_val_ok_footprint_frame >>
  qexistsl [`G`, `s`, `tn`] >> simp[] >>
  conj_tac >- (rpt strip_tac >> gvs[ghost_kept_def]) >>
  conj_tac
  >- (`?w0. eval_operand op s = SOME w0` by gvs[expr_val_rel_def] >>
      drule_all abi_args_operand_kept >> simp[]) >>
  reverse conj_tac >- (drule_all ghost_kept_operand >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  conj_tac >- (gvs[expr_val_at_def] >> metis_tac[]) >>
  conj_tac >- (irule abi_args_operand_footprint_kept >> metis_tac[]) >>
  rpt strip_tac >> drule_all abi_args_operand_footprint_taint_kept >> simp[]
QED

Theorem abi_args_captured_operand_ptr_transport:
  ptr_val_ok cx ty v op G tn s /\ expr_val_rel cx ty v op s /\
  wb_frame ce es es' st s t /\ ghost_kept ce es st G tn s H tm /\
  (!x. op = Var x ==> not_fresh_at st x) /\ (!l. op <> Label l) /\
  (!tv w. ~is_word_type ty /\
     evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand op s = SOME w ==>
     val_wf tv v /\
     ?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < st.cs_next_id /\
       b <= w2n w /\ w2n w + val_footprint tv v <= b+sz /\
       (!n lb lsz. local_region ce es.scopes s n lb lsz ==>
         b+sz <= lb \/ lb+lsz <= b)) ==>
  ptr_val_ok cx ty v op H tm t
Proof
  strip_tac >> irule ptr_val_ok_footprint_frame >>
  qexistsl [`G`, `s`, `tn`] >> simp[] >>
  conj_tac >- (rpt strip_tac >> gvs[ghost_kept_def]) >>
  conj_tac
  >- (`?w0. eval_operand op s = SOME w0` by gvs[expr_val_rel_def] >>
      drule_all abi_args_operand_kept >> simp[]) >>
  reverse conj_tac >- (drule_all ghost_kept_operand >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!tv w. _` drule_all >> strip_tac >> simp[] >>
  conj_tac
  >- (`mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (gvs[wb_frame_def] >> first_x_assum irule >> simp[] >>
         conj_tac >- metis_tac[] >> qexists `aid` >> simp[]) >>
      drule mem_bytes_at_agree_window >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [ghost_kept_def]) >> strip_tac >>
  qpat_x_assum `!aid off sz i. FLOOKUP _ _ = _ /\ _ ==> _` irule >>
  simp[] >> qexistsl [`aid`, `b`, `sz`] >> simp[] >> metis_tac[]
QED
