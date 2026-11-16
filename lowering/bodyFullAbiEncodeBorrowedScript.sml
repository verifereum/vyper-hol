(* Uncaptured ABI operands: nonmutation preserves bytes, the full ghost
   frame preserves taint over the whole local region, including length words. *)
Theory bodyFullAbiEncodeBorrowed
Ancestors
  abiEncodeArgsSim logValueFramePtr bodyPtrDefs loweringPosts exprSimProps
  valueEncodingProps valueEncodingProofs ptrDiscipline

Theorem borrowed_footprint_frame[local]:
  expr_sim_inv ce cx env es /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s /\
  stmt_state_rel (H1:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee t /\ ee.scopes = es.scopes /\
  local_ptrs_reserved ce st /\ wb_frame ce es ee st s t /\
  ghost_kept_at lo ce es st G tn s G' tn' /\
  sb.cs_next_id <= st.cs_next_id /\
  expr_val_at ce cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w ==>
  val_wf tv v /\
  mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
  (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\
       i IN tn'.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[]
  >- (conj_tac
      >- (`mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
            (fs[wb_frame_def] >> first_x_assum irule >>
             conj_tac >- metis_tac[] >> qexists `aid` >> simp[] >> decide_tac) >>
          `w2n w = b + (w2n w - b)` by decide_tac >>
          `w2n w - b + val_footprint tv v <= sz` by decide_tac >>
          drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
          disch_then (qspecl_then [`w2n w - b`, `val_footprint tv v`] mp_tac) >>
          simp[]) >>
      rpt strip_tac >> fs[ghost_kept_at_def] >>
      qpat_x_assum `!aid off sz i. FLOOKUP _ _ = _ /\ _ ==> _` irule >>
      conj_tac >- (qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
        gvs[] >> decide_tac) >>
      simp[])
  >- (conj_tac
      >- (irule abi_args_local_window_kept >> metis_tac[]) >>
      rpt strip_tac >> fs[ghost_kept_at_def] >>
      qpat_x_assum `!n b sz i. local_region _ _ _ _ _ _ /\ _ ==> _` irule >>
      conj_tac >- simp[] >>
      qexistsl_tac [`b`, `n`, `sz`] >> simp[] >> decide_tac)
  >> simp[valueEncodingDefsTheory.mem_bytes_at_def] >> rpt strip_tac >> decide_tac
QED

Theorem abi_encode_borrowed_operand_retained:
  expr_sim_inv ce cx env es /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s /\
  stmt_state_rel (H1:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee t /\ ee.scopes = es.scopes /\
  local_ptrs_reserved ce st /\ wb_frame ce es ee st s t /\
  ghost_kept_at lo ce es st G tn s G' tn' /\
  sb.cs_next_id <= st.cs_next_id /\
  (!x. op = Var x ==> not_fresh_at st x) /\ (!l. op <> Label l) /\
  expr_val_rel cx ty v op s /\ expr_val_at ce cx ty sa sb es v op s /\
  ptr_val_ok cx ty v op G tn s ==>
  expr_val_rel cx ty v op t /\ expr_val_at ce cx ty sa sb ee v op t /\
  ptr_val_ok cx ty v op G' tn' t
Proof
  strip_tac >>
  `eval_operand op s = eval_operand op t` by
    (Cases_on `eval_operand op s` >> gvs[expr_val_rel_def] >>
     metis_tac[abi_args_operand_kept]) >>
  conj_tac >- (irule abi_args_value_kept_eq >> metis_tac[]) >>
  conj_tac >- (irule abi_args_location_kept_eq >> simp[] >> metis_tac[]) >>
  irule ptr_val_ok_footprint_frame >> qexistsl_tac [`G`, `s`, `tn`] >> simp[] >>
  conj_tac >- (Cases_on `op` >> gvs[ghost_kept_at_def, op_taint_def]) >>
  reverse conj_tac
  >- (Cases_on `op` >> gvs[ghost_kept_at_def, op_taint_def]) >>
  rpt gen_tac >> strip_tac >>
  `eval_operand op s = SOME w` by metis_tac[] >>
  drule_all borrowed_footprint_frame >> simp[]
QED
