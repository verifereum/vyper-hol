(* Scalar representation boundaries for the pointer log pipeline. *)
Theory logValueFramePtr
Ancestors
  representationCleanPtr robustCopyTransportPtr bodyPtrDefs stmtSimLogArgs exprSimProps
  pred_set loweringPosts
  valueEncoding valueEncodingProps valueEncodingProofs
  venomState ptrDiscipline finite_map words list arithmetic

Theorem ptr_val_ok_bytes_word_clean:
  !cx ty bs op G tn s tv w.
    ptr_val_ok cx ty (BytesV bs) op G tn s /\ ~is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w ==>
    !i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem
Proof
  rpt gen_tac >> strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory tv (BytesV bs) (w2n w) mem` by
    (gvs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]) >>
  drule robust_val_in_memory_bytes_clean >> simp[]
QED

Theorem ptr_val_ok_bytes_payload_clean:
  !cx ty bs op G tn s tv w.
    ptr_val_ok cx ty (BytesV bs) op G tn s /\ ~is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k))) /\
    eval_operand op s = SOME w ==>
    !i. w2n w + 32 <= i /\ i < w2n w + 32 + LENGTH bs ==>
        i NOTIN tn.t_mem
Proof
  rpt gen_tac >> strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory tv (BytesV bs) (w2n w) mem` by
    (gvs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]) >>
  drule robust_val_in_memory_bytes_clean >> simp[]
QED

Theorem ptr_buf_ok_frame:
  !cenv e op G G' s t.
    ptr_buf_ok cenv e op G s /\
    (!w. eval_operand op t = SOME w ==> eval_operand op s = SOME w) /\
    (!x. op = Var x ==> FLOOKUP G' x = FLOOKUP G x) ==>
    ptr_buf_ok cenv e op G' t
Proof
  rw[ptr_buf_ok_def] >> metis_tac[]
QED

(* Expressions may remove taint in an older value's footprint, but cannot
   introduce it.  Padding is deliberately outside this boundary. *)
Theorem robust_val_in_memory_footprint_frame:
  !tv v p tn tn' mem mem'.
    val_wf tv v /\
    mem_bytes_at p (val_footprint tv v) mem' =
      mem_bytes_at p (val_footprint tv v) mem /\
    (!i. p <= i /\ i < p + val_footprint tv v /\ i IN tn' ==> i IN tn) /\
    (!m. mem_agree_outside tn mem m ==> val_in_memory tv v p m) ==>
    !m. mem_agree_outside tn' mem' m ==> val_in_memory tv v p m
Proof
  rpt gen_tac >> strip_tac >>
  `!m. mem_agree_outside (tn UNION tn') mem' m ==>
       val_in_memory tv v p m` by
    (rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
     conj_tac >- simp[] >>
     qexistsl_tac [`mem`, `mem'`, `val_footprint tv v`, `p`, `tn`, `tn UNION tn'`] >>
     simp[] >> rpt strip_tac >> eq_tac >> simp[] >>
     strip_tac >> first_x_assum irule >> simp[] >> decide_tac) >>
  rpt strip_tac >> first_x_assum irule >>
  gvs[mem_agree_outside_def] >> metis_tac[]
QED

Theorem log_argument_taint_kept:
  !cenv cx ty tv v op sa sb es s G0 tn0 G tn w i.
    expr_val_at cenv cx ty sa sb es v op s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    log_arg_clear cenv cx ty v /\ eval_operand op s = SOME w /\
    ghost_kept cenv es sb G0 tn0 s G tn /\
    w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn.t_mem ==>
    i IN tn0.t_mem
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_val_at_def]) >>
  disch_then (qspec_then `tv` mp_tac) >> simp[] >> strip_tac
  >- (gvs[] >> gvs[ghost_kept_def] >>
      qpat_x_assum `!aid off sz i. FLOOKUP _ _ = _ /\ _ ==> _` irule >>
      simp[] >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
      metis_tac[])
  >- (gvs[] >>
      `!k. dynarray_len_at cenv n k ==>
         w2n w + val_footprint tv v <= b+k \/ b+k+32 <= w2n w` by
        (qpat_x_assum `log_arg_clear _ _ _ _`
           (mp_tac o REWRITE_RULE [log_arg_clear_def]) >>
         disch_then (qspecl_then [`tv`, `n`, `w2n w - b`] mp_tac) >>
         simp[] >> strip_tac >> gen_tac >> strip_tac >>
         first_x_assum drule >> decide_tac) >>
      gvs[ghost_kept_def] >> first_x_assum irule >>
      simp[] >> qexistsl_tac [`b`, `n`, `sz`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  gvs[]
QED

Theorem ptr_val_ok_footprint_frame:
  !cx ty v op G tn s G' tn' t.
    ptr_val_ok cx ty v op G tn s /\
    op_taint tn' op = op_taint tn op /\
    (!x. op = Var x ==> FLOOKUP G' x = FLOOKUP G x) /\
    (!w. eval_operand op t = SOME w ==> eval_operand op s = SOME w) /\
    (!tv w. ~is_word_type ty /\
       evaluate_type (get_tenv cx) ty = SOME tv /\
       eval_operand op s = SOME w ==>
       val_wf tv v /\
       mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
         mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
       (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\
            i IN tn'.t_mem ==> i IN tn.t_mem)) ==>
    ptr_val_ok cx ty v op G' tn' t
Proof
  rpt gen_tac >> strip_tac >>
  simp[ptr_val_ok_def] >> conj_tac
  >- gvs[ptr_val_ok_def] >> conj_tac
  >- (strip_tac >> gvs[ptr_val_ok_def] >> Cases_on `op` >> gvs[op_prov_def]) >>
  strip_tac >>
  simp[ptr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  `eval_operand op s = SOME w` by metis_tac[] >>
  `val_wf tv v /\
   mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
     mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
   (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\
        i IN tn'.t_mem ==> i IN tn.t_mem)` by metis_tac[] >>
  `(!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory tv v (w2n w) mem) /\
   (val_footprint tv v <> 0 ==>
    ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
             b <= w2n w /\ w2n w + val_store_size tv v <= b+sz)` by
    (gvs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule robust_val_in_memory_footprint_frame >>
      conj_tac >- simp[] >>
      qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tn'.t_mem`] >> simp[]) >>
  metis_tac[]
QED

Theorem log_argument_ptr_val_kept:
  !cenv cx ty v op sa sb es es' s t G0 tn0 G tn.
    ptr_val_ok cx ty v op G0 tn0 s /\ expr_val_rel cx ty v op s /\
    expr_val_at cenv cx ty sa sb es v op s /\ 
    wb_frame cenv es es' sb s t /\ ghost_kept cenv es sb G0 tn0 s G tn /\
    (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l) /\
    log_arg_clear cenv cx ty v ==>
    ptr_val_ok cx ty v op G tn t
Proof
  rpt gen_tac >> strip_tac >> irule ptr_val_ok_footprint_frame >>
  qexistsl_tac [`G0`, `s`, `tn0`] >> simp[] >>
  conj_tac >- (rpt strip_tac >> gvs[ghost_kept_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `?w0. eval_operand op s = SOME w0` by
        gvs[expr_val_rel_def] >>
      drule_all log_frame_operand >> simp[]) >>
  reverse conj_tac
  >- (Cases_on `op` >> gvs[ghost_kept_def, op_taint_def]) >>
  rpt gen_tac >> strip_tac >>
  `val_wf tv v` by (gvs[expr_val_at_def] >> metis_tac[]) >> simp[] >>
  conj_tac
  >- (irule log_argument_footprint_kept >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  rpt strip_tac >> drule_all log_argument_taint_kept >> simp[]
QED
