Theory abiArgsLabelBoundary
Ancestors compileEnv exprSimDefs exprSimProps loweringPosts exprSimHyps exprSimWordArgs abiArgsLabelObserver
  fragExec venomExecProofs venomExecSemantics exprSimAbiEncodeArgsCountedLabels

(* Operational steps include returning INVOKE: the caller label map survives. *)
Theorem abi_args_step_labels:
  step_inst fuel ctx inst s = OK t ==> t.vs_labels = s.vs_labels
Proof
  metis_tac[step_inst_preserves_labels_always]
QED

Theorem abi_args_merge_labels:
  (merge_callee_state caller callee).vs_labels = caller.vs_labels
Proof
  simp[merge_callee_state_def]
QED

Theorem abi_args_operand_control_only:
  eval_operand op (s with <|vs_halted := halted; vs_current_bb := bb; vs_inst_idx := idx|>) =
  eval_operand op s
Proof
  Cases_on `op` >> simp[venomStateTheory.eval_operand_def,
    venomStateTheory.lookup_var_def]
QED

(* Control changes are harmless only when the label map is retained. *)
Theorem abi_args_state_rel_control_only:
  stmt_state_rel ctx func ce cx es
    (s with <|vs_halted := halted; vs_current_bb := bb; vs_inst_idx := idx|>) <=>
  stmt_state_rel ctx func ce cx es s
Proof
  simp[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def,
       local_ptrs_rel_def, local_region_def, local_backed_def,
       venomStateTheory.lookup_var_def, storage_rel_def, transient_rel_def,
       accounts_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def,
       venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def,
       exprLoweringPropsTheory.alloca_room_def,
       exprLoweringPropsTheory.pending_alloca_size_def,
       exprLoweringPropsTheory.immutable_alloca_sep_def,
       exprLoweringPropsTheory.fmp_room_def, immutable_base_zero_def,
       abi_args_operand_control_only]
QED

Theorem abi_args_immutable_base_kept:
  stmt_state_rel ctx func ce cx es t /\
  stmt_state_rel ctx func ce cx es' u /\
  ce.ce_imm_alloca = SOME op ==>
  eval_operand op t = eval_operand op u
Proof
  simp[exprLoweringPropsTheory.stmt_state_rel_def, immutable_base_zero_def] >>
  metis_tac[]
QED

Theorem abi_args_state_rel_label_transport:
  immutable_base_zero ce (s with vs_labels := labels) = immutable_base_zero ce s ==>
  (stmt_state_rel ctx func ce cx es (s with vs_labels := labels) <=>
   stmt_state_rel ctx func ce cx es s)
Proof
  strip_tac >>
  simp[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def,
       local_ptrs_rel_def, local_region_def, local_backed_def,
       venomStateTheory.lookup_var_def, storage_rel_def, transient_rel_def,
       accounts_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def,
       venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def,
       exprLoweringPropsTheory.alloca_room_def,
       exprLoweringPropsTheory.pending_alloca_size_def,
       exprLoweringPropsTheory.immutable_alloca_sep_def,
       exprLoweringPropsTheory.fmp_room_def]
QED

Theorem abi_args_delete_unprotected_label:
  ce.ce_imm_alloca <> SOME (Label l) /\
  (ce.ce_is_ctor ==> l <> "runtime_begin") ==>
  immutable_base_zero ce (s with vs_labels := s.vs_labels \\ l) =
  immutable_base_zero ce s
Proof
  namedCases_on `ce.ce_imm_alloca` ["", "immop"]
  >- (simp[immutable_base_zero_def, finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
      metis_tac[]) >>
  Cases_on `immop` >>
  simp[immutable_base_zero_def, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
  metis_tac[]
QED

Theorem abi_args_label_observe[local]:
  expr_sim ctx func ce cx ty e es /\
  lower_value compile_expr ce ty e sa = (Label l,sb) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 ==>
  ?t. stmt_state_rel ctx func ce cx ee t /\
      expr_val_rel cx (post_value_type ce e) v (Label l) t /\
      expr_val_at ce cx (post_value_type ce e) sa sb ee v (Label l) t /\
      t.vs_labels = s0.vs_labels
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `stmt_state_rel ctx func ce cx es start` >>
  qabbrev_tac `z = start with <|vs_halted := F;
    vs_current_bb := sa.cs_current_bb;
    vs_inst_idx := LENGTH sa.cs_current_insts|>` >>
  `stmt_state_rel ctx func ce cx es z` by
    simp[Abbr `z`, abi_args_state_rel_control_only] >>
  `~z.vs_halted /\ z.vs_current_bb = sa.cs_current_bb /\
   z.vs_inst_idx = LENGTH sa.cs_current_insts` by simp[Abbr `z`] >>
  drule_all abi_args_counted_label_observe >>
  simp[Abbr `z`] 
QED

Theorem abi_args_success_label_classification:
  expr_sim ctx func ce cx (expr_type e) e es /\
  lower_value compile_expr ce (expr_type e) e sa = (Label l,sm) /\
  (bind (eval_expr cx e) (read_result cx)) es = (INL v,es1) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 ==>
  ce.ce_imm_alloca = SOME (Label l) \/ (ce.ce_is_ctor /\ l = "runtime_begin")
Proof
  strip_tac >> spose_not_then assume_tac >>
  `ce.ce_imm_alloca <> SOME (Label l) /\
   (ce.ce_is_ctor ==> l <> "runtime_begin")` by metis_tac[] >>
  `immutable_base_zero ce (s0 with vs_labels := s0.vs_labels \\ l) =
   immutable_base_zero ce s0` by metis_tac[abi_args_delete_unprotected_label] >>
  `stmt_state_rel ctx func ce cx es (s0 with vs_labels := s0.vs_labels \\ l)` by
    metis_tac[abi_args_state_rel_label_transport] >>
  drule_all abi_args_label_observe >>
  simp[expr_val_rel_def, venomStateTheory.eval_operand_def,
       finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
  rpt strip_tac >> gvs[]
QED

(* Empty typed aggregates exercise the explicit zero-footprint escape. *)
Theorem abi_args_empty_tuple_footprint:
  val_footprint (TupleTV []) (ArrayV (TupleV [])) = 0 /\
  val_wf (TupleTV []) (ArrayV (TupleV [])) /\
  value_has_type (TupleTV []) (ArrayV (TupleV [])) /\
  (!p mem. val_in_memory (TupleTV []) (ArrayV (TupleV [])) p mem)
Proof
  EVAL_TAC >> simp[]
QED

Theorem abi_args_runtime_empty_tuple_location:
  FLOOKUP s.vs_labels "runtime_begin" = SOME w ==>
  expr_val_rel cx (TupleT []) (ArrayV (TupleV [])) (Label "runtime_begin") s /\
  expr_val_at ce cx (TupleT []) sa sb es (ArrayV (TupleV [])) (Label "runtime_begin") s
Proof
  simp[expr_val_rel_def, expr_val_at_def, venomStateTheory.eval_operand_def,
       vyperValueTheory.evaluate_type_def, is_word_type_def,
       abi_args_empty_tuple_footprint, valueEncodingTheory.val_in_memory_def]
QED

Theorem abi_args_update_runtime_label:
  ce.ce_imm_alloca <> SOME (Label "runtime_begin") /\
  immutable_base_zero ce s ==>
  immutable_base_zero ce
    (s with vs_labels := s.vs_labels |+ ("runtime_begin",w))
Proof
  namedCases_on `ce.ce_imm_alloca` ["", "immop"]
  >- simp[immutable_base_zero_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `immop` >>
  simp[immutable_base_zero_def, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem abi_args_state_rel_update_runtime:
  stmt_state_rel ctx func ce cx es s /\
  ce.ce_imm_alloca <> SOME (Label "runtime_begin") ==>
  stmt_state_rel ctx func ce cx es
    (s with vs_labels := s.vs_labels |+ ("runtime_begin",w))
Proof
  strip_tac >>
  `immutable_base_zero ce s` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def] >>
  `immutable_base_zero ce
     (s with vs_labels := s.vs_labels |+ ("runtime_begin",w))` by
    metis_tac[abi_args_update_runtime_label] >>
  metis_tac[abi_args_state_rel_label_transport]
QED

Theorem abi_args_runtime_word_observed:
  expr_sim ctx func ce cx (expr_type e) e es /\
  lower_value compile_expr ce (expr_type e) e sa = (Label "runtime_begin",sm) /\
  (bind (eval_expr cx e) (read_result cx)) es = (INL v,es1) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\
  is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
  FLOOKUP s0.vs_labels "runtime_begin" = SOME w ==>
  w = typed_val_to_w256 tv v
Proof
  strip_tac >> drule_all abi_args_label_observe >>
  rpt strip_tac >>
  gvs[expr_val_rel_def, venomStateTheory.eval_operand_def]
QED

Theorem abi_args_runtime_word_is_base:
  expr_sim ctx func ce cx (expr_type e) e es /\
  lower_value compile_expr ce (expr_type e) e sa = (Label "runtime_begin",sm) /\
  (bind (eval_expr cx e) (read_result cx)) es = (INL v,es1) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\
  is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv ==>
  ce.ce_imm_alloca = SOME (Label "runtime_begin")
Proof
  strip_tac >> spose_not_then assume_tac >>
  `!w. stmt_state_rel ctx func ce cx es
     (s0 with vs_labels := s0.vs_labels |+ ("runtime_begin",w))` by
    metis_tac[abi_args_state_rel_update_runtime] >>
  `!w. FLOOKUP (s0 with vs_labels := s0.vs_labels |+ ("runtime_begin",w)).vs_labels
     "runtime_begin" = SOME w` by simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  `0w = typed_val_to_w256 tv v` by metis_tac[abi_args_runtime_word_observed] >>
  `1w = typed_val_to_w256 tv v` by metis_tac[abi_args_runtime_word_observed] >>
  gvs[]
QED

Theorem abi_args_zero_footprint_size:
  val_footprint tv v = 0 ==> type_memory_size tv = 0
Proof
  Cases_on `v` >> simp[val_footprint_def] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem abi_args_zero_footprint_relocate:
  val_in_memory tv v src mem /\ val_wf tv v /\ val_footprint tv v = 0 ==>
  val_in_memory tv v dst mem'
Proof
  strip_tac >>
  `type_memory_size tv = 0` by metis_tac[abi_args_zero_footprint_size] >>
  irule valueEncodingPropsTheory.val_in_memory_relocate >>
  simp[] >> qexistsl_tac [`mem`, `0`, `src`] >>
  simp[valueEncodingTheory.mem_bytes_at_def]
QED

Theorem abi_args_runtime_zero_transport:
  stmt_state_rel ctx func ce cx es' u /\ ce.ce_is_ctor /\
  ~is_word_type ty /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==> val_footprint tv v = 0) /\
  expr_val_rel cx ty v (Label "runtime_begin") t /\
  expr_val_at ce cx ty sa sb es v (Label "runtime_begin") t ==>
  expr_val_rel cx ty v (Label "runtime_begin") u /\
  expr_val_at ce cx ty sa sb es' v (Label "runtime_begin") u
Proof
  strip_tac >>
  `IS_SOME (FLOOKUP u.vs_labels "runtime_begin")` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def, immutable_base_zero_def] >>
  Cases_on `FLOOKUP u.vs_labels "runtime_begin"` >> gvs[] >>
  gvs[expr_val_rel_def, expr_val_at_def, venomStateTheory.eval_operand_def] >>
  metis_tac[abi_args_zero_footprint_relocate]
QED

Theorem abi_args_local_region_frontier:
  stmt_state_rel ctx func ce cx es s /\
  local_region ce es.scopes s name b sz ==>
  b + sz <= s.vs_alloca_next
Proof
  simp[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def,
       local_ptrs_rel_def, local_region_def] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >> gvs[]
QED

Theorem abi_args_value_at_frontier:
  stmt_state_rel ctx func ce cx es s /\
  expr_val_at ce cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w /\ 0 < val_footprint tv v ==>
  w2n w + val_footprint tv v <= s.vs_alloca_next
Proof
  strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[]
  >- (fs[exprLoweringPropsTheory.stmt_state_rel_def,
          venomMemDefsTheory.alloca_inv_def,
          venomMemDefsTheory.alloca_next_valid_def] >>
      first_x_assum drule >> decide_tac) >>
  drule_all abi_args_local_region_frontier >> decide_tac
QED

Theorem abi_args_runtime_footprint_observed:
  expr_sim ctx func ce cx (expr_type e) e es /\
  lower_value compile_expr ce (expr_type e) e sa = (Label "runtime_begin",sm) /\
  (bind (eval_expr cx e) (read_result cx)) es = (INL v,es1) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\
  ~is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
  FLOOKUP s0.vs_labels "runtime_begin" = SOME (-1w) ==>
  val_footprint tv v = 0
Proof
  strip_tac >> drule_all abi_args_label_observe >> strip_tac >>
  rename1 `stmt_state_rel ctx func ce cx es1 t` >>
  spose_not_then assume_tac >>
  `0 < val_footprint tv v` by decide_tac >>
  `eval_operand (Label "runtime_begin") t = SOME (-1w)` by
    simp[venomStateTheory.eval_operand_def] >>
  drule_all abi_args_value_at_frontier >>
  `t.vs_alloca_next < dimword (:256)` by
    metis_tac[exprLoweringPropsTheory.stmt_state_rel_def,
              exprLoweringPropsTheory.alloca_room_next_lt] >>
  simp[wordsTheory.word_2comp_n2w, wordsTheory.w2n_n2w,
       wordsTheory.dimword_def] >>
  fs[wordsTheory.dimword_def] >> decide_tac
QED

Theorem abi_args_runtime_nonbase_zero:
  expr_sim ctx func ce cx (expr_type e) e es /\
  lower_value compile_expr ce (expr_type e) e sa = (Label "runtime_begin",sm) /\
  (bind (eval_expr cx e) (read_result cx)) es = (INL v,es1) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\
  ce.ce_imm_alloca <> SOME (Label "runtime_begin") /\
  ~is_word_type (post_value_type ce e) ==>
  !tv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv ==>
       val_footprint tv v = 0
Proof
  rpt strip_tac >>
  `stmt_state_rel ctx func ce cx es
     (s0 with vs_labels := s0.vs_labels |+ ("runtime_begin",-1w))` by
    metis_tac[abi_args_state_rel_update_runtime] >>
  `FLOOKUP (s0 with vs_labels := s0.vs_labels |+ ("runtime_begin",-1w)).vs_labels
     "runtime_begin" = SOME (-1w)` by simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[abi_args_runtime_footprint_observed]
QED

Theorem abi_args_runtime_nonbase_transport:
  expr_sim ctx func ce cx (expr_type e) e es /\
  lower_value compile_expr ce (expr_type e) e sa = (Label "runtime_begin",sm) /\
  (bind (eval_expr cx e) (read_result cx)) es = (INL v,es1) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\
  ce.ce_imm_alloca <> SOME (Label "runtime_begin") /\ ce.ce_is_ctor /\
  stmt_state_rel ctx func ce cx es' u /\
  expr_val_rel cx (post_value_type ce e) v (Label "runtime_begin") t /\
  expr_val_at ce cx (post_value_type ce e) sc sd est v (Label "runtime_begin") t ==>
  expr_val_rel cx (post_value_type ce e) v (Label "runtime_begin") u /\
  expr_val_at ce cx (post_value_type ce e) sc sd es' v (Label "runtime_begin") u
Proof
  strip_tac >> Cases_on `is_word_type (post_value_type ce e)`
  >- (`!tv. evaluate_type (get_tenv cx) (post_value_type ce e) <> SOME tv` by
        metis_tac[abi_args_runtime_word_is_base] >>
      `IS_SOME (FLOOKUP u.vs_labels "runtime_begin")` by
        gvs[exprLoweringPropsTheory.stmt_state_rel_def, immutable_base_zero_def] >>
      Cases_on `FLOOKUP u.vs_labels "runtime_begin"` >> gvs[] >>
      simp[expr_val_rel_def, expr_val_at_def, venomStateTheory.eval_operand_def]) >>
  `!tv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv ==>
        val_footprint tv v = 0` by metis_tac[abi_args_runtime_nonbase_zero] >>
  metis_tac[abi_args_runtime_zero_transport]
QED

(* Consumer boundary: the original suffix witness is retained.  A protected
   base has the same operand value; a nonbase runtime label carries only a
   zero-footprint value (or an unevaluated type), so needs no address equality. *)
Theorem abi_args_success_label_transport:
  expr_sim ctx func ce cx (expr_type e) e es /\
  lower_value compile_expr ce (expr_type e) e sa = (Label l,sm) /\
  (bind (eval_expr cx e) (read_result cx)) es = (INL v,es1) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\
  stmt_state_rel ctx func ce cx es1 t /\ stmt_state_rel ctx func ce cx es' u /\
  expr_val_rel cx (post_value_type ce e) v (Label l) t /\
  expr_val_at ce cx (post_value_type ce e) sc sd est v (Label l) t ==>
  eval_operand (Label l) t = eval_operand (Label l) u \/
  (expr_val_rel cx (post_value_type ce e) v (Label l) u /\
   expr_val_at ce cx (post_value_type ce e) sc sd es' v (Label l) u)
Proof
  strip_tac >>
  drule_all abi_args_success_label_classification >> strip_tac
  >- metis_tac[abi_args_immutable_base_kept] >>
  Cases_on `ce.ce_imm_alloca = SOME (Label l)`
  >- metis_tac[abi_args_immutable_base_kept] >>
  gvs[] >> disj2_tac >> metis_tac[abi_args_runtime_nonbase_transport]
QED

(* Caller-premise audit for success_label_transport:
   abi_args_ready supplies expr_sim at Inv es; the uncaptured branch supplies
   lower_value, successful forced evaluation, head fn_has_code/distinctness and
   local_ptrs_reserved.  Its precondition supplies the related initial s0.
   The counted port additionally requires forced-evaluation gas_admissible,
   supplied by expr_body_pre_gas_admissible at the head environment (using
   abi_args_body_pre_arg and expr_body_pre_eval at later environments).
   Value/location conclusions now use post_value_type ce e, exactly as
   expr_post does; compiler calls still use expr_type e. No universal
   equality between these types is assumed. The forced source computation
   is written with bind directly to avoid eta-expansion matching failures.
   expr_post at the head witness t supplies stmt_state_rel, expr_val_rel and
   expr_val_at; abi_args_post at the ORIGINAL suffix witness u supplies the
   final stmt_state_rel.  Thus no expr_vv_sim, evaluated-type existence,
   positive-footprint, label equality or metadata-coherence premise is added.
   The equality alternative uses existing memory/frame transport; the other
   alternative already gives both value obligations at u.  Live operand and
   frame adapters are separate consumers, not asserted by this diagnostic. *)
