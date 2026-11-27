(* The memory-backed SHA256 suffix at the reached argument cut. *)
Theory bodyShaMemoryMachineMods
Ancestors
  bodyFullHashShaBytesSuccess bodyMemBiSha256Compose bodyPtrHashBuiltinsCases
  bodyPtrHashBuiltinsShaStringInput bodyPtrHashBuiltinsInputWindow
  exprSimHash exprSimHashBoundary exprSimWordArgs exprOperandVar exprLoweringProps
  bodyMethodIdScratchFrameMods bodyFullShadowBodyInv instSeqPtrLo
  loweringPosts loweringStateRelDefs fragExec stmtReasonLitFragMemory
  compileEnv builtinHashing bodyPtrDefs ptrDiscipline venomState venomInstProps
  vyperInterpreter vyperTyping vyperValue vyperAST vyperTypeSystem
  arithmetic words finite_map list pred_set

Theorem sha_memory_view[local]:
  expr_post H ctx func ce cx e es sa sm s0 mid v x s /\
  expr_type e = BaseT bt /\
  ((?k. bt = StringT k) \/ (?k. bt = BytesT (Dynamic k))) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bt) /\
  value_has_type (BaseTV bt) v /\
  ptr_val_ok cx (expr_type e) v x G tn s ==>
  ?p b. x = Var p /\ eval_operand x s = SOME (n2w b) /\
    mem_word_at b s.vs_memory = n2w (LENGTH (precompile_input Sha256 [v])) /\
    mem_bytes_at (b+32) (LENGTH (precompile_input Sha256 [v])) s.vs_memory =
      precompile_input Sha256 [v] /\
    b+32 < dimword (:256) /\ LENGTH (precompile_input Sha256 [v]) < dimword (:256) /\
    ptr_covers G tn p s (32 + LENGTH (precompile_input Sha256 [v])) /\
    (!i. b <= i /\ i < b+32+LENGTH (precompile_input Sha256 [v]) ==> i NOTIN tn.t_mem) /\
    (LENGTH (precompile_input Sha256 [v]) = 0 \/
      (?aid a k. FLOOKUP s.vs_allocas aid = SOME (a,k) /\ aid < sm.cs_next_id /\
                 a <= b+32 /\ b+32+LENGTH (precompile_input Sha256 [v]) <= a+k) \/
      (?nm a k. local_region ce mid.scopes s nm a k /\
                a <= b+32 /\ b+32+LENGTH (precompile_input Sha256 [v]) <= a+k))
Proof
  strip_tac >> gvs[] >> Cases_on `v` >> gvs[value_has_type_def]
  >- (
    `expr_val_at ce cx (expr_type e) sa sm mid (StringV s') x s` by
      fs[expr_post_def, is_bytestring_type_def] >>
    `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
    drule hash_string_post_view >> simp[] >> strip_tac >>
    gvs[] >>
    drule_all_then strip_assume_tac hash_string_operand >>
    `b < dimword (:256)` by decide_tac >>
    drule hash_string_input_window >>
    disch_then (qspecl_then [`n2w b`, `sm`] mp_tac) >>
    simp[wordsTheory.w2n_n2w, LESS_MOD] >> disch_tac >>
    qexists_tac `b` >>
    qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` mp_tac >>
    rewrite_tac [List.nth (CONJUNCTS precompile_input_def, 1)] >>
    qpat_x_assum `ptr_covers G tn _ s _` mp_tac >>
    simp[wordsTheory.w2n_n2w, LESS_MOD])
  >- (
    `expr_val_at ce cx (expr_type e) sa sm mid (BytesV l) x s` by
      fs[expr_post_def, is_bytestring_type_def] >>
    `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
    drule hash_dynamic_post_view >> simp[] >> strip_tac >>
    gvs[] >>
    drule_all_then strip_assume_tac hash_dynamic_bytes_operand >>
    `b < dimword (:256)` by decide_tac >>
    drule hash_dynamic_bytes_input_window >>
    disch_then (qspecl_then [`n2w b`, `sm`] mp_tac) >>
    simp[wordsTheory.w2n_n2w, LESS_MOD] >> disch_tac >>
    qexists_tac `b` >>
    qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` mp_tac >>
    rewrite_tac [CONJUNCT1 precompile_input_def] >>
    qpat_x_assum `ptr_covers G tn _ s _` mp_tac >>
    simp[wordsTheory.w2n_n2w, LESS_MOD])
QED

Theorem sha_memory_machine_mods:
  expr_post (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx e es sa sm s0 mid v x s /\
  expr_type e = BaseT bt /\
  ((?k. bt = StringT k) \/ (?k. bt = BytesT (Dynamic k))) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bt) /\
  value_has_type (BaseTV bt) v /\
  ptr_val_ok cx (expr_type e) v x G tn s /\
  lower_value compile_expr ce (expr_type e) e sa = (x,sm) /\
  compile_sha256_bytes x sm = (op,sn) /\
  expr_store_bound cx (expr_type e) v x s /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!p k. ce.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  (!p k. ce.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv_at_mods (DF H) lo d ce cx mid G tn s ==>
  let bs = precompile_input Sha256 [v]; I = emitted_insts sm sn in
  run_inst_seq_mem_ok I s /\
  ?r Gf tf. run_inst_seq I s = r /\ inst_seq_ptr (DF H) lo ctx func PG G tn I s Gf tf /\
    ((?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
      ?z outcome rest. r = OK z /\ s.vs_outcomes = outcome::rest /\ outcome.co_success /\
        eval_operand op z = SOME (SHA_256_bytes bs) /\
        ghost_inv_at (DF H) 0 d ce cx (mid with outcomes := SOME rest) Gf tf
          (z with vs_inst_idx := s.vs_inst_idx+7) /\
        ghost_kept_at 0 ce mid sm G tn s Gf tf /\ op_taint tf op = {} /\
        op_prov Gf op = NONE /\
        (!p. not_fresh_at sm p ==> lookup_var p z = lookup_var p s) /\
        pure_frame ce func mid sm s z) /\
    (~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
      ?z. r = Abort (if s.vs_outcomes = [] then ExHalt_abort else Revert_abort) z)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rewrite_tac[LET_THM] >> BETA_TAC >>
  `is_bytestring_type (expr_type e) /\ is_bytes_or_string_type (expr_type e)` by
    (qpat_assum `(?k. bt = StringT k) \/ _` mp_tac >>
     strip_tac >> gvs[is_bytestring_type_def, is_bytes_or_string_type_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sm sn) s` by
    (drule sha256_typed_suffix_mem_ok >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  drule_all_then (qx_choosel_then [`p`,`b`] (map_every assume_tac o CONJUNCTS))
    sha_memory_view >>
  qpat_x_assum `x = Var p` SUBST_ALL_TAC >>
  qabbrev_tac `bs = precompile_input Sha256 [v]` >>
  `b < dimword (:256)` by decide_tac >>
  `?rootbase cap. FLOOKUP G p = SOME (rootbase,cap) /\ rootbase <= b /\
      b+32+LENGTH bs <= rootbase+cap /\ op_taint tn (Var p) = {}` by
    (qpat_assum `ptr_covers _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
     qpat_assum `eval_operand (Var p) s = _`
       (assume_tac o REWRITE_RULE[eval_operand_def]) >>
     `w = n2w b` by
       (qpat_assum `lookup_var p s = SOME w` mp_tac >>
        qpat_assum `lookup_var p s = SOME (n2w b)` mp_tac >>
        rpt (pop_assum kall_tac) >> metis_tac[optionTheory.SOME_11]) >>
     qpat_x_assum `w = n2w b` SUBST_ALL_TAC >>
     `w2n (n2w b:bytes32) = b` by simp[wordsTheory.w2n_n2w, LESS_MOD] >>
     qexistsl_tac [`b'`,`sz'`] >> simp[] >>
     qpat_assum `w2n (n2w b:bytes32) = b` (fn th =>
       qpat_assum `b' <= w2n _` (mp_tac o REWRITE_RULE[th]) >>
       qpat_assum `_ + _ <= b' + sz'` (mp_tac o REWRITE_RULE[th])) >>
     decide_tac) >>
  `not_fresh_at sm p` by (drule compile_lower_value_var >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by (drule (CONJUNCT2 compile_expr_grows) >> simp[]) >>
  `local_ptrs_reserved ce sm` by (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `(!p k. ce.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p) /\
   (!p k. ce.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p)` by
    (simp[not_fresh_at_def] >> metis_tac[not_fresh_at_def, LESS_EQ_TRANS]) >>
  `stmt_state_rel H ctx func ce cx mid s` by metis_tac[expr_post_state] >>
  drule_all_then assume_tac hash_sha256_memory_alloca_code >>
  `sn.cs_current_bb = sm.cs_current_bb /\
   sn.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sn` by
    (qpat_assum `compile_sha256_bytes _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[hash_buffer_suffix_shape, same_blocks_def]) >>
  drule_all_then strip_assume_tac fn_has_code_code >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `isPREFIX (emitted_insts sm sn) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_then assume_tac method_id_ghost_at_zero >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  Cases_on `?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success`
  >- suspend "success"
  >- suspend "abort"
QED

Resume sha_memory_machine_mods[success]:
  pop_assum strip_assume_tac >>
  `?t Gf tf. run_inst_seq (emitted_insts sm sn) s = OK t /\
    inst_seq_ptr (DF H) 0 ctx func PG G tn (emitted_insts sm sn) s Gf tf /\
    eval_operand op t = SOME (SHA_256_bytes bs) /\
    ghost_inv_at (DF H) 0 d ce cx (mid with outcomes := SOME rest) Gf tf
      (t with vs_inst_idx := s.vs_inst_idx+7) /\
    ghost_kept_at 0 ce mid sm G tn s Gf tf /\ op_taint tf op = {} /\
    op_prov Gf op = NONE` by
      (irule sha_bytes_success_frame_at >> simp[] >>
       reverse conj_tac >- (qexists_tac `H` >> first_assum ACCEPT_TAC) >>
       qexistsl_tac [`b`,`cap`,`LENGTH bs`,`rootbase`,`p`] >>
       `b + (LENGTH bs + 32) = b+32+LENGTH bs` by decide_tac >>
       `cap+rootbase = rootbase+cap` by decide_tac >>
       qpat_assum `b + (LENGTH bs + 32) = _` (fn th => pure_rewrite_tac[th]) >>
       qpat_assum `cap+rootbase = _` (fn th => pure_rewrite_tac[th]) >>
       qpat_assum `LENGTH bs = 0 \/ _` (assume_tac o REWRITE_RULE[LENGTH_NIL]) >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. Var p = Var x ==> not_fresh_at sm x` by simp[] >>
  drule_all compile_sha256_bytes_frame >> disch_then (qx_choose_then `z` strip_assume_tac) >>
  `z = t` by
    (qpat_assum `run_inst_seq _ s = OK z` mp_tac >>
     qpat_assum `run_inst_seq _ s = OK t` (fn th => rewrite_tac[th]) >> simp[]) >>
  qpat_x_assum `z = t` SUBST_ALL_TAC >>
  qexistsl_tac [`OK t`,`Gf`,`tf`] >> simp[] >>
  conj_tac
  >- (irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `DF H` >> simp[]) >>
  qpat_x_assum `ghost_inv_at _ 0 _ _ _ _ _ _ (t with vs_inst_idx := _)` mp_tac >> simp[]
QED

Resume sha_memory_machine_mods[abort]:
  drule_all sha_bytes_abort_ptr_at >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`Abort (if s.vs_outcomes = [] then ExHalt_abort else Revert_abort) t`,`Gf`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `DF H` >> simp[]) >>
  simp[] >> metis_tac[]
QED

Finalise sha_memory_machine_mods
