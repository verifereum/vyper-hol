(* Topics consume physical capture types, not declared indexed capacities.
   The positional relation permits a caller to select any indexed subsequence
   while retaining each captured operand's actual type and value. *)
Theory bodyFullLogScalarTopics
Ancestors
  bodyFullLogArgs bodyFullLogSuffix stmtSimLogArgs supportedTypes list
  stmtSimLogTopics stmtLogTopicsMemory valueCopyBytes exprSimMemDefs
  exprSimProps vyperTyping vfmConstants

Theorem compile_log_scalar_topics_from_capture:
  log_full_post DF lo d ctx func cenv cx es sa sm s0 G0 tn0 args captured
    H (INL vs) ee G tn s /\
  expr_sim_inv cenv cx env inv_es /\ local_ptrs_reserved cenv sm /\
  LIST_REL (\arg v. supported_scalar_type (SND arg) /\
    ?j. j < LENGTH args /\ v = EL j vs /\
        FST arg = FST (EL j captured) /\
        SND arg = expr_type (EL j args)) xs ivs /\
  compile_log_topic_ops (MAP (\p. (FST p,is_bytestring_type (SND p))) xs) sm =
    (ops,sb) /\
  encode_indexed_event_topics (REPLICATE (LENGTH xs) T) (MAP SND xs) ivs =
    SOME topics /\
  ~ctx_has_dalloca ctx /\
  fn_has_code sm sb func /\ ~s.vs_halted /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
           (OK t,Gf,tnf)) /\
    (t with <| vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx |>) = s /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted /\
    LIST_REL (\op w. eval_operand op t = SOME w) ops topics /\
    EVERY (\op. op_taint tnf op = {}) ops /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sm p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    stmt_state_rel H ctx func cenv cx ee t /\
    ((!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
             not_fresh_at sm x) /\
     (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
             not_fresh_at sm x) ==>
     !D d. ghost_inv_at D lo d cenv cx ee G tn s ==>
           ghost_inv_at D lo d cenv cx ee Gf tnf t)
Proof
  strip_tac >>
  qpat_x_assum `log_full_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [log_full_post_def]) >> gvs[] >>
  `LIST_REL (\arg v. log_arg_rel cenv cx sa sm ee s arg v /\
      supported_scalar_type (SND arg) /\
      ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v)
      xs ivs /\
   LIST_REL (\arg v. ptr_val_ok cx (SND arg) v (FST arg) G tn s) xs ivs /\
   EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
               (!l. FST p <> Label l)) xs /\
   LIST_REL (\arg v. expr_store_bound cx (SND arg) v (FST arg) s) xs ivs` by
    (fs[LIST_REL_EL_EQN, EVERY_EL] >> rpt conj_tac >> rpt strip_tac >>
     qpat_assum `!n. n < LENGTH xs ==> _`
       (qspec_then `n` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
     qpat_assum `!n. n < LENGTH captured /\ n < LENGTH args ==> _`
       (qspec_then `j` assume_tac) >>
     `j < LENGTH captured` by decide_tac >>
     qpat_x_assum `j < LENGTH captured /\ j < LENGTH args ==> _`
       (fn th => drule_all_then strip_assume_tac th) >>
     `EL j (ZIP (MAP FST captured,args)) =
        (FST (EL j captured),EL j args)` by
       (dep_rewrite.DEP_REWRITE_TAC [EL_ZIP, EL_MAP] >> simp[]) >>
     fs[] >>
     Cases_on `EL n xs` >> fs[log_arg_rel_def] >>
     Cases_on `expr_type (EL j args)` >>
     fs[supported_scalar_type_def, supported_word_type_def,
        supported_string_type_def] >>
     metis_tac[log_arg_clear_base, pairTheory.PAIR]) >>
  `LENGTH xs = LENGTH ivs` by metis_tac[LIST_REL_LENGTH] >>
  (* The capture's actual read extent supplies the hash memory check. *)
  `LIST_REL (\arg v. !w len. ~is_word_type (SND arg) /\
      eval_operand (FST arg) s = SOME w /\
      ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
       (?str. v = StringV str /\ len = LENGTH str)) ==>
      w2n w + (32*((len+31) DIV 32)+32) <= s.vs_alloca_next) xs ivs` by
    (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
     qpat_assum `LIST_REL (\arg v. log_arg_rel _ _ _ _ _ _ _ _ /\ _) xs ivs`
       (mp_tac o Q.SPEC `n` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     qpat_assum `LIST_REL (\arg v. expr_store_bound _ _ _ _ _) xs ivs`
       (mp_tac o Q.SPEC `n` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     simp[] >> rpt strip_tac >>
     `is_bytestring_type (SND (EL n xs))` by
       metis_tac[stmtSimLogTopicsTheory.log_scalar_topic_shape] >>
     drule_all valueCopyBytesTheory.bytestring_type_value >> strip_tac >>
     gvs[vyperTypingTheory.value_has_type_def,
         exprSimMemDefsTheory.expr_store_bound_def,
         exprSimPropsTheory.val_store_size_def,
         vfmConstantsTheory.word_size_def] >> decide_tac) >>
  `LIST_REL (\arg v. supported_scalar_type (SND arg) /\
      ?aty tv. supported_scalar_type aty /\
        log_arg_rel cenv cx sa sm ee s (FST arg,aty) v /\
        evaluate_type (get_tenv cx) aty = SOME tv /\ value_has_type tv v /\
        (is_bytestring_type aty <=> is_bytestring_type (SND arg)) /\
        encode_event_topic aty v = encode_event_topic (SND arg) v) xs ivs` by
    (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
     qpat_assum `LIST_REL (\arg v. log_arg_rel _ _ _ _ _ _ _ _ /\ _) xs ivs`
       (mp_tac o Q.SPEC `n` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     simp[] >> strip_tac >>
     qexistsl_tac [`SND (EL n xs)`,`tv`] >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) s` by
    (irule stmtLogTopicsMemoryTheory.compile_log_topic_ops_mem_ok >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `compile_log_topic_ops _ _ = _`)) >>
     qexistsl_tac [`sa`,`ivs`] >> simp[]) >>
  drule_all compile_log_topic_ops_origin_ptr_path >> simp[]
QED

(* Backward-compatible wrapper: the original statement remains exact. *)
Theorem compile_log_scalar_topics_full:
  log_full_post DF lo d ctx func cenv cx es sa sm s0 G0 tn0 args captured
    H (INL vs) ee G tn s /\
  expr_sim_inv cenv cx env ee /\ local_ptrs_reserved cenv sm /\
  LIST_REL (\arg v. supported_scalar_type (SND arg) /\
    ?j. j < LENGTH args /\ v = EL j vs /\
        FST arg = FST (EL j captured) /\
        SND arg = expr_type (EL j args)) xs ivs /\
  compile_log_topic_ops (MAP (\p. (FST p,is_bytestring_type (SND p))) xs) sm =
    (ops,sb) /\
  encode_indexed_event_topics (REPLICATE (LENGTH xs) T) (MAP SND xs) ivs =
    SOME topics /\
  ~ctx_has_dalloca ctx /\ run_inst_seq_mem_ok (emitted_insts sm sb) s /\
  fn_has_code sm sb func /\ ~s.vs_halted /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
           (OK t,Gf,tnf)) /\
    (t with <| vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx |>) = s /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted /\
    LIST_REL (\op w. eval_operand op t = SOME w) ops topics /\
    EVERY (\op. op_taint tnf op = {}) ops /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sm p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    stmt_state_rel H ctx func cenv cx ee t /\
    ((!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
             not_fresh_at sm x) /\
     (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
             not_fresh_at sm x) ==>
     !D d. ghost_inv_at D lo d cenv cx ee G tn s ==>
           ghost_inv_at D lo d cenv cx ee Gf tnf t)
Proof
  strip_tac >>
  mp_tac (Q.INST [`inv_es` |-> `ee`] (SPEC_ALL compile_log_scalar_topics_from_capture)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]
QED
