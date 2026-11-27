(* Topic selection keeps the originating expression attached to each saved
   compiler operand; filtering never repeats a snapshot decision. *)
Theory bodyLogTopicListMods
Ancestors
  bodyFullLogSuffix bodyAbiEncodePackedPostMods eventLogSplitProps
  stmtSimLogTopics stmtLowering exprSafeOperand venomExecSemantics list pair words
  fragGasOriginPtr ptrDiscipline loweringStateRelDefs compileEnv vyperEvent
  supportedTypes venomState bodyLogSavedRowAdvanceMods bodyLogCaptureOperandMods

Theorem log_split_saved_projection[local]:
  LENGTH flags = LENGTH rows ==>
  split_log_ops (MAP (\((e,sv),ty). (sv,ty)) rows) flags =
    (MAP (\((e,sv),hashed). (sv,hashed)) (FST (split_log_ops rows flags)),
     MAP (\((e,sv),ty). (sv,ty)) (SND (split_log_ops rows flags)))
Proof
  qid_spec_tac `rows` >> Induct_on `flags`
  >- (Cases_on `rows` >> simp[split_log_ops_def]) >>
  gen_tac >> Cases_on `rows` >- simp[] >>
  rename1 `LENGTH (flag::flags) = LENGTH (row::rows) ==> _` >>
  PairCases_on `row` >> Cases_on `flag` >>
  simp[split_log_ops_def, LET_THM] >>
  Cases_on `split_log_ops rows flags` >> simp[]
QED

Theorem log_topic_operand_words[local]:
  !ops topics.
    LIST_REL (\op w. safe_operand sb op /\
      eval_operand op t = SOME w /\ op_taint tf op = {}) ops topics ==>
    EVERY (safe_operand sb) ops /\ EVERY (\op. op_taint tf op = {}) ops /\
    eval_operands ops t = SOME topics
Proof
  Induct >> Cases_on `topics` >> simp[eval_operands_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem log_zip_indexed_and[local]:
  !flags rows vs.
    LENGTH flags = LENGTH rows /\ LIST_REL R rows vs /\
    LIST_REL (\(flag,row) v. flag ==> A row v) (ZIP (flags,rows)) vs ==>
    LIST_REL (\(flag,row) v. flag ==> A row v /\ R row v) (ZIP (flags,rows)) vs
Proof
  Induct >> rpt gen_tac >> Cases_on `rows` >> Cases_on `vs` >> simp[] >>
  rpt strip_tac >> simp[] >> first_x_assum irule >> simp[]
QED

(* Bind the read and the compile witnesses in that order: no raw read, or
   compile-cut choice, is extracted from the valid-horizon quantifier. *)
Theorem log_topic_list_with_row_facts_mods:
  LENGTH flags = LENGTH rows /\
  LIST_REL (\((e,sv),ty) v. ty = lowered_value_type ce e /\
    A e v /\ expr_body_pre_mods mods ce cx env e entry /\
    (!x. vv_operand sv = Var x ==> not_fresh_at front x) /\
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      ?si sm ss vv copy. abi_encode_saved_row_mods lo ce cx origin front
        e sv v si sm ss vv copy H ee G tn s) rows vs /\
  LIST_REL (\(flag,row) v. flag ==> supported_event_leaf_type (SND row))
    (ZIP (flags,rows)) vs /\
  encode_indexed_event_topics flags (MAP SND rows) vs = SOME topics /\
  compile_log_saved_topics ce
    (FST (split_log_ops (MAP (\((e,sv),ty). (sv,ty)) rows) flags)) front = (ops,last) /\
  fn_has_code front last func /\ ~s.vs_halted /\ P front s G tn /\
  local_ptrs_reserved ce front /\ contract_inv mods exps ctx ce cx /\
  expr_sim_inv_mods mods ce cx env ee /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ dead_lo_ok_mods H (DF H) lo ce cx) /\
  (!a u Gu tu H. P a u Gu tu /\ valid_horizon cx st0 H ee.storage_trace ==>
    front.cs_next_id <= a.cs_next_id /\ front.cs_next_var <= a.cs_next_var /\
    wb_frame ce ee ee front s u /\ ghost_kept_at lo ce ee front G tn s Gu tu /\
    s.vs_alloca_next <= u.vs_alloca_next /\ stmt_state_rel H ctx func ce cx ee u /\
    immutable_frame_mods func ce cx ee u /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gu tu u) /\
  (!e sv ty v hashed w a b u Gu tu op. ty = lowered_value_type ce e /\
    hashed = is_bytestring_type ty /\ supported_event_leaf_type ty /\
    encode_event_topic ty v = SOME w /\
    A e v /\ expr_body_pre_mods mods ce cx env e entry /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       ?si sm ss vv copy. abi_encode_saved_row_mods lo ce cx origin a
         e sv v si sm ss vv copy H ee Gu tu u) /\
    P a u Gu tu /\ ~u.vs_halted /\ fn_has_code a b func /\
    compile_log_saved_topics ce [(sv,hashed)] a = ([op],b) ==>
    ?z Gz tz. P b z Gz tz /\ ~z.vs_halted /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
      safe_operand b op /\ eval_operand op z = SOME w /\ op_taint tz op = {} /\
      (!x. not_fresh_at a x ==> lookup_var x z = lookup_var x u /\
        FLOOKUP Gz x = FLOOKUP Gu x /\ op_taint tz (Var x) = op_taint tu (Var x))) ==>
  ?t Gf tf. P last t Gf tf /\ ~t.vs_halted /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    EVERY (safe_operand last) (Lit (n2w hash)::ops) /\
    EVERY (\op. op_taint tf op = {}) (Lit (n2w hash)::ops) /\
    eval_operands (Lit (n2w hash)::ops) t = SOME (n2w hash::topics) /\
    (!x. not_fresh_at front x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    LIST_REL (\((e,sv),ty) v. ty = lowered_value_type ce e /\
      !H. valid_horizon cx st0 H ee.storage_trace ==>
        ?si sm ss vv copy. abi_encode_saved_row_mods lo ce cx origin last
          e sv v si sm ss vv copy H ee Gf tf t)
      (SND (split_log_ops rows flags)) (log_non_indexed_values flags vs)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `R0 = \((e,sv),ty) v. ty = lowered_value_type ce e /\
    A e v /\ expr_body_pre_mods mods ce cx env e entry /\
    (!x. vv_operand sv = Var x ==> not_fresh_at front x) /\
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      ?si sm ss vv copy. abi_encode_saved_row_mods lo ce cx origin front
        e sv v si sm ss vv copy H ee G tn s` >>
  `!a u Gu tu e sv v si sm ss vv copy H.
     P a u Gu tu /\ valid_horizon cx st0 H ee.storage_trace /\
     expr_body_pre_mods mods ce cx env e entry /\
     (!x. vv_operand sv = Var x ==> not_fresh_at front x) /\
     abi_encode_saved_row_mods lo ce cx origin front e sv v si sm ss vv copy
       H ee G tn s ==>
     abi_encode_saved_row_mods lo ce cx origin a e sv v si sm ss vv copy
       H ee Gu tu u` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!a u Gu tu H. P a u Gu tu /\ _ ==> _`
       (drule_all_then strip_assume_tac) >>
     `!l. vv_operand sv <> Label l` by
       (qpat_assum `abi_encode_saved_row_mods _ _ _ _ front _ _ _ _ _ _ _ _ _ _ _ _ _`
          (strip_assume_tac o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
        drule_all_then ACCEPT_TAC log_capture_operand_not_label_mods) >>
     drule_all_then ACCEPT_TAC log_saved_row_advance_mods) >>
  `LIST_REL R0 rows vs` by simp[Abbr `R0`] >>
  qabbrev_tac `RI = \row v. supported_event_leaf_type (SND row) /\ R0 row v` >>
  `LIST_REL (\(flag,row) v. flag ==> RI row v) (ZIP (flags,rows)) vs` by
    (simp[Abbr `RI`] >>
     ho_match_mp_tac log_zip_indexed_and >> simp[]) >>
  `LIST_REL (\(row,hashed) w. ?ty v. hashed = is_bytestring_type ty /\ RI (row,ty) v /\
      encode_event_topic ty v = SOME w) (FST (split_log_ops rows flags)) topics` by
    (mp_tac (ISPEC ``RI:((expr # vyper_value) # type) -> value -> bool``
       (Q.GEN `R` split_log_ops_indexed_rel)) >>
     disch_then (qspecl_then [`flags`,`rows`,`vs`,`topics`] mp_tac) >>
     asm_rewrite_tac[]) >>
  suspend "compose"
QED

Resume log_topic_list_with_row_facts_mods[compose]:
  drule_then (fn th => fs[th]) log_split_saved_projection >>
  qabbrev_tac `R = \(sv,hashed) w. ?e ty v. hashed = is_bytestring_type ty /\
    RI ((e,sv),ty) v /\ encode_event_topic ty v = SOME w` >>
  `LIST_REL R (MAP (\((e,sv),hashed). (sv,hashed)) (FST (split_log_ops rows flags))) topics` by
    (simp[LIST_REL_MAP1] >> irule LIST_REL_mono >>
     qexists_tac `\(row,hashed) w. ?ty v. hashed = is_bytestring_type ty /\
       RI (row,ty) v /\ encode_event_topic ty v = SOME w` >>
     simp[] >> PairCases >> simp[Abbr `R`, combinTheory.o_DEF] >>
     rpt strip_tac >> qexistsl_tac [`x0`, `ty`, `v`] >> simp[]) >>
  mp_tac (Q.INST [`R` |-> `R`] (SPEC_ALL compile_log_saved_topics_run)) >>
  (impl_tac >-
    (qx_gen_tac `row` >> PairCases_on `row` >>
     simp[Abbr `R`, Abbr `RI`, Abbr `R0`] >>
     rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     qpat_x_assum `?e v. _` (qx_choosel_then [`e`,`v`] strip_assume_tac) >>
     qpat_assum `!e sv v w a b u Gu tu op. _` irule >>
     simp[] >> qexistsl_tac [`e`,`row0`,`v`] >> simp[] >>
     reverse conj_tac >- (qpat_assum `row1 <=> _` (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
     gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> ?si sm ss vv copy. _`
       (drule_then (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`copy`] assume_tac)) >>
     qexistsl_tac [`si`,`sm`,`ss`,`vv`,`copy`] >>
     qpat_assum `!a u Gu tu e sv v si sm ss vv copy H. _` irule >> simp[])) >>
  disch_then (drule_all_then strip_assume_tac) >>
  suspend "data"
QED

Resume log_topic_list_with_row_facts_mods[data]:
  drule_then strip_assume_tac log_topic_operand_words >>
  rename1 `P last t Gf tf` >> qexistsl_tac [`t`,`Gf`,`tf`] >>
  simp[safe_operand_def, op_taint_def, eval_operands_def, eval_operand_def] >>
  irule LIST_REL_mono >> irule_at Any split_log_ops_data_rel >>
  qexists_tac `R0` >> simp[Abbr `R0`] >>
  PairCases >> rpt gen_tac >> simp[] >> strip_tac >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?si sm ss vv copy. _`
    (drule_then (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`copy`] assume_tac)) >>
  qexistsl_tac [`si`,`sm`,`ss`,`vv`,`copy`] >>
     qpat_assum `!a u Gu tu e sv v si sm ss vv copy H. _` irule >> simp[]
QED

Finalise log_topic_list_with_row_facts_mods

(* Compatibility: the original callback need not use source row facts. *)
Theorem log_topic_list_mods:
  LENGTH flags = LENGTH rows /\
  LIST_REL (\((e,sv),ty) v. ty = lowered_value_type ce e /\
    expr_body_pre_mods mods ce cx env e entry /\
    (!x. vv_operand sv = Var x ==> not_fresh_at front x) /\
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      ?si sm ss vv copy. abi_encode_saved_row_mods lo ce cx origin front
        e sv v si sm ss vv copy H ee G tn s) rows vs /\
  LIST_REL (\(flag,row) v. flag ==> supported_event_leaf_type (SND row))
    (ZIP (flags,rows)) vs /\
  encode_indexed_event_topics flags (MAP SND rows) vs = SOME topics /\
  compile_log_saved_topics ce
    (FST (split_log_ops (MAP (\((e,sv),ty). (sv,ty)) rows) flags)) front = (ops,last) /\
  fn_has_code front last func /\ ~s.vs_halted /\ P front s G tn /\
  local_ptrs_reserved ce front /\ contract_inv mods exps ctx ce cx /\
  expr_sim_inv_mods mods ce cx env ee /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ dead_lo_ok_mods H (DF H) lo ce cx) /\
  (!a u Gu tu H. P a u Gu tu /\ valid_horizon cx st0 H ee.storage_trace ==>
    front.cs_next_id <= a.cs_next_id /\ front.cs_next_var <= a.cs_next_var /\
    wb_frame ce ee ee front s u /\ ghost_kept_at lo ce ee front G tn s Gu tu /\
    s.vs_alloca_next <= u.vs_alloca_next /\ stmt_state_rel H ctx func ce cx ee u /\
    immutable_frame_mods func ce cx ee u /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gu tu u) /\
  (!e sv ty v hashed w a b u Gu tu op. ty = lowered_value_type ce e /\
    hashed = is_bytestring_type ty /\ supported_event_leaf_type ty /\
    encode_event_topic ty v = SOME w /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       ?si sm ss vv copy. abi_encode_saved_row_mods lo ce cx origin a
         e sv v si sm ss vv copy H ee Gu tu u) /\
    P a u Gu tu /\ ~u.vs_halted /\ fn_has_code a b func /\
    compile_log_saved_topics ce [(sv,hashed)] a = ([op],b) ==>
    ?z Gz tz. P b z Gz tz /\ ~z.vs_halted /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
      safe_operand b op /\ eval_operand op z = SOME w /\ op_taint tz op = {} /\
      (!x. not_fresh_at a x ==> lookup_var x z = lookup_var x u /\
        FLOOKUP Gz x = FLOOKUP Gu x /\ op_taint tz (Var x) = op_taint tu (Var x))) ==>
  ?t Gf tf. P last t Gf tf /\ ~t.vs_halted /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    EVERY (safe_operand last) (Lit (n2w hash)::ops) /\
    EVERY (\op. op_taint tf op = {}) (Lit (n2w hash)::ops) /\
    eval_operands (Lit (n2w hash)::ops) t = SOME (n2w hash::topics) /\
    (!x. not_fresh_at front x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    LIST_REL (\((e,sv),ty) v. ty = lowered_value_type ce e /\
      !H. valid_horizon cx st0 H ee.storage_trace ==>
        ?si sm ss vv copy. abi_encode_saved_row_mods lo ce cx origin last
          e sv v si sm ss vv copy H ee Gf tf t)
      (SND (split_log_ops rows flags)) (log_non_indexed_values flags vs)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  match_mp_tac (BETA_RULE (Q.INST [`A` |-> `\e v. T`]
    (SPEC_ALL log_topic_list_with_row_facts_mods))) >>
  asm_simp_tac bool_ss [] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!e sv ty v hashed w a b u Gu tu op. _` irule >>
  asm_rewrite_tac[] >>
  qexistsl [`e`,`is_bytestring_type (lowered_value_type ce e)`,`sv`,
            `lowered_value_type ce e`,`v`] >> asm_rewrite_tac[]
QED
