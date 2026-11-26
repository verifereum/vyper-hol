(* The scalar store consumes the one prepared word and its silent unwrap
   path, starting the outcome at the reached target rather than after it. *)
Theory bodyQualifiedAssignSlotWordLandingMods
Ancestors
  bodyQualifiedAssignOperandCutMods bodyQualifiedPlaceSlotScalarMods
  vyperFiniteStoragePreservation bodyAssignQualifiedStageJoinMods
  bodyWriteTargetStageMods bodyFullTargetDefs loweringPosts compileEnv

Theorem qualified_assign_slot_word_landing_mods:
  qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
    mid sr st dst u Gu tu marks p ee Gz tz z /\
  qualified_assign_route_mods AssignSlotWord key p (SOME vv) dty dst /\
  qualified_assign_operand_cut_mods (DF,lo,d,explicit,ctx,func,PG)
    cenv cx st0 (bt,e,dty) (vv,op,p,dst,v) (sa,st,su,sb)
    (es,s0,G0,tn0) (ee,z,Gz,tz) (s,G,tn) /\
  assign_place_store_code_mods cenv e (SOME vv) dst st = ((),sb) /\
  type_widens_to tenv (expr_type e) dty /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (write_place cx p v) (ee,z,Gz,tz)
    (\H res ef Gf tf t. ?ce.
       stmt_lands lctx sb res t /\ ~t.vs_halted /\
       (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
       cenv_top_ext cenv ce ef.scopes /\ stmt_state_rel H ctx func ce cx ef t /\
       immutable_frame_mods func ce cx ef t /\ storage_well_formed_on cx ef (FST H) /\
       return_buf_frame d ce sb t /\ alloca_history func t /\ return_buf_sep d ce ef t /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
       ghost_inv_at_mods (DF H) lo d ce cx ef Gf tf t /\
       (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
       (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
       (!x. not_fresh_at sa x ==>
         FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
       alloca_frame cenv es sa s0 ce ef t /\
       (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
         (!n b len. local_region cenv es.scopes s0 n b len ==> off + sz <= b \/ b + len <= off) /\
         off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tn0.t_mem))
    (assign_qualified_exit_mods ctx cx RetQ)
Proof
  PairCases_on `key` >> Cases_on `p` >> simp[qualified_assign_route_mods_def] >>
  rename1 `write_place cx (StoragePlace tr dw dtv) v` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_type e = dty` by metis_tac[type_widens_to_word] >>
  qhdtm_x_assum `qualified_assign_target_reached_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (qspec_then `[]` (mp_tac o MATCH_MP eval_target_place_observed_region)) >>
  simp[NoAsms] >> strip_tac >>
  qhdtm_x_assum `qualified_assign_operand_cut_mods`
    (mp_tac o REWRITE_RULE [qualified_assign_operand_cut_mods_def]) >>
  simp[Excl "AND_IMP_INTRO",write_target_location_mods_def,place_ptr_rel_def,target_ptr_ok_def] >>
  strip_tac >>
  `assign_place_store_code_mods cenv e (SOME vv)
      (FST dst,SOME (slot_loc tr),SOME (ValPT dty)) st = ((),sb)` by
    (qpat_assum `dst = _` (once_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
  Cases_on `write_place cx (StoragePlace tr (n2w offset + n2w delta) dtv) v ee` >>
  irule qualified_place_slot_word_mods >>
  qpat_assum `assign_place_store_code_mods _ _ _ (FST dst,_,_) _ = _` (irule_at Any) >>
  qpat_assum `unwrap_value _ _ _ = _` (irule_at Any) >>
  qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `storage_subregion _ _ _ dtv` (irule_at Any) >>
  qexistsl_tac [`tn`,`s`,`offset`,`G`] >>
  `rt = dtv` by metis_tac[optionTheory.SOME_11] >>
  fs[wb_frame_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED
