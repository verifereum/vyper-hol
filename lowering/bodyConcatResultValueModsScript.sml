(* The located Concat result after the logical length has been stored. *)
Theory bodyConcatResultValueMods
Ancestors
  bodyConcatResultShapeMods bodyConcatResultEncodingMods
  bodyFullPostsMods exprSimHash exprSimProps exprSimMemDefs
  reasonCodeResourcesPtr bodyPtrAttributeFields bodyPtrDefs rawCallBufferPtr
  typeLayoutProps compileEnv exprLowering loweringPosts context
  vyperInterpreter vyperAST vyperState venomState words arithmetic

Triviality concat_store_bound:
  (a = BaseT (BytesT (Dynamic n)) \/ a = BaseT (StringT n)) /\
  evaluate_type (get_tenv cx) a = SOME tv /\ val_store_size tv v <= bsz /\
  type_memory_bytes cenv (lowered_value_type cenv (Builtin a (Concat n) args)) <= bsz /\
  w2n w + bsz <= t.vs_alloca_next /\ lookup_var bv t = SOME w /\
  buf.buf_operand = Var bv ==>
  vv_store_bound cx a (lowered_value_type cenv (Builtin a (Concat n) args)) ee
    (Value v) (LocatedValue a (base_ptr buf)) t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[vv_store_bound_def,base_ptr_def,eval_operand_def,read_result_def,return_def] >>
  qpat_x_assum `_ \/ _` strip_assume_tac >>
  gvs[lowered_value_type_def,concat_buffer_type_def] >>
  rpt strip_tac >>
  drule type_memory_bytes_base_evaluated >>
  disch_then (qspec_then `cenv` assume_tac) >> decide_tac
QED

Theorem concat_result_value_mods:
  let e = Builtin a (Concat n) args;
      vv = LocatedValue a (base_ptr buf)
  in
  2 <= LENGTH args /\ SUM (MAP bytelike_type_bound (MAP expr_type args)) <= n /\
  ((a = BaseT (BytesT (Dynamic n)) /\
    EVERY (\ty. ?bd. ty = BaseT (BytesT bd)) (MAP expr_type args)) \/
   (a = BaseT (StringT n) /\
    EVERY (\ty. ?m. ty = BaseT (StringT m)) (MAP expr_type args))) /\
  LIST_REL (\arg v. ?tv. evaluate_type (get_tenv cx) (expr_type arg) = SOME tv /\
                        value_has_type tv v) args vs /\
  evaluate_type (get_tenv cx) a = SOME tv /\
  p = FLAT (MAP concat_payload_mods vs) /\ bsz = concat_alloc_size (MAP expr_type args) /\
  B + bsz < dimword (:256) /\ B + bsz <= t.vs_alloca_next /\
  buf.buf_operand = Var bv /\ lookup_var bv t = SOME (n2w B) /\
  ptr_covers G tn bv t bsz /\ FLOOKUP t.vs_allocas aid = SOME (B,bsz) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  mload B t = n2w (LENGTH p) /\ mem_bytes_at (B+32) (LENGTH p) t.vs_memory = p /\
  (!i. B <= i /\ i < B+32+LENGTH p ==> i NOTIN tn.t_mem) /\
  (!name b sz. local_region cenv ee.scopes t name b sz ==> B+bsz <= b \/ b+sz <= B) /\
  wb_frame cenv es ee sa s0 t /\ (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
  immutable_frame_mods func cenv cx ee t /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H)) ==>
  ?v. evaluate_concat n vs = INL v /\ ~is_word_type a /\ val_wf tv v /\
      val_footprint tv v = 32 + LENGTH p /\ val_in_memory tv v B t.vs_memory /\
      val_store_size tv v <= bsz /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        vv_post_mods H ctx func cenv cx e es sa sb s0 ee (Value v) vv t) /\
      vv_store_bound cx a (lowered_value_type cenv e) ee (Value v) vv t /\
      ptr_vv_ok cx a (Value v) vv ee G tn t /\ ptr_buf_ok cenv e (Var bv) G t /\
      (!x. Value v = Value x /\ ~is_word_type a /\ ~is_bytestring_type a ==>
        vv_own cenv cx a sa sb ee (Value v) vv t /\
        (!ty q. vv = LocatedValue ty q ==> q.ptr_location = LocMemory))
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac concat_result_shape_mods >>
  `concat_payload_mods v = p` by metis_tac[] >>
  drule_all_then (qspec_then `cenv` (map_every assume_tac o CONJUNCTS)) concat_result_encoding_mods >>
  `w2n (n2w B : bytes32) = B` by (`B < dimword (:256)` by decide_tac >> simp[]) >>
  Q.SUBGOAL_THEN `a = BaseT (BytesT (Dynamic n)) \/ a = BaseT (StringT n)` assume_tac
  >- metis_tac[] >>
  qexists_tac `v` >>
  ntac 6 (conj_tac >- (first_assum ACCEPT_TAC ORELSE simp[])) >>
  conj_tac >- suspend "post" >>
  conj_tac >- (irule concat_store_bound >> simp[] >> qexists_tac `bsz` >> simp[]) >>
  conj_tac >- suspend "pointer" >>
  conj_tac >- (irule ptr_buf_ok_from_covers >> qexistsl_tac [`bsz`,`tn`] >> simp[]) >>
  `is_bytestring_type a` by (qpat_x_assum `a = _ \/ a = _` strip_assume_tac >> simp[is_bytestring_type_def]) >>
  simp[]
QED

Resume concat_result_value_mods[post]:
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `val_footprint tv v <= bsz` by
    (irule LESS_EQ_TRANS >> qexists_tac `val_store_size tv v` >>
     simp[val_footprint_le_store_size]) >>
  `vv_post H ctx func cenv cx (Builtin a (Concat n) args) es sa sb s0 ee
      (Value v) (LocatedValue a (base_ptr buf)) t` by
    (irule (REWRITE_RULE [expr_type_def]
       (Q.INST [`e` |-> `Builtin a (Concat n) args`] vv_post_allocated_memory_intro)) >>
     simp[expr_type_def,base_ptr_def,eval_operand_def] >>
     qexistsl_tac [`aid`,`B`,`bsz`] >>
     qpat_x_assum `bsz = _` SUBST_ALL_TAC >>
     qpat_x_assum `p = FLAT _` SUBST_ALL_TAC >>
     simp[] >> first_assum ACCEPT_TAC) >>
  pop_assum mp_tac >>
  simp[vv_post_def,vv_post_mods_def,vv_holds_mods_def,vv_place_ptr_mods_def,base_ptr_def] >>
  strip_tac >> first_assum ACCEPT_TAC
QED

Resume concat_result_value_mods[pointer]:
  `ptr_mem_ok cx a v (Var bv) G tn t` by
    (irule clean_memory_representation_ptr >> qexistsl_tac [`n2w B`,`bsz`,`tv`] >>
     qpat_assum `w2n (n2w B : bytes32) = B` (pure_rewrite_tac o single) >>
     conj_tac
     >- (gen_tac >> strip_tac >> qpat_assum `!i. B <= i /\ _ ==> _` irule >> decide_tac) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule ptr_vv_ok_memory >> simp[base_ptr_def,read_result_def,return_def] >>
  qpat_assum `ptr_covers _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
  first_assum ACCEPT_TAC
QED

Finalise concat_result_value_mods
