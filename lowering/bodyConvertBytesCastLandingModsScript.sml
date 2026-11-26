(* Join the reached non-widening Convert run to its readonly post. *)
Theory bodyConvertBytesCastLandingMods
Ancestors
  bodyConvertBytesSuffixMods bodyConvertBytesCastRunMods bodyConvertBytesCastPostMods
  bodyFullPathHistory bodyMemBopRestWordPath bodyFullPostsMods exprLoweringProps
  freshWrites loweringPosts bodyPtrDefs loweringStateRelDefs venomState
  vyperState vyperAST compileEnv vyperStorageFootprint exprSimDefs context

local
  val eout = ``TypeBuiltin dst Convert dst [e]``
  val vvout = ``LocatedValue dst (mk_ptr out LocMemory)``
in
  val cast_post =
    ``\H (res : eval_result + vyperState$exception) ee G tn t. ?tv. res = INL tv /\
        vv_post_mods H ctx func ce cx ^eout es sa sb s0 ee tv ^vvout t /\
        vv_store_bound cx (post_value_type ce ^eout) (lowered_value_type ce ^eout)
          ee tv ^vvout t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at_mods (DF (H : (bool # 256 word # type_value) list # num list))
          lo d ce cx ee G tn t /\
        ptr_vv_ok cx (post_value_type ce ^eout) tv ^vvout ee G tn t /\
        (!v. tv = Value v /\ ~is_word_type (post_value_type ce ^eout) /\
             ~is_bytestring_type (post_value_type ce ^eout) ==>
             vv_own ce cx (post_value_type ce ^eout) sa sb ee tv ^vvout t /\
             (!t' p. ^vvout = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
        (ce.ce_is_ctor /\ vv_location ^vvout = SOME LocCode ==>
         ?val. read_result cx tv ee = (INL val, ee) /\
               !rt w. evaluate_type (get_tenv cx) (post_value_type ce ^eout) = SOME rt /\
                      eval_operand (vv_operand ^vvout) t = SOME w ==>
                      w2n w + type_memory_size rt <= lo /\
                      (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                        val_in_memory rt val (w2n w) mem)) /\
        (!t' op. ^vvout = StackValue t' op /\ ~is_word_type (post_value_type ce ^eout) ==>
                 ptr_buf_ok ce ^eout op G t) /\
        (!t' p. ^vvout = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
                ptr_buf_ok ce ^eout p.ptr_operand G t) /\
        ghost_kept_at lo ce es sa G0 tn0 s0 G tn``
end

Theorem bytes_convert_cast_landing_mods:
  is_bytestring_type (expr_type e) /\ is_bytestring_type dst /\
  type_alloc_ok ce (expr_type e) /\ type_alloc_ok ce dst /\
  evaluate_type (get_tenv cx) dst = SOME tout /\
  type_memory_bytes ce dst = type_memory_size tout /\
  type_memory_bytes ce dst <= type_memory_bytes ce (lowered_value_type ce e) /\
  compile_type_convert op (mk_convert_op (expr_type e) dst) sm = (out,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\
  sm.cs_next_id <= sb.cs_next_id /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  ~t.vs_halted /\ mid.gas_obs = [] /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    ?pt rt w.
      expr_post_mods H ctx func ce cx e es sa sm s0 mid v op t /\
      storage_well_formed_on cx mid (FST H) /\
      expr_store_bound cx (post_value_type ce e) v op t /\
      t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d ce cx mid G tn t /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
      ptr_val_ok cx (post_value_type ce e) v op G tn t /\ ptr_buf_ok ce e op G t /\
      ~is_word_type (post_value_type ce e) /\
      evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
      type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
      value_has_type pt v /\ value_has_type rt v /\ val_wf rt v /\
      eval_operand op t = SOME w /\ op_taint tn op = {} /\
      (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
        val_in_memory rt v (w2n w) mem) /\
      (type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= t.vs_alloca_next) /\
      w2n w + type_memory_size rt < dimword (:256) /\
      (0 < type_memory_size rt ==>
        ?x. op = Var x /\ not_fresh_at sm x /\ ptr_covers G tn x t (type_memory_size rt))) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) ce.ce_modules cx st0
    (\ee. (sum_CASE (convert_result cx (expr_type e) dst v) (\w. INL (Value w)) INR,ee))
    (mid,t,G,tn) ^cast_post
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule bytes_convert_suffix_continuation_mods >> simp[] >>
  strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (qx_choosel_then [`pt`,`rt`,`w`] (map_every assume_tac o CONJUNCTS))) >>
  `post_value_type ce e = expr_type e` by simp[] >>
  qpat_assum `compile_type_convert _ _ _ = _`
    (mp_then Any mp_tac bytes_convert_cast_run_mods) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  disch_then (fn rule =>
    qpat_assum `evaluate_type _ (post_value_type _ _) = _`
      (mp_then (Pat `evaluate_type _ (post_value_type _ _) = _`) mp_tac rule)) >>
  disch_then (qspecl_then [`v`,`func`,`explicit`,`ctx`,`PG`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (DISJ_CASES_THEN2
      (qx_choosel_then [`vout`,`src`,`q`,`Gf`,`tnf`] (map_every assume_tac o CONJUNCTS))
      (qx_choosel_then [`msg`,`q`,`Gf`,`tnf`] (map_every assume_tac o CONJUNCTS))))
  >- suspend "normal" >>
  disj2_tac >> qexistsl_tac [`msg`,`q`,`Gf`,`tnf`] >> asm_rewrite_tac[]
QED

Resume bytes_convert_cast_landing_mods[normal]:
  qpat_x_assum `op = Var _` SUBST_ALL_TAC >>
  disj1_tac >> qexistsl_tac [`vout`,`q`,`Gf`,`tnf`] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  `alloca_inv t` by
    (qpat_assum `expr_post_mods H0 _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
     drule_then (ACCEPT_TAC o MATCH_MP rest_word_state_alloca_inv)
       exprSimWordArgsTheory.expr_post_state) >>
  `alloca_history func q` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ (OK q,_,_)`
       (qspec_then `DF H0` (mp_then Any mp_tac body_full_path_alloca_history)) >>
     asm_rewrite_tac[]) >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `expr_post_mods H0 _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `ghost_inv_at_mods (DF H0) _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `storage_well_formed_on _ _ (FST H0)` kall_tac >>
  qpat_x_assum `valid_horizon _ _ H0 _` kall_tac >>
  `type_memory_size tout <= type_memory_size rt` by
    (qpat_assum `type_memory_bytes ce dst = type_memory_size tout`
       (once_rewrite_tac o single o SYM) >>
     qpat_assum `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt`
       (once_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME pt` by
    (qpat_assum `post_value_type ce e = expr_type e`
       (once_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     expr_post_mods H ctx func ce cx e es sa sm s0 mid v (Var src) t /\
     storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at_mods (DF H) lo d ce cx mid G tn t` by
    (gen_tac >> strip_tac >>
     first_x_assum (drule_then (qx_choosel_then [`pt'`,`rt'`,`w'`]
       (map_every assume_tac o CONJUNCTS))) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all_then mp_tac bytes_convert_cast_post_mods >>
  simp[expr_type_def, exprLoweringTheory.lowered_value_type_def,
       vv_location_def, mk_ptr_def]
QED

Finalise bytes_convert_cast_landing_mods
