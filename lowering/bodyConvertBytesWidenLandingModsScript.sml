(* Widen a reached bytestring using the actual registered copy destination. *)
Theory bodyConvertBytesWidenLandingMods
Ancestors
  bodyConvertBytesWidenRunMods bodyConvertBytesWidenPostMods
  bodyCopyReadPhysicalTypeMods abiBufferAllocationCode exprSimBufferStore
  allocationPtr emitHelperProps exprSimWordArgs valueCopyBytes allocLimits
  vyperStorageFootprint vyperState words finite_map venomState loweringHalt
  venomExecSemantics fragExec exprLoweringProps bodyFullPostsMods exprBodyPreProps
  bodyFullShadowBodyInv loweringPosts compileEnv context vyperAST

Theorem widen_alloc_map[local]:
  stmt_state_rel H ctx func ce cx mid t /\ cap < dimword (:256) /\
  MEM (mk_inst id ALLOCA [Lit (n2w cap)] [dstvar]) (fn_insts func) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w cap)] [dstvar]) t = OK r /\
  z = r with vs_inst_idx := idx ==>
  !aid b n. FLOOKUP z.vs_allocas aid = SOME (b,n) ==>
    FLOOKUP t.vs_allocas aid = SOME (b,n) \/ t.vs_alloca_next <= b
Proof
  strip_tac >> Cases_on `FLOOKUP t.vs_allocas id` >-
   (drule_all step_alloca_fresh >> disch_then (qspec_then `dstvar` assume_tac) >>
    qpat_x_assum `step_inst_base _ _ = OK r` mp_tac >>
    simp[] >> disch_then (SUBST_ALL_TAC o SYM) >>
    simp[update_var_def,FLOOKUP_UPDATE] >> rpt gen_tac >>
    IF_CASES_TAC >> simp[]) >>
  rename1 `FLOOKUP t.vs_allocas id = SOME p` >> PairCases_on `p` >>
  drule_all stmt_state_rel_alloca_site_bound >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac) >>
  drule reused_alloca_step >> disch_then (qspec_then `dstvar` assume_tac) >>
  qpat_x_assum `step_inst_base _ _ = OK r` mp_tac >> simp[] >>
  disch_then (SUBST_ALL_TAC o SYM) >> simp[update_var_def]
QED

Theorem widen_copy_same_endpoint[local]:
  compile_alloc_buffer cap sm = (buf,sc) /\
  emit_void MCOPY [Var dst;Var src;Lit (n2w k)] sc = ((),sb) /\
  k < dimword(:256) /\
  run_inst_seq (emitted_insts sm sb) t = OK u /\
  run_inst_seq (emitted_insts sm sc) t = OK r /\
  z = r with vs_inst_idx := LENGTH sc.cs_current_insts /\
  lookup_var dst z = SOME dw /\ lookup_var src z = SOME a /\
  q = u with vs_inst_idx := LENGTH sb.cs_current_insts ==>
  q = (mcopy (w2n dw) (w2n a) k z) with vs_inst_idx := LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule compile_alloc_buffer_code >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `emitted_insts sm sb = emitted_insts sm sc ++ emitted_insts sc sb` by
    (irule emitted_insts_append >> asm_rewrite_tac[]) >>
  `lookup_var dst r = SOME dw /\ lookup_var src r = SOME a` by
    (qpat_assum `lookup_var dst z = _` mp_tac >> qpat_assum `lookup_var src z = _` mp_tac >>
     simp[lookup_var_def, NoAsms, SimpLHS] >>
     qpat_assum `z = r with vs_inst_idx := _` SUBST1_TAC >>
     simp[lookup_var_def]) >>
  `run_inst_seq (emitted_insts sc sb) r = OK (mcopy (w2n dw) (w2n a) k r)` by
    (qpat_assum `emit_void MCOPY _ _ = _`
       (mp_then Any (qspecl_then [`dw`,`a`,`n2w k`,`r`] mp_tac) buffer_emit_mcopy_run) >>
     simp[eval_operand_def,w2n_n2w]) >>
  `u = mcopy (w2n dw) (w2n a) k r` by
    (qpat_assum `run_inst_seq (emitted_insts sm sc) t = OK r`
      (mp_then Any (qspec_then `emitted_insts sc sb` mp_tac) run_inst_seq_append) >>
     qpat_assum `emitted_insts sm sb = _ ++ _` (once_rewrite_tac o single o GSYM) >>
     simp[]) >>
  simp[mcopy_def,write_memory_with_expansion_def]
QED

local
  val eout = ``TypeBuiltin dst Convert dst [e]``
  val vvout = ``LocatedValue dst (mk_ptr out LocMemory)``
in
  val widen_post =
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

Theorem bytes_convert_widen_landing_mods:
  is_bytestring_type (expr_type e) /\ is_bytestring_type dst /\
  expr_body_pre_mods mods ce cx env e es /\ type_alloc_ok ce dst /\
  evaluate_type (get_tenv cx) dst = SOME tout /\
  type_memory_bytes ce dst = type_memory_size tout /\
  type_memory_bytes ce (lowered_value_type ce e) < type_memory_bytes ce dst /\
  compile_bytestring_widen_copy (type_memory_bytes ce dst) op
    (type_memory_bytes ce (lowered_value_type ce e)) sm = (out,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid) /\
  ~t.vs_halted /\ mid.gas_obs = [] /\
  valid_horizon cx st0 H0 mid.storage_trace /\
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
        ?x. op = Var x /\ not_fresh_at sm x /\ ptr_covers G tn x t (type_memory_size rt))) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s0 /\ immutable_frame_mods func ce cx es s0 /\
     storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G0 tn0 s0) ==>
  ?vout q Gf tnf. convert_result cx (expr_type e) dst v = INL vout /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK q,Gf,tnf)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      (^widen_post) H (INL (Value vout)) mid Gf tnf q)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?pt rt w. _`
    (drule_then (qx_choosel_then [`pt`,`rt`,`a`] (map_every assume_tac o CONJUNCTS))) >>
  `is_bytestring_type (lowered_value_type ce e)` by
    (irule compileEnvTheory.arg_type_fits_bytestring_source >>
     qexists_tac `expr_type e` >> simp[] >>
     irule copy_lowered_fits_mods >>
     drule expr_body_pre_mods_inv >> disch_then (irule_at Any) >>
     drule expr_body_pre_mods_well_typed >> simp[]) >>
  `0 < type_memory_bytes ce (lowered_value_type ce e)` by
    simp[bytestring_memory_bytes_positive] >>
  `0 < type_memory_size rt` by metis_tac[] >>
  qpat_assum `0 < type_memory_size rt ==> _`
    (drule_then (qx_choose_then `src` (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `op = Var src` SUBST_ALL_TAC >>
  suspend "run"
QED

Resume bytes_convert_widen_landing_mods[run]:
  `type_memory_bytes ce dst < dimword (:256)` by
    (`~is_word_type dst` by simp[is_bytestring_word_type] >>
     `type_memory_bytes ce dst < 2 ** 64` by fs[type_alloc_ok_def] >>
     irule arithmeticTheory.LESS_TRANS >> qexists_tac `2 ** 64` >> simp[dimword_def]) >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME pt` by
    (`post_value_type ce e = expr_type e` by
       (irule post_value_type_bytestring >> first_assum ACCEPT_TAC) >>
     qpat_assum `post_value_type ce e = expr_type e`
       (once_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
  `val_footprint pt v <= type_memory_bytes ce (lowered_value_type ce e)` by
    (qpat_assum `type_memory_bytes ce (lowered_value_type ce e) = _` SUBST1_TAC >>
     irule bytestring_val_footprint_le >>
     reverse conj_tac >- simp[] >>
     qexistsl_tac [`expr_type e`,`lowered_value_type ce e`,`get_tenv cx`] >> simp[]) >>
  `lookup_var src t = SOME a` by fs[eval_operand_def] >>
  `w2n a + type_memory_bytes ce (lowered_value_type ce e) <= t.vs_alloca_next` by
    (qpat_assum `type_memory_size rt = 0 \/ _` mp_tac >> simp[]) >>
  `ptr_covers G tn src t (type_memory_bytes ce (lowered_value_type ce e))` by simp[] >>
  `stmt_state_rel H0 ctx func ce cx mid t` by
    (qpat_assum `expr_post_mods H0 _ _ _ _ _ _ _ _ _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
     drule_then ACCEPT_TAC expr_post_state) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods (DF H0) _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     simp[]) >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  drule_all (Q.INST [`s` |-> `t`, `es` |-> `mid`, `H` |-> `H0`]
      (INST_TYPE [``:'b`` |-> ``:256``] bytes_convert_widen_run_mods)) >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  disch_then (qx_choose_then `vout`
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac
        (qx_choosel_then [`u`,`q`,`Gf`,`tnf`,`dstvar`,`dw`,`z`,`Ga`,`tna`,`sc`,`buf`,`r`]
           (map_every assume_tac o CONJUNCTS)))))) >>
  qpat_x_assum `out = Var dstvar` SUBST_ALL_TAC >>
  suspend "endpoint"
QED
Resume bytes_convert_widen_landing_mods[endpoint]:
  qabbrev_tac `k = type_memory_bytes ce (lowered_value_type ce e)` >>
  qabbrev_tac `cap = type_memory_bytes ce dst` >>
  `fn_has_code sm sc func` by
    (drule_all exprSimConvertBytesTheory.convert_widen_copy_code >>
     disch_then (qx_choosel_then [`buf1`,`sc1`,`i`,`p`] (map_every assume_tac o CONJUNCTS)) >>
     `sc1 = sc` by metis_tac [pairTheory.PAIR_EQ] >>
     fs[]) >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w cap)] [dstvar]) (fn_insts func) /\
   step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w cap)] [dstvar]) t = OK r` by
    (drule compile_alloc_buffer_code >> strip_tac >>
     `dstvar = STRING #"%" (toString sm.cs_next_var)` by metis_tac[operand_11] >>
     conj_tac
     >- (drule_all exprSimAllocTheory.buffer_alloc_code >> simp[]) >>
     qpat_x_assum `run_inst_seq (emitted_insts sm sc) t = OK r` mp_tac >>
     simp[run_inst_seq_def,AllCaseEqs()]) >>
  `!aid b n. FLOOKUP z.vs_allocas aid = SOME (b,n) ==>
      FLOOKUP t.vs_allocas aid = SOME (b,n) \/ t.vs_alloca_next <= b` by
    (qpat_x_assum `FLOOKUP z.vs_allocas sm.cs_next_id = _` kall_tac >>
     rpt gen_tac >> disch_tac >>
     drule_all (Q.INST [`H` |-> `H0`] widen_alloc_map) >>
     disch_then ACCEPT_TAC) >>
  `lookup_var src z = SOME a` by
    (qpat_assum `!x. not_fresh_at sm x ==> lookup_var x z = _ /\ _`
       (qspec_then `src` mp_tac) >> simp[]) >>
  `k < dimword (:256)` by
    (irule arithmeticTheory.LESS_TRANS >> qexists_tac `cap` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `q = (mcopy (w2n dw) (w2n a) k z) with vs_inst_idx := LENGTH sb.cs_current_insts` by
    (drule_all widen_copy_same_endpoint >> simp[]) >>
  suspend "post"
QED

Resume bytes_convert_widen_landing_mods[post]:
  `!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
       val_in_memory tout vout (w2n a) m` by
    (gen_tac >> strip_tac >>
     `val_in_memory rt v (w2n a) m` by (first_x_assum drule >> simp[]) >>
     `val_in_memory pt v (w2n a) m` by
       (irule bytestring_val_in_memory_transfer >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qexistsl_tac [`lowered_value_type ce e`,`expr_type e`,`get_tenv cx`,`rt`] >> simp[]) >>
     drule_all exprSimConvertBytesTheory.convert_bytestring_memory >>
     disch_then (qspecl_then [`w2n a`,`m`] mp_tac) >> simp[]) >>
  qexistsl_tac [`vout`,`q`,`Gf`,`tnf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?pt rt w. _`
    (drule_then (qx_choosel_then [`ptH`,`rtH`,`wH`] (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `stmt_state_rel H ctx func ce cx mid z` by
    (qpat_assum `expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
     drule_then assume_tac expr_post_state >>
     qpat_assum `!h. stmt_state_rel h _ _ _ _ _ _ ==> stmt_state_rel h _ _ _ _ _ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `type_memory_bytes ce dst = cap` by simp[Abbr `cap`] >>
  `type_memory_size tout = cap` by simp[] >>
  `post_value_type ce (TypeBuiltin dst Convert dst [e]) = dst /\
   lowered_value_type ce (TypeBuiltin dst Convert dst [e]) = dst` by
    simp[post_value_type_def,expr_type_def,exprLoweringTheory.lowered_value_type_def] >>
  qpat_assum `post_value_type ce (TypeBuiltin dst Convert dst [e]) = dst`
    (pure_rewrite_tac o single) >>
  qpat_assum `lowered_value_type ce (TypeBuiltin dst Convert dst [e]) = dst`
    (pure_rewrite_tac o single) >> BETA_TAC >>
  irule (BETA_RULE (Q.INST [`D` |-> `DF H`, `iid` |-> `sc.cs_next_id`]
           (INST_TYPE [``:'a`` |-> ``:256``] bytes_convert_widen_post_mods))) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G`,`Ga`,`PG`,`a`,`cap`,`dw`,
                `mk_inst sm.cs_next_id ALLOCA [Lit (n2w cap)] [dstvar]`,
                `k`,`tout`,`sc`,`sm`,`src`,`t`,`tn`,`tna`,`u`,`v`,`z`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[NoAsms,venomInstTheory.mk_inst_def])
QED

Finalise bytes_convert_widen_landing_mods
