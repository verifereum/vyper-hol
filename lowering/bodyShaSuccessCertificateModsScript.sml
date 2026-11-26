(* The all-tail source result and counted normal SHA256 suffix. *)
Theory bodyShaSuccessCertificateMods
Ancestors
  bodyShaSuccessLandingFrameMods bodyShaSuccessStackPostMods
  bodyPtrHashBuiltinsShaSource bodyFullHashCleanFrame bodyFullHashKeccakFixed
  exprSimWordArgs exprSimVVFrame fragGasSeqPtr allocaHistoryFragment
  entrySinkExtraction vyperStorageFootprint rich_list
  bodyFullPostsMods bodyInvSplit loweringStateRelDefs loweringPosts
  exprLoweringProps venomState bodyFullShadowBodyInv bodyPtrDefs
  exprSimHash vyperCallOutcomeProps vyperState vyperAST compileEnv
  exprSimMemDefs ptrDiscipline vyperInterpreter builtinHashing vyperValue
  list pred_set finite_map fragExec unitTransformDefs

Theorem sha_linked_immutable_pc[local]:
  immutable_frame_mods func cenv cx es (s with vs_inst_idx := j) <=>
  immutable_frame_mods func cenv cx es s
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def, immutables_rel_def,
       immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
       local_region_def, lookup_var_def]
QED

Theorem sha_linked_stack_post[local]:
  vv_post_mods H ctx func cenv cx e es sa sb s0 ef (Value w) (StackValue ty op) z <=>
  immutable_frame_mods func cenv cx ef z /\
  vv_post H ctx func cenv cx e es sa sb s0 ef (Value w) (StackValue ty op) z
Proof
  simp[vv_post_mods_def, vv_post_def, vv_holds_mods_def,
       vv_place_ptr_mods_def, vv_place_ptr_def, AC CONJ_ASSOC CONJ_COMM]
QED

Theorem sha_success_certificate_mods:
  storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x s /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s) /\
  (?J. stmt_state_rel J ctx func cenv cx es s0) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  (if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
   else case expr_type e of
     BaseT (BytesT (Fixed m)) => compile_sha256_bytesm x m sm
   | _ => compile_sha256_word x sm) = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  s.vs_outcomes = outcome::rest /\ outcome.co_success /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  same_blocks sm sb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  LENGTH (emitted_insts sm sb) = 7 /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sb) /\
  MAP (\i. (func.fn_name,i.inst_id) IN explicit)
    (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb)) = [F] /\
  run_inst_seq_mem_ok (emitted_insts sm sb) s /\
  (ctx_has_dalloca ctx ==>
    !pre i post u. emitted_insts sm sb = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
                   dalloca_no_wrap i u) /\
  run_inst_seq (emitted_insts sm sb) s = OK z /\
  ghost_kept_at 0 cenv mid sm G tn s Gf tf /\
  (!p. not_fresh_at sm p ==> lookup_var p z = lookup_var p s) /\
  pure_frame cenv func mid sm s z /\
  op_taint tf op = {} /\ op_prov Gf op = NONE /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sm sb) s Gf tf /\
    ghost_inv_at (DF H) 0 d cenv cx (mid with outcomes := SOME rest) Gf tf
      (z with vs_inst_idx := s.vs_inst_idx + 7)) ==>
  let ef = SND (take_call_outcome NONE 2w (precompile_input Sha256 [v]) NONE mid);
      t = z with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb) in
  ?w.
    (!tail.
      (case builtin_result cx (mid with gas_obs := tail).accounts
              (BaseT (BytesT (Fixed 32))) Sha256 [expr_type e] [v] of
         INR exc => (INR exc,mid with gas_obs := tail)
       | INL r => (do precompile_call_success Sha256 [v]; return (Value r) od)
                    (mid with gas_obs := tail)) =
      (INL (Value w),ef with gas_obs := tail)) /\
    storage_trace_domain cx st0 ef.storage_trace /\
    !H. valid_horizon cx st0 H ef.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [F] (OK t,Gf,tf) /\
      (\H res ee G tn t. ?tv. res = INL tv /\
        vv_post_mods H ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
          es sa sb s0 ee tv (StackValue (BaseT (BytesT (Fixed 32))) op) t /\
        vv_store_bound cx
          (post_value_type cenv (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e]))
          (lowered_value_type cenv (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e]))
          ee tv (StackValue (BaseT (BytesT (Fixed 32))) op) t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
        ptr_vv_ok cx (post_value_type cenv (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e]))
          tv (StackValue (BaseT (BytesT (Fixed 32))) op) ee G tn t /\
        (!v. tv = Value v /\
             ~is_word_type (post_value_type cenv (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])) /\
             ~is_bytestring_type (post_value_type cenv (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])) ==>
             vv_own cenv cx (post_value_type cenv (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e]))
               sa sb ee tv (StackValue (BaseT (BytesT (Fixed 32))) op) t /\
             (!t' p. StackValue (BaseT (BytesT (Fixed 32))) op = LocatedValue t' p ==>
                     p.ptr_location = LocMemory)) /\
        (cenv.ce_is_ctor /\ vv_location (StackValue (BaseT (BytesT (Fixed 32))) op) = SOME LocCode ==>
         ?value. read_result cx tv ee = (INL value,ee) /\
                 !rt w. evaluate_type (get_tenv cx)
                          (post_value_type cenv (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])) = SOME rt /\
                        eval_operand (vv_operand (StackValue (BaseT (BytesT (Fixed 32))) op)) t = SOME w ==>
                        w2n w + type_memory_size rt <= lo /\
                        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                               val_in_memory rt value (w2n w) mem)) /\
        (!t' operand. StackValue (BaseT (BytesT (Fixed 32))) op = StackValue t' operand /\
                      ~is_word_type (post_value_type cenv (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])) ==>
                      ptr_buf_ok cenv (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e]) operand G t) /\
        (!t' p. StackValue (BaseT (BytesT (Fixed 32))) op = LocatedValue t' p /\
                p.ptr_location = LocMemory ==>
                ptr_buf_ok cenv (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e]) p.ptr_operand G t) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        H (INL (Value w)) (ef with gas_obs := []) Gf tf t
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  qabbrev_tac `ef = SND (take_call_outcome NONE 2w (precompile_input Sha256 [v]) NONE mid)` >>
  qabbrev_tac `Jm = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 Jm mid.storage_trace` by fs[Abbr `Jm`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `Jm` (drule_then (strip_assume_tac o REWRITE_RULE[expr_post_mods_def]))) >>
  drule_then strip_assume_tac (cj 2 compile_expr_grows) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  drule_all_then (qx_choose_then `u`
    (CONJUNCTS_THEN2 (K ALL_TAC) (qx_choose_then `r` (assume_tac o CONJUNCT1))))
    sha256_typed_post_run >>
  drule_then assume_tac expr_post_state >>
  drule_all_then assume_tac hash_sha256_source_success >>
  qexists_tac `r` >> conj_tac
  >- (qunabbrev_tac `ef` >> first_assum ACCEPT_TAC) >>
  conj_tac >- fs[storage_trace_domain_def, Abbr `ef`] >>
  `ef with gas_obs := [] = ef` by
    simp[Abbr `ef`, vyperStateTheory.evaluation_state_component_equality] >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func (z with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb))` by
    (irule alloca_history_run_inst_seq >> goal_assum (drule_at Any) >>
     fs[EVERY_CONJ, IS_PREFIX_APPEND] >> metis_tac[]) >>
  drule_all_then strip_assume_tac run_inst_seq_preserves_entry_control >>
  `z.vs_current_bb = sb.cs_current_bb /\
   LENGTH sb.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts sm sb)` by
    (conj_tac >- fs[same_blocks_def] >>
     qpat_assum `sb.cs_current_insts = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  drule_then assume_tac expr_post_frame >>
  `ghost_kept_at lo cenv mid sm G tn s Gf tf` by
    (qpat_assum `ghost_kept_at 0 _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ghost_kept_at_def] >> disch_then ACCEPT_TAC) >>
  drule_all_then assume_tac hash_ghost_kept_wb_trans >>
  qpat_x_assum `stmt_state_rel Jm _ _ _ _ mid s` kall_tac >>
  qpat_x_assum `expr_post Jm _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qx_gen_tac `H` >>
  `valid_horizon cx st0 H ef.storage_trace <=> valid_horizon cx st0 H mid.storage_trace` by
    simp[Abbr `ef`] >>
  qpat_x_assum `valid_horizon _ _ H ef.storage_trace <=> _` (fn th => once_rewrite_tac[th]) >>
  disch_tac >>
  qpat_assum `!U. valid_horizon _ _ U _ ==> inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qabbrev_tac `t = z with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)` >>
  conj_tac
  >- (qpat_assum `MAP _ (FILTER _ _) = [F]` (fn th => once_rewrite_tac[GSYM th]) >>
      qunabbrev_tac `t` >> irule run_inst_seq_gas_origin_ptr_path >>
      asm_rewrite_tac[] >> qexists_tac `bb` >> asm_rewrite_tac[] >>
      qpat_assum `s.vs_inst_idx = _` (fn idx =>
        qpat_assum `isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions)`
          (ACCEPT_TAC o REWRITE_RULE[idx]))) >>
  qpat_assum `!U. valid_horizon _ _ U _ ==> expr_post_mods U _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then (strip_assume_tac o REWRITE_RULE[expr_post_mods_def]))) >>
  `stmt_state_rel H ctx func cenv cx mid s` by
    (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _` (mp_then Any ACCEPT_TAC expr_post_state)) >>
  drule_all_then (qspec_then `v` (strip_assume_tac o SIMP_RULE bool_ss [LET_THM]))
    sha_success_landing_frame_mods >>
  `ef = SND (take_call_outcome NONE 2w (precompile_input Sha256 [v]) NONE mid)` by simp[Abbr `ef`] >>
  `immutable_frame_mods func cenv cx ef z` by fs[Abbr `ef`, sha_linked_immutable_pc] >>
  drule_all_then (qx_choose_then `w` strip_assume_tac) sha_success_stack_post_mods >>
  `w = r` by fs[] >>
  qpat_x_assum `w = r` SUBST_ALL_TAC >>
  `vv_post_mods H ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
    es sa sb s0 ef (Value r) (StackValue (BaseT (BytesT (Fixed 32))) op) t` by
    fs[sha_linked_stack_post, sha_linked_immutable_pc, Abbr `t`] >>
  `stmt_state_rel H ctx func cenv cx ef t` by fs[vv_post_mods_def] >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by (fs[Abbr `t`] >> decide_tac) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx ef Gf tf t` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ (SND _) _ _ _` mp_tac >>
     simp[Abbr `t`, Abbr `ef`]) >>
  `t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (qpat_assum `LENGTH sb.cs_current_insts = _` (fn th => once_rewrite_tac[th]) >> simp[Abbr `t`]) >>
  qpat_x_assum `ef = SND _` kall_tac >>
  qexists_tac `Value r` >>
  simp[expr_type_def, vv_store_bound_stack_word, is_word_type_def,
       ptr_vv_ok_def, ptr_val_ok_def, post_value_type_def, read_result_def, return_def,
       contextTheory.vv_location_def]
QED
