Theory createSizeBlueprintAbiReplayCutsMods
Ancestors
  createSizeCtorRowsReplayMods createCtorRowCutsMods createSizeOperandPreMods
  exprLoweringProps freshWrites vyperCreate list rich_list

(* Specialize constructor-row replay to the ABI blueprint operand layout. *)
Theorem blueprint_abi_replay_ctor_cuts_mods:
  ctors <> [] /\ contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_body_pre_mods mods ce cx env (Call ann (CreateTarget (CreateFromBlueprint F) hs rof ks) args df) entry /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  EVERY (create_operand_completed_ok_mods mods exps cx) (create_operand_order (CreateFromBlueprint F) hs args) /\
  (!i s vs s'. i < LENGTH ctors /\ ~exprs_can_mutate ce (DROP (SUC i) ctors) /\
    eval_exprs cx (DROP (SUC i) ctors) s = (INL vs,s') ==>
    !tr. get_storage cx s' tr = get_storage cx s tr) /\
  local_ptrs_reserved ce (C 0) /\ (!K. dead_lo_ok_mods K (DF K) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  (!i. i < LENGTH ctors ==>
    compile_expr ce (expr_type (EL i ctors)) (EL i ctors) (C i) = (V i,M i) /\
    compile_expr (gas_shadow_env T ce) (expr_type (EL i ctors)) (gas_shadow_expr (EL i ctors)) (Sh i) = (V i,SM i) /\
    compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) ctors))
      (ext_call_arg_value (lowered_value_type ce (EL i ctors)) (V i)) (M i) =
      (EL i svs,C (SUC i)) /\
    (St (SUC i)).vs_current_bb = (C (SUC i)).cs_current_bb /\
    (St (SUC i)).vs_inst_idx = LENGTH (C (SUC i)).cs_current_insts /\
    R i = (Chunk i ++ Snap i) ++ R (SUC i) /\
    create_expr_prefix (C i) (M i) (gas_explicit_sites ctx shctx) ctx func
      (St i) (Chunk i) (Mid i) /\
    (Mid i).vs_current_bb = (M i).cs_current_bb /\
    (Mid i).vs_inst_idx = LENGTH (M i).cs_current_insts /\
    create_expr_prefix (M i) (C (SUC i)) (gas_explicit_sites ctx shctx) ctx func
      (Mid i) (Snap i) (St (SUC i)) /\
    fn_has_code (M i) (C (SUC i)) func /\ ci_mono (C 0) (C i) /\
    (is_word_type (lowered_value_type ce (EL i ctors)) ==>
      compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) ctors))
        (ext_call_arg_value (lowered_value_type ce (EL i ctors)) (V i)) (SM i) =
        (EL i svs,Sh (SUC i)) /\
      expr_sim_full_code (ctx,shctx,func,shfunc) (C i,C (SUC i),Sh i,Sh (SUC i))) /\
    (~is_word_type (lowered_value_type ce (EL i ctors)) ==>
      expr_sim_full_code (ctx,shctx,func,shfunc) (C i,M i,Sh i,SM i))) /\
  (!i. i < LENGTH ctors ==> ?j. ctor_segment_fetch func (St (SUC i)) = SOME j /\
    j.inst_opcode <> PHI /\ (C (SUC i)).cs_next_id <= j.inst_id) /\
  (!i. i < LENGTH ctors ==>
    (is_word_type (lowered_value_type ce (EL i ctors)) ==>
      create_expr_prefix (C i) (C (SUC i)) (gas_explicit_sites ctx shctx) ctx func
        (St i) (Chunk i ++ Snap i) (St (SUC i))) /\
    (~is_word_type (lowered_value_type ce (EL i ctors)) /\
      exprs_can_mutate ce (DROP (SUC i) ctors) /\
      gas_origin_path T (gas_explicit_sites ctx shctx) ctx func (Mid i) [] (OK (St (SUC i))) ==>
      Snap i = [])) /\
  bind (eval_exprs cx ctors) k p0 = (res,out) /\ (!vs. storage_trace_frame (k vs)) /\
  valid_horizon cx st0 H out.storage_trace /\
  p0.gas_obs = gas_explicit (R 0) (St 0).vs_gas_readings ++ tail /\
  expr_sim_inv_mods mods ce cx env p0 /\ return_buf_frame d ce (C 0) (St 0) /\
  alloca_history func (St 0) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (St 0)) /\
  (!f i z. frag_reachable ctx func (St 0) f i z ==> dalloca_fmp_headroom i z) /\
  ~(St 0).vs_halted /\ (St 0).vs_current_bb = (C 0).cs_current_bb /\
  (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\
  (!K. valid_horizon cx st0 K p0.storage_trace ==>
    stmt_state_rel K ctx func ce cx p0 (St 0) /\
    immutable_frame_mods func ce cx p0 (St 0) /\ storage_well_formed_on cx p0 (FST K) /\
    ghost_inv_at_mods (DF K) lo d ce cx p0 G0 tn0 (St 0)) ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?cvs E gf tf. E 0 = p0 /\ LENGTH cvs = LENGTH ctors /\
    eval_exprs cx ctors p0 = (INL cvs,E (LENGTH ctors)) /\
    k cvs (E (LENGTH ctors)) = (res,out) /\
    valid_horizon cx st0 H (E (LENGTH ctors)).storage_trace /\
    (!i. i <= LENGTH ctors ==>
      (E i).gas_obs = gas_explicit (R i) (St i).vs_gas_readings ++ tail /\
      expr_sim_inv_mods mods ce cx env (E i) /\ return_buf_frame d ce (C i) (St i) /\
      alloca_history func (St i) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (St i)) /\
      (!f j z. frag_reachable ctx func (St i) f j z ==> dalloca_fmp_headroom j z) /\
      ~(St i).vs_halted /\ (St i).vs_current_bb = (C i).cs_current_bb /\
      (St i).vs_inst_idx = LENGTH (C i).cs_current_insts) /\
    (!K. valid_horizon cx st0 K (E (LENGTH ctors)).storage_trace ==>
      stmt_state_rel K ctx func ce cx (E (LENGTH ctors)) (St (LENGTH ctors)) /\
      immutable_frame_mods func ce cx (E (LENGTH ctors)) (St (LENGTH ctors)) /\
      storage_well_formed_on cx (E (LENGTH ctors)) (FST K) /\
      ghost_inv_at_mods (DF K) lo d ce cx (E (LENGTH ctors)) gf tf (St (LENGTH ctors))) /\
    (!i. i < LENGTH ctors ==>
      bind (eval_expr cx (EL i ctors)) (read_result cx) (E i) = (INL (EL i cvs),E (SUC i)) /\
      expr_body_pre_mods mods ce cx env (EL i ctors) (E i) /\
      (?tv ann. evaluate_type (get_tenv cx) (lowered_value_type ce (EL i ctors)) = SOME tv /\
        evaluate_type (get_tenv cx) (expr_type (EL i ctors)) = SOME ann /\
        arg_type_fits (lowered_value_type ce (EL i ctors)) (expr_type (EL i ctors)) /\
        value_has_type tv (EL i cvs) /\ value_has_type ann (EL i cvs)) /\
      (!g h. (!K. valid_horizon cx st0 K (E i).storage_trace ==>
          stmt_state_rel K ctx func ce cx (E i) (St i) /\
          storage_well_formed_on cx (E i) (FST K) /\
          ghost_inv_at_mods (DF K) lo d ce cx (E i) g h (St i)) ==>
        (is_word_type (lowered_value_type ce (EL i ctors)) ==>
          ?g' h'. !K op. valid_horizon cx st0 K (E (SUC i)).storage_trace /\
            lower_value compile_expr ce (expr_type (EL i ctors)) (EL i ctors) (C i) =
              (op,C (SUC i)) ==>
            expr_sim_full_post_mods (DF,lo,d,ctx,func) ce cx (EL i ctors)
              (E i,C i,C (SUC i),St i,op,g,h) K (INL (EL i cvs) : value + exception)
              ((E (SUC i)) with gas_obs := []) g' h' (St (SUC i))) /\
        (~is_word_type (lowered_value_type ce (EL i ctors)) ==>
          ?g' h' raw. eval_expr cx (EL i ctors) (E i) = (INL raw,E (SUC i)) /\
          !K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
            vv_post_mods K ctx func ce cx (EL i ctors) (E i) (C i) (M i) (St i)
              ((E (SUC i)) with gas_obs := []) raw (V i) (Mid i) /\
            vv_store_bound cx (post_value_type ce (EL i ctors)) (lowered_value_type ce (EL i ctors))
              ((E (SUC i)) with gas_obs := []) raw (V i) (Mid i) /\
            ptr_vv_ok cx (post_value_type ce (EL i ctors)) raw (V i)
              ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
            alloca_history func (Mid i) /\ (St i).vs_alloca_next <= (Mid i).vs_alloca_next /\
            ghost_inv_at_mods (DF K) lo d ce cx ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
            ghost_kept_at lo ce (E i) (C i) g h (St i) g' h' /\
            (!tag op. V i = StackValue tag op /\ ~is_word_type (post_value_type ce (EL i ctors)) ==>
              ptr_buf_ok ce (EL i ctors) op g' (Mid i)) /\
            (!tag p. V i = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok ce (EL i ctors) p.ptr_operand g' (Mid i)) /\
            (ce.ce_is_ctor /\ vv_location (V i) = SOME LocCode ==>
              ?val. read_result cx raw ((E (SUC i)) with gas_obs := []) =
                (INL val,(E (SUC i)) with gas_obs := []) /\
              !rt w. evaluate_type (get_tenv cx) (post_value_type ce (EL i ctors)) = SOME rt /\
                eval_operand (vv_operand (V i)) (Mid i) = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside h'.t_mem (Mid i).vs_memory mem ==>
                  val_in_memory rt val (w2n w) mem))))) /\
    (!i. i < LENGTH ctors /\ ~exprs_can_mutate ce (DROP (SUC i) ctors) ==>
      !tr. get_storage cx (E (LENGTH ctors)) tr = get_storage cx (E (SUC i)) tr)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!i. i < LENGTH ctors ==> create_operand_completed_ok_mods mods exps cx (EL i ctors)` by
    (qpat_assum `args = _` (fn th => qhdtm_assum `EVERY` (mp_tac o REWRITE_RULE[th])) >>
     Cases_on `hs` >> simp[create_operand_order_def,EVERY_APPEND] >>
     metis_tac[EVERY_MEM,EL_MEM]) >>
  `!i p. i < LENGTH ctors /\ expr_sim_inv_mods mods ce cx env p ==>
         expr_body_pre_mods mods ce cx env (EL i ctors) p` by
    (rpt strip_tac >> irule create_call_operand_body_pre_mods >> simp[] >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) entry` (irule_at Any) >>
     simp[MEM_APPEND,EL_MEM]) >>
  mp_tac (Q.INST [`args` |-> `ctors`] create_ctor_rows_at_cuts_mods) >>
  (impl_tac >- suspend "rows") >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (qx_choose_then `cvs` (qx_choose_then `E` (qx_choose_then `gf` (qx_choose_then `tf`
      (map_every assume_tac o CONJUNCTS))))))
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> qexistsl [`cvs`,`E`,`gf`,`tf`] >> asm_rewrite_tac[] >>
  suspend "storage"
QED

Resume blueprint_abi_replay_ctor_cuts_mods[rows]:
  asm_rewrite_tac[] >>
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `!i. i < LENGTH ctors ==> (_ ==> create_expr_prefix _ _ _ _ _ _ _ _) /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `local_ptrs_reserved ce (C i) /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C i) x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C i) x)` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var,freshWritesTheory.not_fresh_at_mono]) >>
  asm_rewrite_tac[] >>
  conj_tac >- (disch_tac >> first_x_assum (drule_then strip_assume_tac) >> simp[]) >>
  strip_tac >> simp[]
QED

Resume blueprint_abi_replay_ctor_cuts_mods[storage]:
  `!i. i < LENGTH ctors ==>
     bind (eval_expr cx (EL i ctors)) (read_result cx) (E i) = (INL (EL i cvs),E (SUC i))` by
    (rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`args` |-> `ctors`, `vs` |-> `cvs`] ctor_rows_source_mods) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  strip_tac >> qx_gen_tac `i` >> strip_tac >>
  `SUC i <= LENGTH ctors` by decide_tac >>
  qpat_assum `!i. i <= LENGTH ctors ==> eval_exprs _ _ _ = _`
    (qspec_then `SUC i` (drule_then assume_tac)) >>
  qpat_assum `!i s vs s'. _ ==> !tr. get_storage _ _ tr = _`
    (qspecl_then [`i`,`E (SUC i)`,`DROP (SUC i) cvs`,`E (LENGTH ctors)`] mp_tac) >>
  simp[]
QED

Finalise blueprint_abi_replay_ctor_cuts_mods
