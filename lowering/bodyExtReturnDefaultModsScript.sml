(* The selected default of an external-call return, on the linked frame. *)
Theory bodyExtReturnDefaultMods
Ancestors
  bodyExtReturnLayoutMods bodyExtReturnAllocMods bodyExtReturnDefaultControlMods
  bodyExtReturnDefaultWordMods bodyExtReturnDefaultBytesMods
  bodyExtReturnDefaultFlatMods bodyExtReturnDefaultWidenedMods
  bodyExtReturnDefaultPostMods actualAllocExec bodyPtrBopRepresentationFrame
  bodyPtrBopHashFootprint annassignRelayoutPost exprBodyPreProps
  exprBodyPreTypingProps bodyExprPreFacts exprSimExtCallCase
  compileEnv exprLoweringProps fragExec exprSafeOperand venomState
  context loweringPosts
  ptrDiscipline freshWrites fragGasOriginPtr words finite_map
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
Libs monadsyntax

Theorem extcall_return_default_mods:
  ret_type <> NoneT /\ has_default /\ returnData = [] /\
  expr_body_pre_mods mods cenv cx env
    (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt) es /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  cap = abi_size_bound cenv.ce_struct_fields
          (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type) /\
  (if ret_type = NoneT then comp_return (Lit 0w)
   else if has_default then
     comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
       (\r. compile_default_return_path cenv ret_type default_ty buf_op
          r.buf_operand default_op addr_op skip
          (abi_static_size cenv.ce_struct_fields
             (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type))
          cap (type_to_abi_dec_info cenv.ce_struct_fields cenv
             (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)))
   else
     comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
       (\r. comp_bind (compile_return_value_decode
                   (abi_static_size cenv.ce_struct_fields
                      (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)) cap)
       (\hi_op. comp_ignore_bind
          (compile_abi_decode_to_buf r.buf_operand (Lit 0w) MLOAD buf_op hi_op
             (type_to_abi_dec_info cenv.ce_struct_fields cenv
                (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)))
          (comp_return r.buf_operand)))) sr = (result_op,sb) /\
  vv = (if ret_type = NoneT then StackValue ann result_op
        else LocatedValue ann (mk_ptr result_op LocMemory)) /\
  fn_has_code sr sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ MEM func ctx.ctx_functions /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr_op buf_op
    cap target has_default default_op default_ty default_opt returnData ee t /\
  (IS_SOME default_opt /\ ~is_word_type default_ty ==>
    ?w aid tv. eval_operand default_op t = SOME w /\
      evaluate_type (get_tenv cx) default_ty = SOME tv /\
      FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      aid < sr.cs_next_id) /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
    immutable_frame_mods func cenv cx ee t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  EVERY (\op. op_taint tn op = {}) [addr_op; buf_op; default_op] /\
  (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
    ptr_mem_ok cx default_ty dv default_op G tn t /\
    (type_memory_bytes cenv default_ty <> 0 ==>
      ?x b sz w. default_op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
        eval_operand default_op t = SOME w /\ b <= w2n w /\
        w2n w + type_memory_bytes cenv default_ty <= b + sz /\
        w2n w + type_memory_bytes cenv default_ty <= t.vs_alloca_next)) /\
  (cap <> 0 ==>
    ?v b sz ro. buf_op = Var v /\ FLOOKUP G v = SOME (b,sz) /\
      eval_operand buf_op t = SOME ro /\ b <= w2n ro /\ w2n ro + cap <= b + sz /\
      (!i. w2n ro <= i /\ i < w2n ro + MIN cap (LENGTH returnData) ==> i NOTIN tn.t_mem)) ==>
  ?res r G' tn'.
    (!tail.
      (case (if returnData = [] then default_opt else NONE) of
       SOME v => do accounts' <- get_accounts;
                    check (skip \/ ext_call_has_code target accounts')
                      "ExtCall target has no code";
                    return (Value v) od
     | NONE => do v <- lift_sum_runtime
                    (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
                  return (Value v) od) (ee with gas_obs := tail) =
        (res,ee with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (r,G',tn') /\
      ((?z tv. r = OK z /\ res = INL tv /\
        let e = Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts)
                      args dflt in
        vv_post_mods H ctx func cenv cx e es sa sb s0 (ee with gas_obs := []) tv vv z /\
        vv_store_bound cx (expr_type e) (lowered_value_type cenv e) (ee with gas_obs := []) tv vv z /\
        z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
        ghost_inv_at_mods (DF H) lo d cenv cx (ee with gas_obs := []) G' tn' z /\
        ptr_vv_ok cx (post_value_type cenv e) tv vv (ee with gas_obs := []) G' tn' z /\
        (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
          ?val. read_result cx tv (ee with gas_obs := []) = (INL val,ee with gas_obs := []) /\
                !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                       eval_operand (vv_operand vv) z = SOME w ==>
                  w2n w + type_memory_size rt <= lo /\
                  (!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
                    val_in_memory rt val (w2n w) mem)) /\
        (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type cenv e) ==>
          ptr_buf_ok cenv e op G' z) /\
        (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv e p.ptr_operand G' z) /\
        vv_own cenv cx (post_value_type cenv e) sa sb (ee with gas_obs := []) tv vv z /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn') \/
       (exit_result r /\ create_size_exit_ok ctx res r /\ expr_exit res r)))
Proof
  strip_tac >>
  qpat_x_assum `cap = abi_size_bound _ _` kall_tac >>
  gvs[] >>
  drule_all_then strip_assume_tac extcall_return_layout_mods >>
  qpat_assum `extcall_returned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[extcall_returned_def]) >>
  Cases_on `default_opt` >- fs[extcall_default_ready_def] >>
  rename1 `extcall_default_ready cx ret_type T default_op default_ty (SOME dv) t` >>
  qpat_x_assum `extcall_default_ready _ _ _ _ _ _ _` mp_tac >>
  simp[extcall_default_ready_def] >> strip_tac >>
  qexists_tac `if skip \/ ext_call_has_code target ee.accounts then INL (Value dv)
    else INR (Error (RuntimeError "ExtCall target has no code"))` >>
  simp[vyperStateTheory.get_accounts_def, vyperStateTheory.bind_def,
    vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
    vyperStateTheory.check_def, vyperStateTheory.assert_def, COND_RAND, COND_RATOR] >>
  Cases_on `?H. valid_horizon cx st0 H ee.storage_trace`
  >- suspend "entry" >>
  qexistsl_tac [`OK t`,`G`,`tn`] >> rpt strip_tac >> metis_tac[]
QED

Resume extcall_return_default_mods[entry]:
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `h0` assume_tac) >>
  qpat_x_assum `let rt = _ in _` kall_tac >>
  `type_memory_bytes cenv ret_type < dimword (:256)` by decide_tac >>
  Cases_on `compile_alloc_buffer (type_memory_bytes cenv ret_type) sr` >>
  rename1 `compile_alloc_buffer _ sr = (buf,ar)` >>
  fs[comp_bind_def] >>
  `ci_mono sr ar` by
    (qpat_assum `compile_alloc_buffer _ sr = (buf,ar)` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[ci_mono_compile_alloc_buffer,pairTheory.SND]) >>
  `ci_mono ar sb` by
    (qpat_assum `compile_default_return_path _ _ _ _ _ _ _ _ _ _ _ ar = (_,sb)` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[ci_mono_compile_default_return_path,pairTheory.SND]) >>
  `cs_extends sr ar /\ cs_extends ar sb` by fs[ci_mono_def] >>
  `fn_has_code sr ar func /\ fn_has_code ar sb func` by
    (conj_tac >> irule fn_has_code_mid >> simp[] >>
     qexistsl_tac [`sb`,`sr`] >> simp[cs_extends_refl]) >>
  `?H. valid_horizon cx st0 H ee.storage_trace` suffices_by
    (disch_tac >> drule_all extcall_return_alloc_cut_mods >>
     disch_then (qspecl_then [`explicit`,`PG`]
       (qx_choosel_then [`q`,`dw`,`a`,`J`,`tm`] strip_assume_tac)) >>
     suspend "control_entry") >>
  qexists_tac `h0` >> simp[]
QED

Resume extcall_return_default_mods[control_entry]:
  `sa.cs_next_id <= sr.cs_next_id /\ sr.cs_next_var <= ar.cs_next_var` by fs[ci_mono_def] >>
  `sa.cs_next_var <= ar.cs_next_var` by decide_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at ar x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv ar` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sr` >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ar x` by metis_tac[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ar x` by metis_tac[] >>
  `safe_operand ar default_op /\ safe_operand ar addr_op` by
    (conj_tac >> irule safe_operand_mono >> qexists_tac `sr` >> simp[]) >>
  `!op. safe_operand sr op ==>
      eval_operand op a = eval_operand op t /\ op_taint tm op = op_taint tn op` by
    (Cases_on `op` >> simp[safe_operand_def,eval_operand_def,op_taint_def] >>
     strip_tac >> qpat_assum `!x. not_fresh_at sr x ==> lookup_var x a = _ /\ _`
       (drule_then strip_assume_tac) >> fs[op_taint_def]) >>
  `eval_operand default_op a = SOME w /\ op_taint tm default_op = {} /\
   eval_operand addr_op a = SOME aw /\ op_taint tm addr_op = {}` by
    (qpat_assum `!op. safe_operand sr op ==> _`
       (qspecl_then [`default_op`] mp_tac) >>
     qpat_assum `!op. safe_operand sr op ==> _`
       (qspecl_then [`addr_op`] mp_tac) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ a /\ _`
    (qspec_then `h0` (drule_then strip_assume_tac)) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp a)` by
    (qpat_assum `stmt_state_rel h0 _ _ _ _ _ a` (mp_tac o MATCH_MP
       bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >> simp[]) >>
  `lo <= a.vs_alloca_next` by decide_tac >>
  qpat_assum `buf.buf_operand = Var q` (fn th =>
    qpat_x_assum `compile_default_return_path _ _ _ _ _ _ _ _ _ _ _ ar = _`
      (assume_tac o REWRITE_RULE[th])) >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`bs` |-> `[]`, `has_default` |-> `T`]
    (INST_TYPE [alpha |-> ``:256``] extcall_default_entry_tmem_mods))) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`ds`,`de`,`ck`,`dj`,`xl`,`cj`,`old3`,`u`,`Gu`,`tu`] strip_assume_tac)) >>
  `?p Gp tp.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK p,Gp,tp)) /\
    typed_copy_state_frame ds (w2n dw) (type_memory_size actual_tv) u p /\
    (!mem. mem_agree_outside tp.t_mem p.vs_memory mem ==>
      val_in_memory actual_tv dv (w2n dw) mem) /\
    (!x. not_fresh_at ds x ==>
      FLOOKUP Gp x = FLOOKUP Gu x /\ op_taint tp (Var x) = op_taint tu (Var x)) /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size actual_tv) ==>
      (i IN tp.t_mem <=> i IN tu.t_mem)) /\
    tp.t_stor = tu.t_stor /\ tp.t_trans = tu.t_trans /\ tp.t_imm = tu.t_imm /\
    ~p.vs_halted /\ p.vs_current_bb = de.cs_current_bb /\
    p.vs_inst_idx = LENGTH de.cs_current_insts` by suspend "payload" >>
  suspend "after_payload"
QED

Resume extcall_return_default_mods[payload]:
  Cases_on `is_word_type ret_type`
  >- (`eval_operand default_op u = eval_operand default_op t` by simp[] >>
      drule_all extcall_default_word_payload >>
      disch_then (qspecl_then [`explicit`,`PG`] ACCEPT_TAC)) >>
  suspend "nonword_payload"
QED

Resume extcall_return_default_mods[nonword_payload]:
  `~is_word_type default_ty` by
    (qpat_assum `type_widens_to _ _ _` mp_tac >>
     metis_tac[vyperTypeSystemTheory.type_widens_to_def,
               aggregateEvaluatedLayoutTheory.arg_type_fits_word_type]) >>
  qpat_assum `~is_word_type default_ty ==> ptr_mem_ok _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `!x. default_op = Var x ==> FLOOKUP Gu x = FLOOKUP G x` by
    (rpt strip_tac >>
     `not_fresh_at sr x` by fs[safe_operand_def] >>
     `not_fresh_at ar x` by
       (irule not_fresh_at_mono >> qexists_tac `sr` >> simp[]) >>
     qpat_assum `!x. not_fresh_at sr x ==> lookup_var x a = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at ar x ==> lookup_var x u = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `w2n w + val_footprint tv dv <= t.vs_alloca_next` by simp[] >>
  `!i. i < t.vs_alloca_next /\ i IN tu.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >>
     `i IN tm.t_mem` by
       (qpat_assum `tu.t_mem = tm.t_mem` (fn th => pure_rewrite_tac[GSYM th]) >>
        first_assum ACCEPT_TAC) >>
     `~(t.vs_alloca_next <= i)` by decide_tac >>
     qpat_assum `!j. j IN tm.t_mem <=> j IN tn.t_mem \/ _`
       (qspec_then `i` mp_tac) >>
     qpat_assum `i IN tm.t_mem` (fn th =>
       qpat_assum `~(t.vs_alloca_next <= i)` (fn lt => simp[NoAsms,th,lt]))) >>
  `ptr_mem_ok cx default_ty dv default_op Gu tu u` by
    (irule bop_ptr_mem_ok_frame >> qexistsl_tac [`G`,`t`,`tn`,`tv`] >>
     simp[] >> rpt strip_tac >>
     qpat_assum `!i. i < t.vs_alloca_next /\ i IN tu.t_mem ==> _` irule >>
     simp[] >> decide_tac) >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
       sz = type_memory_size rt) fields)` by
    (drule expr_body_pre_mods_inv >>
     simp[NoAsms,exprSimHypsDefsTheory.expr_sim_inv_mods_def] >>
     strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  `type_memory_bytes cenv default_ty = type_memory_size tv` by
    (irule typedMemoryCopyTheory.typed_copy_memory_size >>
     qexists_tac `get_tenv cx` >> simp[] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  `type_memory_size tv <> 0 ==>
     (?x. default_op = Var x /\ ptr_covers Gu tu x u (type_memory_size tv)) /\
     w2n w + type_memory_size tv <= u.vs_alloca_next` by
    (strip_tac >> qpat_assum `type_memory_bytes cenv default_ty <> 0 ==> _` mp_tac >>
     (impl_tac >- simp[]) >> strip_tac >>
     rename1 `default_op = Var src` >>
     `FLOOKUP Gu src = FLOOKUP G src` by simp[] >>
     conj_tac >- (qexists_tac `src` >> gvs[bodyPtrDefsTheory.ptr_covers_def,eval_operand_def]) >>
     fs[] >> decide_tac) >>
  `ptr_covers Gu tu q u (type_memory_size actual_tv) /\
   w2n dw + type_memory_size actual_tv <= u.vs_alloca_next` by
    (qpat_assum `type_memory_bytes cenv ret_type = type_memory_size actual_tv`
       (fn th => pure_rewrite_tac[GSYM th]) >> conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `is_bytestring_type ret_type`
  >- (drule_all extcall_default_bytes_payload >>
      disch_then (qspecl_then [`explicit`,`PG`] ACCEPT_TAC)) >>
  `alloca_room ctx func a` by
    (qpat_assum `stmt_state_rel h0 _ _ _ _ _ a`
       (mp_then Any ACCEPT_TAC stateRelProjTheory.stmt_state_rel_alloca_room)) >>
  `u.vs_alloca_next < dimword (:256)` by
    (qpat_assum `alloca_room ctx func a`
       (mp_then Any mp_tac alloca_room_next_lt) >> simp[]) >>
  Cases_on `default_ty = ret_type`
  >- (qpat_x_assum `default_ty = ret_type` SUBST_ALL_TAC >>
      `tv = actual_tv` by
        (qpat_assum `evaluate_type (get_tenv cx) ret_type = SOME tv` mp_tac >>
         qpat_assum `evaluate_type (get_tenv cx) ret_type = SOME actual_tv`
           (fn th => simp[NoAsms,th])) >>
      qpat_x_assum `tv = actual_tv` SUBST_ALL_TAC >>
      `type_memory_size actual_tv <> 0 ==>
         (?x. default_op = Var x /\ ptr_covers Gu tu x u (type_memory_size actual_tv)) /\
         ptr_covers Gu tu q u (type_memory_size actual_tv) /\
         w2n w + type_memory_size actual_tv <= u.vs_alloca_next /\
         w2n dw + type_memory_size actual_tv <= u.vs_alloca_next /\
         u.vs_alloca_next < dimword (:256)` by simp[] >>
      drule_all extcall_default_flat_payload >>
      disch_then (qspecl_then [`explicit`,`PG`] ACCEPT_TAC)) >>
  suspend "widened_payload"
QED

Resume extcall_return_default_mods[widened_payload]:
  `0 < type_memory_size tv` by
    (drule_all strict_widening_source_positive >> simp[]) >>
  `type_memory_size tv <> 0` by decide_tac >>
  qpat_assum `type_memory_size tv <> 0 ==> _` (drule_then strip_assume_tac) >>
  rename1 `default_op = Var src` >>
  `loweringStateRelDefs$regions_disjoint
     (w2n dw) (type_memory_size actual_tv) (w2n w) (type_memory_size tv)` by
    (qpat_assum `~is_word_type default_ty ==> ?aid. _` (drule_then strip_assume_tac) >>
     qpat_assum `!aid b len. aid < sr.cs_next_id /\ FLOOKUP t.vs_allocas aid = _ ==> _`
       (drule_all_then mp_tac) >> simp[]) >>
  Q.SUBGOAL_THEN `w2n w + type_memory_size tv <= w2n dw \/
      w2n dw + type_memory_size actual_tv <= w2n w` assume_tac
  >- (qpat_assum `loweringStateRelDefs$regions_disjoint (w2n dw) _ (w2n w) _` mp_tac >>
      simp[NoAsms,loweringStateRelDefsTheory.regions_disjoint_def,DISJ_COMM]) >>
  `!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
     val_in_memory tv dv (w2n w) mem` by
    (rpt strip_tac >> drule_all ptr_mem_ok_robust >> simp[]) >>
  `w2n w + type_memory_size tv < dimword (:256) /\
   w2n dw + type_memory_size actual_tv < dimword (:256)` by decide_tac >>
  Q.SUBGOAL_THEN `type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= u.vs_alloca_next`
    assume_tac >- simp[] >>
  Q.SUBGOAL_THEN `type_memory_size actual_tv = 0 \/ w2n dw + type_memory_size actual_tv <= u.vs_alloca_next`
    assume_tac >- simp[] >>
  `(is_bytestring_type ret_type ==> is_bytestring_type default_ty)` by simp[] >>
  `compile_store_memory cenv (Var src) (Var q) ret_type default_ty ds = ((),de) /\
   not_fresh_at ds src /\ lookup_var src u = SOME w` by
    (qpat_assum `default_op = Var src` SUBST_ALL_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qpat_assum `!x. Var src = Var x ==> not_fresh_at ds x`
                    (qspec_then `src` mp_tac) >> simp[]) >>
     qpat_assum `eval_operand (Var src) u = SOME w`
       (ACCEPT_TAC o REWRITE_RULE[eval_operand_def])) >>
  drule_all extcall_default_widened_payload >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`p`,`Gp`,`tp`] strip_assume_tac)) >>
  qexistsl_tac [`p`,`Gp`,`tp`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume extcall_return_default_mods[after_payload]:
  `stmt_state_rel h0 ctx func cenv cx ee u` by
    (qpat_assum `!H. stmt_state_rel H ctx func cenv cx ee a ==>
                     stmt_state_rel H ctx func cenv cx ee u`
       (qspec_then `h0` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK u,Gu,tu)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (t,G,tn) [] (OK a,J,tm)`
       (qspec_then `D` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
     disch_then (qspecl_then [`a`,`J`,`tm`,`[]`,`OK u`,`Gu`,`tu`] mp_tac) >> simp[]) >>
  drule_all (INST_TYPE [beta |-> ``:eval_result``, gamma |-> ``:eval_result``]
    extcall_default_exit_create_size_mods) >>
  Cases_on `skip \/ ext_call_has_code target ee.accounts` >>
  simp[Excl "create_size_exit_ok_inr"]
  >- (disch_then (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac) >>
      qexistsl_tac [`OK z`,`Gz`,`tz`] >> qx_gen_tac `h` >> strip_tac >>
      conj_tac >- suspend "join_path" >>
      disj1_tac >> qexists_tac `z` >>
      suspend "copy_post") >>
  disch_then (qx_choosel_then [`r`,`Gz`,`tz`] strip_assume_tac) >>
  qexistsl_tac [`r`,`Gz`,`tz`] >> qx_gen_tac `h` >> strip_tac >>
  reverse conj_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (qpat_assum `create_size_exit_ok ctx (INR _) r` mp_tac >> simp[NoAsms]) >>
     first_assum ACCEPT_TAC) >>
  suspend "abort_path"
QED

Resume extcall_return_default_mods[join_path]:
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gu`,`u`,`tu`] >> simp[]
QED

Resume extcall_return_default_mods[abort_path]:
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gu`,`u`,`tu`] >> simp[]
QED

Resume extcall_return_default_mods[copy_post]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ a /\ _`
    (qspec_then `h` (drule_then strip_assume_tac)) >>
  `stmt_state_rel h ctx func cenv cx ee u` by
    (qpat_assum `!H. stmt_state_rel H ctx func cenv cx ee a ==>
                     stmt_state_rel H ctx func cenv cx ee u`
       (qspec_then `h` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at_mods (DF h) lo d cenv cx ee Gu tu u` by
    (qpat_assum `!D d. ghost_inv_at_mods D lo d cenv cx ee J tm a ==>
                      ghost_inv_at_mods D lo d cenv cx ee Gu tu u` match_mp_tac >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!es s0 sa G0 tn0. sa.cs_next_var <= ar.cs_next_var ==> _`
    (qspecl_then [`es`,`s0`,`sa`,`G0`,`tn0`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (CONJUNCTS_THEN (drule_then assume_tac)) >>
  `!x. not_fresh_at sa x ==> not_fresh_at ds x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `ar` >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ds x` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at ds x` irule >>
     qpat_assum `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
       (drule_then ACCEPT_TAC)) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ds x` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at ds x` irule >>
     qpat_assum `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
       (drule_then ACCEPT_TAC)) >>
  suspend "copy_site"
QED

Resume extcall_return_default_mods[copy_site]:
  drule_all_then assume_tac actual_alloc_buffer_site >>
  drule_then strip_assume_tac loweringHaltTheory.compile_alloc_buffer_parts >>
  `sr.cs_next_id < sb.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
  `FLOOKUP u.vs_allocas sr.cs_next_id = SOME (w2n dw,type_memory_size actual_tv)` by
    (qpat_assum `u.vs_allocas = a.vs_allocas` SUBST1_TAC >>
     qpat_assum `type_memory_bytes cenv ret_type = _`
       (fn th => pure_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
  `lo <= w2n dw` by
    (qpat_assum `allocas_from lo u`
       (mp_tac o REWRITE_RULE[allocas_from_def]) >>
     disch_then (drule_then ACCEPT_TAC)) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by
    (simp[] >> decide_tac) >>
  `w2n dw + type_memory_size actual_tv <= u.vs_alloca_next /\
   ptr_covers Gu tu q u (type_memory_size actual_tv)` by
    (qpat_assum `type_memory_bytes cenv ret_type = _`
       (fn th => pure_rewrite_tac[GSYM th]) >> conj_tac >> first_assum ACCEPT_TAC) >>
  `!aid b len. FLOOKUP s0.vs_allocas aid = SOME (b,len) /\ aid < sa.cs_next_id ==>
     regions_disjoint (w2n dw) (type_memory_size actual_tv) b len` by
    (rpt strip_tac >>
     `FLOOKUP t.vs_allocas aid = SOME (b,len)` by
       (qpat_assum `wb_frame cenv es ee sa s0 t`
          (strip_assume_tac o REWRITE_RULE[loweringPostsTheory.wb_frame_def]) >>
        first_x_assum (drule_then ACCEPT_TAC)) >>
     `aid < sr.cs_next_id` by decide_tac >>
     qpat_assum `!aid b len. aid < sr.cs_next_id /\ FLOOKUP t.vs_allocas aid = _ ==> _`
       (drule_all_then mp_tac) >> simp[]) >>
  `!name b len. local_region cenv ee.scopes u name b len ==>
     regions_disjoint (w2n dw) (type_memory_size actual_tv) b len` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes a name b len` by
       (irule (iffLR loweringStateRelDefsTheory.local_region_lookup_cong) >>
        goal_assum (drule_at (Pat `local_region _ _ u _ _ _`)) >>
        rpt strip_tac >>
        `not_fresh_at ar p'` by metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
        qpat_assum `!x. not_fresh_at ar x ==> lookup_var x u = _ /\ _`
          (drule_then strip_assume_tac) >> simp[]) >>
     qpat_assum `!name b len. local_region cenv ee.scopes a name b len ==> _`
       (drule_then mp_tac) >> simp[]) >>
  `!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size actual_tv) ==>
       (i IN tz.t_mem <=> i IN tu.t_mem)` by
    (qpat_assum `tu.t_mem = tm.t_mem` SUBST1_TAC >>
     qpat_assum `!i. i IN tm.t_mem <=> _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `type_memory_bytes cenv ret_type = _` SUBST1_TAC >>
     qpat_assum `!i. _ ==> (i IN tz.t_mem <=> _)` mp_tac >>
     simp[NoAsms, arithmeticTheory.ADD_COMM, DE_MORGAN_THM]) >>
  suspend "copy_apply"
QED

Resume extcall_return_default_mods[copy_apply]:
  qabbrev_tac `e = Call ret_type (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt` >>
  `expr_type e = ret_type /\ lowered_value_type cenv e = ret_type /\
   post_value_type cenv e = ret_type /\ expr_has_effect e` by
    simp[Abbr `e`, exprLoweringTheory.lowered_value_type_def,
         post_value_type_def, vyperASTTheory.expr_type_def,
         supportedExprTraverseTheory.expr_has_effect_def,
         Once supportedExprTraverseTheory.supported_expr_exists_def,
         supportedExprTraverseTheory.expr_effect_root_def] >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  qabbrev_tac `vv = LocatedValue ret_type (mk_ptr (Var q) LocMemory)` >>
  `vv_post_mods h ctx func cenv cx e es sa sb s0 ee (Value dv) vv z /\
   vv_store_bound cx ret_type ret_type ee (Value dv) vv z /\
   s0.vs_alloca_next <= z.vs_alloca_next /\
   ghost_inv_at_mods (DF h) lo d cenv cx ee Gz tz z /\
   ptr_vv_ok cx ret_type (Value dv) vv ee Gz tz z /\
   ptr_buf_ok cenv e (Var q) Gz z /\
   vv_own cenv cx ret_type sa sb ee (Value dv) vv z /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tz` suffices_by
    (strip_tac >> qunabbrev_tac `vv` >> fs[mk_ptr_def, vv_location_def]) >>
  qunabbrev_tac `vv` >>
  match_mp_tac (GEN_ALL (SIMP_RULE bool_ss [LET_THM] extcall_default_copy_post_mods)) >>
  goal_assum (drule_at (Pat `typed_copy_state_frame ds _ _ u z`)) >>
  goal_assum (drule_at (Pat `ghost_inv_at_mods (DF h) lo d cenv cx ee Gu tu u`)) >>
  qexists_tac `mk_inst sr.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv ret_type))]
    [STRING #"%" (toString sr.cs_next_var)]` >>
  simp[venomInstTheory.mk_inst_def, LET_THM] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Finalise extcall_return_default_mods
