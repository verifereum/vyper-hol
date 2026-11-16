(* Runtime MethodId: hash, selector, and optional output-buffer composition. *)
Theory bodyFullBuiltinEnvMethodIdSuffix
Ancestors
  bodyFullBuiltinEnvMethodIdHashDynamic bodyFullBuiltinEnvMethodIdHashFixed
  bodyFullBuiltinEnvMethodIdSelector bodyFullBuiltinEnvMethodIdBuffer
  bodyFullBuiltinEnvMethodIdRuntime bodyFullGhostFrame bodyFullUnwrapRun wordArgsPtr
  exprSimHash exprSimSource exprSimWordArgs exprSimMemDefs exprSimUnwrapProps exprSimUnwrap
  exprSimVVFrame exprSimMemoryStack exprSimPtrLiteralBuffer bodySimFull bodyPtrDefs bodyMemoryDefs
  fragExec fragGasOriginPtr gasOutcomeFullCompose loweringPosts loweringStateRelDefs
  exprLoweringProps exprLowering compileEnv context freshWrites venomMemDefs
  ptrDiscipline exprSimProps valueEncoding valueEncodingDefs
  vyperValue vyperAST vyperInterpreter vyperState vyperTyping vyperContext
  vyperStorageTrace vyperStorageFootprint vyperTypeSystem exprSimHypsDefs exprSimHyps
  venomState vfmConstants finite_map list words arithmetic

Theorem method_id_runtime_full_suffix:
 !DF lo d explicit ctx func PG tops cenv cx env ann e es sa sm sb s0 st0 mid v x s G0 tn0 G tn fixed op.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann MethodId [e]) es /\
    ann = BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)) /\
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    local_ptrs_reserved cenv sa /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    return_buf_frame d cenv sa s0 /\ storage_trace_domain cx st0 mid.storage_trace /\
    (?xs. !tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs ++ tail) =
      (INL v, mid with gas_obs := tail)) /\
    mid.gas_obs = [] /\ ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_post H ctx func cenv cx e es sa sm s0 mid v x s /\
      expr_store_bound cx (expr_type e) v x s /\ alloca_history func s /\
      s0.vs_alloca_next <= s.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx mid G tn s /\
      ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
    ?r z G' tn'.
      builtin_result cx mid.accounts ann MethodId [expr_type e] [v] = INL r /\
      ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func z /\
      s.vs_alloca_next <= z.vs_alloca_next /\ local_ptrs_reserved cenv sb /\
      return_buf_frame d cenv sb z /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn') /\
        expr_post H ctx func cenv cx (Builtin ann MethodId [e]) es sa sb s0 mid r op z /\
        expr_store_bound cx (expr_type (Builtin ann MethodId [e])) r op z /\
        vv_post H ctx func cenv cx (Builtin ann MethodId [e]) es sa sb s0 mid (Value r) (if fixed then StackValue ann op else LocatedValue ann (mk_ptr op LocMemory)) z /\
        vv_store_bound cx (expr_type (Builtin ann MethodId [e])) (lowered_value_type cenv (Builtin ann MethodId [e])) mid (Value r) (if fixed then StackValue ann op else LocatedValue ann (mk_ptr op LocMemory)) z /\
        s0.vs_alloca_next <= z.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx mid G' tn' z /\
        ptr_val_ok cx (post_value_type cenv (Builtin ann MethodId [e])) r op G' tn' z /\
        ptr_vv_ok cx (post_value_type cenv (Builtin ann MethodId [e])) (Value r) (if fixed then StackValue ann op else LocatedValue ann (mk_ptr op LocMemory)) mid G' tn' z /\
        (~fixed ==> ptr_buf_ok cenv (Builtin ann MethodId [e]) op G' z) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
Proof
  rpt gen_tac >> strip_tac >> simp[LET_THM] >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
     gvs[expr_body_pre_def]) >>
  `is_bytes_or_string_type (expr_type e)` by
    (mp_tac (Q.INST [`b` |-> `MethodId`, `ty` |-> `ann`,
       `ts` |-> `[expr_type e]`] hash_builtin_types) >>
     gvs[expr_body_pre_def, well_typed_expr_def] >> metis_tac[]) >>
  `?bty. expr_type e = BaseT bty` by
    (Cases_on `expr_type e` >> gvs[is_bytes_or_string_type_def]) >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty)` by
    (drule expr_body_pre_type_evaluates >>
     Cases_on `bty` >> gvs[is_bytes_or_string_type_def,
       vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
     rename1 `expr_type e = BaseT (BytesT bd)` >>
     Cases_on `bd` >> gvs[AllCaseEqs()]) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs) = (INL v,mid)` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     `mid with gas_obs := [] = mid` by
       (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
     simp[]) >>
  `value_has_type (BaseTV bty) v` by
    (mp_tac (Q.INST [`es` |-> `es with gas_obs := xs`, `es'` |-> `mid`,
       `res` |-> `INL v`, `bt` |-> `bty`]
       (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_base_result)) >>
     simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `bind _ _ (es with gas_obs := xs) = (INL v,mid)` mp_tac >>
     drule (CONV_RULE (DEPTH_CONV ETA_CONV)
       forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  suspend "cut"
QED

Resume method_id_runtime_full_suffix[cut]:
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (qpat_assum `lower_value compile_expr cenv (expr_type e) e sa = (x,sm)`
      (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `(!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
   (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p)` by
    metis_tac[not_fresh_at_mono] >>
  `return_buf_frame d cenv sm s` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`, `s0`, `sa`] >>
     simp[] >> fs[expr_post_def, wb_frame_def]) >>
  `cs_extends sm sb` by
    (mp_tac (cj 5 hash_suffix_appends) >> simp[cs_appends_def] >>
     disch_then (qspecl_then [`expr_type e`,`x`,`fixed`,`sm`] mp_tac) >> simp[]) >>
  `fn_has_code sm sb func` by metis_tac[fn_has_code_split] >>
  drule_all hash_method_id_runtime_cut >> strip_tac >>
  rename1 `compile_method_id_hash (expr_type e) x sm = (hash,sh)` >>
  rename1 `emit_op SHR [Lit 224w;hash] sh = (sel,sn)` >>
  rename1 `emit_op SHL [Lit 224w;sel] sn = (word,sp)` >>
  drule_all hash_method_id_hash_cut >> strip_tac >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     expr_post H ctx func cenv cx e es sa sm s0 mid v x s /\
     expr_store_bound cx (expr_type e) v x s /\
     ghost_inv_at (DF H) lo d cenv cx mid G tn s /\
     ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
     (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `?hashed Gh tnh bs.
    LENGTH bs = 32 /\
    (!ann. builtin_result cx mid.accounts ann MethodId [expr_type e] [v] =
      INL (BytesV (TAKE 4 bs))) /\
    eval_operand hash hashed = SOME
      (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) (BytesV bs)) /\
    op_taint tnh hash = {} /\ op_prov Gh hash = NONE /\
    ~hashed.vs_halted /\ hashed.vs_current_bb = sh.cs_current_bb /\
    hashed.vs_inst_idx = LENGTH sh.cs_current_insts /\ alloca_history func hashed /\
    s.vs_alloca_next <= hashed.vs_alloca_next /\ local_ptrs_reserved cenv sh /\
    return_buf_frame d cenv sh hashed /\
    (!q. not_fresh_at sm q ==> lookup_var q hashed = lookup_var q s /\
      FLOOKUP Gh q = FLOOKUP G q /\ op_taint tnh (Var q) = op_taint tn (Var q)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP hashed.vs_allocas aid = SOME entry) /\
    locals_kept cenv mid mid s hashed /\ pure_frame cenv func mid sm s hashed /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK hashed,Gh,tnh) /\
      stmt_state_rel H ctx func cenv cx mid hashed /\
      storage_well_formed_on cx mid (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx mid Gh tnh hashed /\
      ghost_kept_at lo cenv mid sm G tn s Gh tnh)` by
    (Cases_on `is_bytestring_type (expr_type e)`
     >- (drule_all method_id_hash_dynamic_full_run >>
         disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
         qexistsl [`u`, `Gh`, `tnh`, `bs`] >> simp[] >>
         conj_tac >- (rpt strip_tac >> Cases_on `entry` >> metis_tac[]) >>
         metis_tac[]) >>
     drule_all method_id_hash_fixed_full_run >>
     disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
     qexistsl [`u`, `Gh`, `tnh`, `bs`] >> simp[] >>
     conj_tac >- (rpt strip_tac >> Cases_on `entry` >> metis_tac[]) >>
         metis_tac[]) >>
  suspend "frames"
QED

Resume method_id_runtime_full_suffix[frames]:
  `ghost_kept_at lo cenv mid sm G tn s Gh tnh` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace)
     ctx func cenv cx mid s` by fs[expr_post_def] >>
  `local_ptrs_rel func cenv mid.scopes s /\ allocas_non_overlapping s` by
    fs[stmt_state_rel_def,state_rel_def,alloca_inv_def] >>
  `!aid off len n b sz.
    FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
    local_region cenv mid.scopes s n b sz /\
    ~(off+len <= b \/ b+sz <= off) ==> off = b /\ len = sz` by suspend "overlap" >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gh tnh` by suspend "hash_ghost" >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace)
     ctx func cenv cx mid hashed` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `allocas_non_overlapping hashed` by fs[stmt_state_rel_def, alloca_inv_def] >>
  `!aid off len. aid < sm.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
     mem_bytes_at off len hashed.vs_memory = mem_bytes_at off len s.vs_memory` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `pure_frame cenv func mid sm s hashed`
       (mp_tac o CONJUNCT2 o PURE_REWRITE_RULE [pure_frame_def]) >>
     disch_then (qspecl_then [`off`,`len`] irule) >> rpt strip_tac >>
     `aid <> inst.inst_id` by decide_tac >>
     `FLOOKUP hashed.vs_allocas aid = SOME (off,len)` by metis_tac[] >>
     qpat_assum `allocas_non_overlapping hashed`
       (mp_tac o PURE_REWRITE_RULE [allocas_non_overlapping_def]) >>
     disch_then (qspecl_then [`aid`,`inst.inst_id`,`off`,`len`,`b`,`sz`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `wb_frame cenv es mid sa s0 s /\
   (~expr_has_effect e ==> pure_frame cenv func es sa s0 s)` by
    (qpat_assum `expr_post (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _`
       mp_tac >> simp[NoAsms,expr_post_def,wb_frame_def] >> metis_tac[]) >>
  `wb_frame cenv es mid sa s0 hashed` by
    (irule wb_frame_allocating_tail >> simp[] >> qexistsl [`s`, `mid.scopes`, `sm`] >>
     simp[] >> fs[pure_frame_def, locals_kept_def] >> metis_tac[]) >>
  `~expr_has_effect e ==> pure_frame cenv func es sa s0 hashed` by
    (strip_tac >> irule pure_frame_trans >> simp[] >> qexistsl [`mid`, `sm`, `s`] >>
     simp[] >> fs[wb_frame_def]) >>
  suspend "selector"
QED

Resume method_id_runtime_full_suffix[overlap]:
  rpt gen_tac >> strip_tac >>
  `FLOOKUP s.vs_allocas aid = SOME (off,len)` by
    (qpat_assum `expr_post (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _`
       mp_tac >> simp[NoAsms,expr_post_def] >> metis_tac[]) >>
  qpat_assum `local_region cenv mid.scopes s n b sz`
    (strip_assume_tac o PURE_REWRITE_RULE [local_region_def]) >>
  qpat_assum `local_ptrs_rel func cenv mid.scopes s`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [local_ptrs_rel_def]) >>
  disch_then (qspecl_then [`n`,`entry`,`p`,`sz`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `local_backed func p s _ sz`
    (strip_assume_tac o PURE_REWRITE_RULE [local_backed_def])
  >- (`aid = inst.inst_id` by
        (CCONTR_TAC >>
         qpat_assum `allocas_non_overlapping s`
           (mp_tac o PURE_REWRITE_RULE [allocas_non_overlapping_def]) >>
         disch_then (qspecl_then [`aid`,`inst.inst_id`,`off`,`len`,`w2n w`,`sz`] mp_tac) >>
         simp[]) >> gvs[]) >>
  qpat_x_assum `!aid b sz'. FLOOKUP s.vs_allocas aid = SOME (b,sz') ==> _`
    (qspecl_then [`aid`,`off`,`len`] mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Resume method_id_runtime_full_suffix[hash_ghost]:
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn`
    (strip_assume_tac o PURE_REWRITE_RULE [ghost_kept_at_def]) >>
  qpat_assum `ghost_kept_at lo cenv mid sm G tn s Gh tnh`
    (strip_assume_tac o PURE_REWRITE_RULE [ghost_kept_at_def]) >>
  simp[NoAsms,ghost_kept_at_def] >> rpt conj_tac
  >- (qx_gen_tac `q` >> strip_tac >>
      `not_fresh_at sm q` by metis_tac[not_fresh_at_mono] >>
      qpat_assum `!x. not_fresh_at sm x ==> FLOOKUP Gh x = _ /\ _`
        (qspec_then `q` mp_tac) >>
      qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP G x = _ /\ _`
        (qspec_then `q` mp_tac) >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      `i IN tn.t_mem` by
        (Cases_on `!n b sz'. local_region cenv mid.scopes s n b sz' ==>
            off+sz <= b \/ b+sz' <= off`
         >- ((qpat_assum `!aid off sz i. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _`
               (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
             `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by
               (qpat_assum `expr_post (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _`
                  mp_tac >> simp[NoAsms,expr_post_def] >> metis_tac[]) >>
             `aid < sm.cs_next_id` by decide_tac >> simp[] >> (metis_tac[NoAsms, expr_post_def]))) >>
         qpat_x_assum `~!n b sz'. local_region cenv mid.scopes s n b sz' ==> _`
           (strip_assume_tac o SIMP_RULE (srw_ss()) [NOT_FORALL_THM,NOT_IMP]) >>
         `off = b /\ sz = sz'` by metis_tac[] >> gvs[] >>
         qpat_assum `!n b sz i. local_region cenv mid.scopes s n b sz /\ _ ==> _`
           (qspecl_then [`n`,`b`,`sz`,`i`] mp_tac) >> simp[]) >>
      qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
        (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
      (impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC)) >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      `local_region cenv mid.scopes s n b sz` by
        (irule local_region_frame_fwd >> qexistsl [`s0`,`sa`,`es.scopes`] >>
         simp[] >> qpat_assum `expr_post (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _`
           mp_tac >> simp[NoAsms,expr_post_def] >> metis_tac[]) >>
      `i IN tn.t_mem` by
        (qpat_assum `!n b sz i. local_region cenv mid.scopes s n b sz /\ _ ==> _`
           (qspecl_then [`n`,`b`,`sz`,`i`] mp_tac) >> simp[]) >>
      qpat_assum `!n b sz i. local_region cenv es.scopes s0 n b sz /\ _ ==> _`
        (qspecl_then [`n`,`b`,`sz`,`i`] mp_tac) >> simp[]) >>
  metis_tac[]
QED

Resume method_id_runtime_full_suffix[selector]:
  `sh.cs_next_var <= sp.cs_next_var /\ sh.cs_next_id <= sp.cs_next_id` by
    (mp_tac (Q.SPECL [`SHR`,`[Lit 224w;hash]`,`sh`] ci_mono_emit_op) >>
     mp_tac (Q.SPECL [`SHL`,`[Lit 224w;sel]`,`sn`] ci_mono_emit_op) >>
     simp[ci_mono_def] >> rpt strip_tac >> decide_tac) >>
  `(!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sh p) /\
   (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sh p)` by
    (drule_all method_id_hash_grows >> strip_tac >> metis_tac[not_fresh_at_mono]) >>
  `fn_has_code sh sp func` by
    (Cases_on `fixed` >> gvs[] >> drule_all hash_method_id_mask_cut >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid hashed /\
     storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid Gh tnh hashed` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `builtin_result cx mid.accounts ann MethodId [expr_type e] [v] =
    INL (BytesV (TAKE 4 bs))` by simp[] >>
  drule_all method_id_selector_full_run >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  rename1 `eval_operand word selected = SOME _` >>
  suspend "selected_frames"
QED

Resume method_id_runtime_full_suffix[selected_frames]:
  `selected.vs_memory = hashed.vs_memory /\
   selected.vs_allocas = hashed.vs_allocas /\
   selected.vs_alloca_next = hashed.vs_alloca_next` by
    (qpat_assum `selected with <|vs_vars := _; vs_inst_idx := _|> = hashed`
       mp_tac >> simp[venom_state_component_equality] >> metis_tac[]) >>
  `sa.cs_next_var <= sh.cs_next_var /\ sa.cs_next_id <= sh.cs_next_id` by
    (drule_all method_id_hash_grows >> strip_tac >> decide_tac) >>
  `return_buf_frame d cenv sp selected` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`,`hashed`,`sh`] >>
     simp[] >> metis_tac[]) >>
  `wb_frame cenv es mid sa s0 selected` by
    (irule wb_frame_allocating_tail >> simp[] >>
     qexistsl [`hashed`,`mid.scopes`,`sh`] >> simp[] >> metis_tac[]) >>
  `~expr_has_effect e ==> pure_frame cenv func es sa s0 selected` by
    (strip_tac >> irule pure_frame_mem_tail >> qexists_tac `hashed` >> simp[]) >>
  `eval_operand word selected = SOME
      (typed_val_to_w256 (BaseTV (BytesT (Fixed 4))) (BytesV (TAKE 4 bs)))` by
    gvs[hash_full_bytes_roundtrip] >>
  rename1 `op_taint tns word = {}` >>
  rename1 `op_prov Gs word = NONE` >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gs tns` by
    (irule ghost_kept_at_clean_suffix >> qexistsl [`Gh`,`tnh`] >> simp[] >>
     metis_tac[not_fresh_at_mono]) >>
  `LENGTH (TAKE 4 bs) = 4` by simp[LENGTH_TAKE] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK selected,Gs,tns)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (s,G,tn) _ _ /\ _`
       (qspec_then `H` strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (hashed,Gh,tnh) _ _ /\ _`
       (qspec_then `H` strip_assume_tac) >>
     metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]) >>
  Cases_on `fixed`
  >- suspend "fixed_output" >>
  suspend "dynamic_output"
QED

Resume method_id_runtime_full_suffix[fixed_output]:
  gvs[] >> qexistsl [`selected`,`Gs`,`tns`] >> simp[] >>
  gen_tac >> disch_tac >>
  `stmt_state_rel H ctx func cenv cx mid selected /\
   storage_well_formed_on cx mid (FST H) /\
   ghost_inv_at (DF H) lo d cenv cx mid Gs tns selected` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==>
       gas_origin_ptr_path _ (hashed,Gh,tnh) _ _ /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `vv_post H ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 4))) MethodId [e])
    es sa sb s0 mid (Value (BytesV (TAKE 4 bs)))
    (StackValue (BaseT (BytesT (Fixed 4))) op) selected` by
    (irule vv_post_word_intro >>
     simp[expr_type_def,is_word_type_def,vyperValueTheory.evaluate_type_def] >>
     metis_tac[]) >>
  `expr_post H ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 4))) MethodId [e])
    es sa sb s0 mid (BytesV (TAKE 4 bs)) op selected` by
    (drule expr_post_of_vv_post_stack >> simp[]) >>
  simp[expr_type_def,expr_store_bound_def,vv_store_bound_def,
    is_word_type_def,ptr_vv_ok_def,read_result_def,return_def] >>
  irule ptr_val_ok_word >> simp[is_word_type_def]
QED

Resume method_id_runtime_full_suffix[dynamic_output]:
  gvs[] >> rename1 `compile_alloc_buffer 64 sp = (buf,sbuf)` >>
  `fn_has_code sp sb func` by
    (drule_all hash_method_id_mask_cut >> simp[]) >>
  `(!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sp p) /\
   (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sp p)` by
    metis_tac[not_fresh_at_mono] >>
  `TAKE 4 (word_to_bytes_be
     (typed_val_to_w256 (BaseTV (BytesT (Fixed 4))) (BytesV (TAKE 4 bs)))) =
     TAKE 4 bs` by
    (mp_tac (Q.INST [`bs` |-> `TAKE 4 bs`,`bd` |-> `Fixed 4`]
       typed_bytes_prefix) >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid selected` by metis_tac[] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     ghost_inv_at (DF H) lo d cenv cx mid Gs tns selected` by metis_tac[] >>
  `LENGTH (TAKE 4 bs) = 4` by simp[LENGTH_TAKE] >>
  `eval_operand word selected = SOME
    (typed_val_to_w256 (BaseTV (BytesT (Fixed 4))) (BytesV (TAKE 4 bs)))` by metis_tac[] >>
  drule_all method_id_output_buffer_full_run >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rename1 `eval_operand op z = SOME p` >>
  suspend "buffer_frames"
QED

Resume method_id_runtime_full_suffix[buffer_frames]:
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'` by
    (irule ghost_kept_at_clean_suffix >> qexistsl [`Gs`,`tns`] >>
     simp[] >> metis_tac[not_fresh_at_mono]) >>
  `sa.cs_next_var <= sp.cs_next_var /\ sa.cs_next_id <= sp.cs_next_id` by decide_tac >>
  `wb_frame cenv es mid sa s0 z` by
    (irule wb_frame_allocating_tail >> simp[] >>
     qexistsl [`selected`,`mid.scopes`,`sp`] >> simp[] >>
     gvs[] >> fs[venomStateTheory.lookup_var_def] >> metis_tac[]) >>
  `~expr_has_effect e ==> pure_frame cenv func es sa s0 z` by
    (strip_tac >> irule pure_frame_trans >> simp[] >>
     qexistsl [`mid`,`sp`,`selected`] >> simp[] >>
     gvs[] >> fs[wb_frame_def]) >>
  `w2n p + 64 <= z.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ z /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
     fs[stmt_state_rel_def,alloca_inv_def,alloca_next_valid_def] >>
     qpat_assum `!aid b sz. FLOOKUP _.vs_allocas aid = SOME (b,sz) ==> _`
       (qspecl_then [`sp.cs_next_id`,`w2n p`,`64`] mp_tac) >> simp[]) >>
  `sp.cs_next_id < sb.cs_next_id` by
    (`sbuf.cs_next_id = sp.cs_next_id+1` by
       (qpat_assum `compile_alloc_buffer 64 sp = (buf,sbuf)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[compile_alloc_buffer_def, emitHelperTheory.emit_op_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
        rpt strip_tac >> gvs[]) >>
     mp_tac (Q.SPECL [`MSTORE`,`[op; Lit 4w]`,`sbuf`] ci_mono_emit_void) >>
     mp_tac (Q.SPECL [`ADD`,`[op; Lit 32w]`,`st`] ci_mono_emit_op) >>
     mp_tac (Q.SPECL [`MSTORE`,`[data;word]`,`sd`] ci_mono_emit_void) >>
     simp[ci_mono_def] >> rpt strip_tac >> decide_tac) >>
  qexistsl [`z`,`G'`,`tn'`] >> simp[] >>
  conj_tac >- (gvs[] >> decide_tac) >> gen_tac >> disch_tac >>
  `stmt_state_rel H ctx func cenv cx mid z /\
   storage_well_formed_on cx mid (FST H) /\
   ghost_inv_at (DF H) lo d cenv cx mid G' tn' z` by metis_tac[] >>
  suspend "dynamic_posts"
QED

Resume method_id_runtime_full_suffix[dynamic_posts]:
  `vv_post H ctx func cenv cx (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [e])
    es sa sb s0 mid (Value (BytesV (TAKE 4 bs)))
    (LocatedValue (BaseT (BytesT (Dynamic 4))) (mk_ptr op LocMemory)) z` by
    (irule (SRULE [expr_type_def] (Q.INST
       [`e` |-> `Builtin (BaseT (BytesT (Dynamic 4))) MethodId [e]`]
       vv_post_allocated_memory_intro)) >>
     simp[expr_type_def,mk_ptr_def,is_word_type_def,
       vyperValueTheory.evaluate_type_def,val_wf_def,type_memory_size_def,
       val_footprint_def,vyperValueTheory.type_slot_size_def,word_size_def,dimword_def] >>
     qexistsl [`sp.cs_next_id`,`w2n p`,`64`] >> simp[] >>
     suspend "dynamic_disjoint") >>
  suspend "dynamic_finish"
QED
Resume method_id_runtime_full_suffix[dynamic_disjoint]:
  qexists_tac `p` >> simp[] >> conj_tac
  >- (qpat_assum `!n b sz. local_region cenv mid.scopes t n b sz ==> _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      simp[local_region_def,venomStateTheory.lookup_var_def,
        loweringStateRelDefsTheory.regions_disjoint_def]) >>
  metis_tac[]
QED

Resume method_id_runtime_full_suffix[dynamic_finish]:
  `expr_post H ctx func cenv cx (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [e])
    es sa sb s0 mid (BytesV (TAKE 4 bs)) op z` by
    (drule expr_post_of_vv_post_memory >> simp[mk_ptr_def,is_word_type_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn')` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ z /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
     metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]) >>
  `s0.vs_alloca_next <= z.vs_alloca_next` by (gvs[] >> decide_tac) >>
  simp[] >> suspend "dynamic_bounds"
QED

Resume method_id_runtime_full_suffix[dynamic_bounds]:
  gvs[] >>
  qpat_assum `LENGTH bs = 32` mp_tac >>
  qpat_assum `eval_operand (Var q) t = SOME p` mp_tac >>
  qpat_assum `FLOOKUP G' q = SOME (w2n p,64)` mp_tac >>
  qpat_assum `op_taint tn' (Var q) = {}` mp_tac >>
  qpat_assum `w2n p + 64 <= t.vs_alloca_next` mp_tac >>
  qpat_assum `ptr_mem_ok cx _ _ (Var q) G' tn' _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> ntac 6 strip_tac >>
  conj_tac
  >- (simp[expr_type_def,expr_store_bound_def,is_word_type_def,
        vyperValueTheory.evaluate_type_def,val_store_size_def,word_size_def,
        ghostPcTransportPtrTheory.eval_operand_inst_idx]) >>
  conj_tac
  >- (simp[expr_type_def,vv_store_bound_def,lowered_value_type_def,mk_ptr_def,
        is_word_type_def,vyperValueTheory.evaluate_type_def,read_result_def,return_def,
        val_store_size_def,type_memory_size_def,word_size_def,
        vyperValueTheory.type_slot_size_def,dimword_def,
        ghostPcTransportPtrTheory.eval_operand_inst_idx]) >>
  conj_tac
  >- simp[expr_type_def,ptr_val_ok_def,is_word_type_def] >>
  conj_tac
  >- (simp[expr_type_def,ptr_vv_ok_def,mk_ptr_def,read_result_def,return_def] >>
      gvs[ptr_mem_ok_def,ghostPcTransportPtrTheory.eval_operand_inst_idx]) >>
  simp[ptr_buf_ok_def,lowered_value_type_def,expr_type_def,type_memory_bytes_def,
       vyperValueTheory.type_slot_size_def,word_size_def]
QED
Finalise method_id_runtime_full_suffix
