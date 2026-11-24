(* Runtime MethodId: hash, selector, and optional output-buffer composition. *)
Theory bodyFullBuiltinEnvMethodIdSuffix
Ancestors
  bodyFullBuiltinEnvMethodIdHashDynamic bodyFullBuiltinEnvMethodIdHashFixed
  bodyFullBuiltinEnvMethodIdSelector bodyFullBuiltinEnvMethodIdBuffer
  methodIdSuffixObserved
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
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
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
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
  mp_tac (Q.SPEC `\a b s z. T` method_id_runtime_suffix_from_observed_parts) >>
  BETA_TAC >>
  (impl_tac >-
    (conj_tac
     >- (rpt gen_tac >> strip_tac >> Cases_on `is_bytestring_type (expr_type e)`
         >- (drule_all method_id_hash_dynamic_full_run >>
             disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
             qexistsl [`u`,`Gh`,`tnh`,`bs`] >> simp[] >>
             conj_tac >- (rpt strip_tac >> PairCases_on `entry` >> metis_tac[]) >>
             metis_tac[]) >>
         drule_all method_id_hash_fixed_full_run >>
         disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
         qexistsl [`u`,`Gh`,`tnh`,`bs`] >> simp[] >>
         conj_tac >- (rpt strip_tac >> PairCases_on `entry` >> metis_tac[]) >>
             metis_tac[]) >>
     pure_rewrite_tac [AND_CLAUSES] >> conj_tac
     >- MATCH_ACCEPT_TAC method_id_selector_full_run >>
     MATCH_ACCEPT_TAC method_id_output_buffer_full_run)) >>
  disch_then (fn th => rpt gen_tac >>
    disch_then (strip_assume_tac o MATCH_MP (SPEC_ALL th))) >>
  qexistsl [`r`,`z`,`G'`,`tn'`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
