(* Fixed-byte MethodId hashing with a shared finite-horizon endpoint. *)
Theory bodyFullBuiltinEnvMethodIdHashFixed
Ancestors
  stateRelProj
  bodyMemBiMethodIdEndpoint bodyFullHashKeccakFixed bodyFullGhostFrame bodyFullUnwrapSlotPost
  exprSimHash exprOperandVar exprSimAlloc fragGasSeqPtr
  allocaHistoryFragment bodyPtrHashBuiltinsKeccakFixedRun
  bodyPtrHashBuiltinsCursor bodyPtrHashBuiltinsAllocFrame
  instIdxIndep memSafeRun bodyMemoryDefs ptrDiscipline venomMemDefs
  loweringPosts fragExecMem contextCodegenRel memLocDefs bodyPtrDefs
  exprSimDefs exprSimProps exprSimHypsDefs exprLoweringProps
  builtinHashing compileEnv loweringStateRelDefs vyperStorageTrace
  venomState venomInst venomExecSemantics finite_map list rich_list words
  vyperStorageFootprint arithmetic fragExec methodIdHashFixedObserved

Theorem method_id_hash_fixed_full_run:
 !DF lo d explicit ctx func PG cenv cx e es sa sm sh s0 st0 mid v x s G tn hash bty.
 expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
 ~is_bytestring_type (expr_type e) /\
 evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
 value_has_type (BaseTV bty) v /\
 lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
 compile_method_id_hash (expr_type e) x sm = (hash,sh) /\
 fn_has_code sm sh func /\ fn_inst_ids_distinct func /\
 (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ local_ptrs_reserved cenv sa /\
 local_ptrs_reserved cenv sm /\
 (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
 (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
 return_buf_frame d cenv sm s /\
 MAP FDOM es.scopes = MAP FDOM mid.scopes /\
 storage_trace_domain cx st0 mid.storage_trace /\
 ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
 s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
 (!H. valid_horizon cx st0 H mid.storage_trace ==>
   expr_post H ctx func cenv cx e es sa sm s0 mid v x s /\
   expr_store_bound cx (expr_type e) v x s /\
   ghost_inv_at (DF H) lo d cenv cx mid G tn s /\
   ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
   (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s))
 ==>
 ?u Gh tnh bs.
 LENGTH bs = 32 /\
 (!ann. builtin_result cx mid.accounts ann MethodId [expr_type e] [v] =
   INL (BytesV (TAKE 4 bs))) /\
 eval_operand hash u = SOME
   (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) (BytesV bs)) /\
 op_taint tnh hash = {} /\ op_prov Gh hash = NONE /\
 ~u.vs_halted /\ u.vs_current_bb = sh.cs_current_bb /\
 u.vs_inst_idx = LENGTH sh.cs_current_insts /\ alloca_history func u /\
 s.vs_alloca_next <= u.vs_alloca_next /\ local_ptrs_reserved cenv sh /\
 return_buf_frame d cenv sh u /\
 (!p. not_fresh_at sm p ==> lookup_var p u = lookup_var p s /\
   FLOOKUP Gh p = FLOOKUP G p /\ op_taint tnh (Var p) = op_taint tn (Var p)) /\
 (!aid a len. FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
   FLOOKUP u.vs_allocas aid = SOME (a,len) /\
   (aid < sm.cs_next_id ==>
     mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory)) /\
 locals_kept cenv mid mid s u /\ pure_frame cenv func mid sm s u /\
 (!H. valid_horizon cx st0 H mid.storage_trace ==>
   gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK u,Gh,tnh) /\
   stmt_state_rel H ctx func cenv cx mid u /\
   storage_well_formed_on cx mid (FST H) /\
   ghost_inv_at (DF H) lo d cenv cx mid Gh tnh u /\
   ghost_kept_at lo cenv mid sm G tn s Gh tnh)
Proof
 rpt gen_tac >> strip_tac >>
 drule_all method_id_hash_fixed_observed >>
 disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
 qexistsl_tac [`u`, `Gh`, `tnh`, `bs`] >> asm_rewrite_tac[]
QED
