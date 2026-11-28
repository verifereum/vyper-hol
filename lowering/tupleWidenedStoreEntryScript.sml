Theory tupleWidenedStoreEntry
Ancestors
  bodyFullPredsMods[qualified]
  bodyFullPreds bodySimFull stmtLowering gasShadow gasShadowState
  gasShadowCompileBase vyperInterpreter fragExec contextRawReachable
  unitTransformDefs valueEncoding valueEncodingDefs vyperStorageFootprint
  exprLoweringProps exprSimHypsDefs compileEnv loweringPosts
  loweringStateRelDefs ptrDiscipline bodyPtrDefs stmtSimDefs allocaHistory
  venomInst venomState vyperTypeSystem vyperState vyperContext
  words finite_map pred_set list arithmetic

(* The fixed parameters describe the original statement boundary and the
   detached tuple snapshot; the cursor describes the remaining stores. *)
Definition tuple_widened_store_entry_def:
  tuple_widened_store_entry exps
    (DF,lo,d,ctx:venom_context,func:ir_function,shadow_func:ir_function)
    (cenv:compile_env,cx:evaluation_context,env:typing_env,st0,
     es:evaluation_state,ee:evaluation_state)
    (sa:compile_state,sb:compile_state,shadow_sb:compile_state,
     s0:venom_state,G0,tn0:taint)
    (tys,gs,elems,tvs,vs,w:bytes32,t:venom_state,tf:taint)
    i (c:compile_state) (sh:compile_state) (src:evaluation_state)
    (s:venom_state) G (tn:taint) obs <=>
  compile_tuple_store_all cenv (DROP i tys) (DROP i gs) (DROP i elems) c = ((),sb) /\
  compile_tuple_store_all (gas_shadow_env T cenv) (DROP i tys)
    (DROP i (MAP gas_shadow_assignment gs)) (DROP i elems) sh = ((),shadow_sb) /\
  fn_has_code c sb func /\ fn_has_code sh shadow_sb shadow_func /\ gas_shadow_state c sh /\
  expr_sim_inv_mods cenv.ce_modules cenv cx env src /\
  body_tuple_targets_full_ok_mods cenv.ce_modules exps cx (DROP i gs) (DROP i vs) /\
  storage_trace_domain cx st0 src.storage_trace /\
  (!tail. assign_tuple_target_list cx (TAKE i gs) (TAKE i vs)
    (ee with gas_obs := obs ++ tail) = (INL (),src with gas_obs := tail)) /\
  src.gas_obs = [] /\ ~s.vs_halted /\
  s.vs_current_bb = c.cs_current_bb /\ s.vs_inst_idx = LENGTH c.cs_current_insts /\
  ~block_is_terminated c /\ return_buf_frame d cenv c s /\
  return_buf_sep d cenv src s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x a. not_fresh_at sa x /\ lookup_var x s0 = SOME a ==> lookup_var x s = SOME a) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame cenv es sa s0 cenv src s /\
  (!aid off sz j. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b z. local_region cenv es.scopes s0 n b z ==> off + sz <= b \/ b + z <= off) /\
    off <= j /\ j < off + sz /\ j IN tn.t_mem ==> j IN tn0.t_mem) /\
  (!H. valid_horizon cx st0 H src.storage_trace ==>
    stmt_state_rel H ctx func cenv cx src s /\
    storage_well_formed_on cx src (FST H) /\ ghost_inv_at (DF H) lo d cenv cx src G tn s) /\
  local_ptrs_reserved cenv c /\ sa.cs_next_id <= c.cs_next_id /\ sa.cs_next_var <= c.cs_next_var /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at c x) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at c x) /\
  (!j. i <= j /\ j < LENGTH tys ==>
    ?x. EL j elems = Var x /\ not_fresh_at c x /\ op_taint tn (Var x) = {} /\
      (if is_word_type (EL j tys) then
         lookup_var x s = SOME (typed_val_to_w256 (EL j tvs) (EL j vs)) /\
         op_prov G (Var x) = NONE
       else
         lookup_var x s = SOME (n2w (w2n w + SUM (MAP type_memory_size (TAKE j tvs)))) /\
         ptr_covers G tn x s (type_memory_size (EL j tvs)) /\
         (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory (EL j tvs) (EL j vs)
             (w2n w + SUM (MAP type_memory_size (TAKE j tvs))) mem))) /\
  (?aid b z. FLOOKUP s.vs_allocas aid = SOME (b,z) /\ aid < c.cs_next_id /\
    b <= w2n w /\ w2n w + type_memory_size_list tvs <= b + z /\
    (!n lb lsz. local_region cenv src.scopes s n lb lsz ==> b + z <= lb \/ lb + lsz <= b)) /\
  mem_bytes_at (w2n w) (type_memory_size_list tvs) s.vs_memory =
    mem_bytes_at (w2n w) (type_memory_size_list tvs) t.vs_memory /\
  (!j. w2n w <= j /\ j < w2n w + type_memory_size_list tvs /\ j IN tn.t_mem ==>
    j IN tf.t_mem) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u)
End

Theorem tuple_widened_store_entry_slices:
  tuple_widened_store_entry exps (DF,lo,d,ctx,func,shadow_func) (cenv,cx,env,st0,es,ee)
    (sa,sb,shadow_sb,s0,G0,tn0) (tys,gs,elems,tvs,vs,w,t,tf) i c sh src s G tn obs ==>
  compile_tuple_store_all cenv (DROP i tys) (DROP i gs) (DROP i elems) c = ((),sb) /\
  compile_tuple_store_all (gas_shadow_env T cenv) (DROP i tys)
    (DROP i (MAP gas_shadow_assignment gs)) (DROP i elems) sh = ((),shadow_sb) /\
  gas_shadow_state c sh /\
  (!tail. assign_tuple_target_list cx (TAKE i gs) (TAKE i vs)
    (ee with gas_obs := obs ++ tail) = (INL (),src with gas_obs := tail))
Proof
  simp[tuple_widened_store_entry_def]
QED
