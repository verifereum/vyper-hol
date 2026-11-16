(* Fixed-byte MethodId hashing with a shared finite-horizon endpoint. *)
Theory bodyFullBuiltinEnvMethodIdHashFixed
Ancestors
  bodyFullHashKeccakFixed bodyFullGhostFrame bodyFullUnwrapSlotPost
  exprSimHash exprOperandVar exprSimAlloc fragGasSeqPtr
  allocaHistoryFragment bodyPtrHashBuiltinsKeccakFixedRun
  bodyPtrHashBuiltinsCursor bodyPtrHashBuiltinsAllocFrame
  instIdxIndep memSafeRun bodyMemoryDefs ptrDiscipline venomMemDefs
  loweringPosts fragExecMem contextCodegenRel memLocDefs bodyPtrDefs
  exprSimDefs exprSimProps exprSimHypsDefs exprLoweringProps
  builtinHashing compileEnv loweringStateRelDefs vyperStorageTrace
  venomState venomInst venomExecSemantics finite_map list rich_list words
  vyperStorageFootprint arithmetic fragExec

Theorem method_id_hash_fixed_full_run:
 !DF lo d explicit ctx func PG cenv cx e es sa sm sh s0 st0 mid v x s G tn hash bty.
 expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
 ~is_bytestring_type (expr_type e) /\
 evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
 value_has_type (BaseTV bty) v /\
 lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
 compile_method_id_hash (expr_type e) x sm = (hash,sh) /\
 fn_has_code sm sh func /\ fn_inst_ids_distinct func /\
 ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sa /\
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
 `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
    mid.storage_trace` by fs[storage_trace_domain_def] >>
 `expr_post (storage_trace_horizon mid.storage_trace)
    ctx func cenv cx e es sa sm s0 mid v x s` by metis_tac[] >>
 drule_all method_id_hash_typed_post_run >> strip_tac >>
 rename1 `run_inst_seq (emitted_insts sm sh) s = OK typed_end` >>
 `?m payload. bty = BytesT (Fixed m) /\ v = BytesV payload /\ m <= 32` by
   (Cases_on `bty` >>
    gvs[vyperTypeSystemTheory.is_bytes_or_string_type_def, is_bytestring_type_def] >>
    rename1 `BytesT bd` >> Cases_on `bd` >>
    gvs[vyperTypeSystemTheory.is_bytes_or_string_type_def, is_bytestring_type_def] >>
    Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def,
      vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
 gvs[] >>
 `compile_keccak256_bytesm x m sm = (hash,sh)` by
   gvs[compile_method_id_hash_def, is_bytestring_type_def] >>
 `?w. eval_operand x s = SOME w /\ LENGTH payload = m /\
    TAKE (LENGTH payload) (word_to_bytes_be w) = payload` by
   (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    drule_at (Pos hd) hash_fixed_post_view >> simp[]) >>
 `!p. x = Var p ==> not_fresh_at sm p` by
   (drule_at (Pos hd) compile_lower_value_var >> simp[]) >>
 `stmt_state_rel (storage_trace_horizon mid.storage_trace)
    ctx func cenv cx mid s` by metis_tac[expr_post_def] >>
 `op_taint tn x = {} /\ allocas_from lo s /\ lo <= s.vs_alloca_next` by
   (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    gvs[ptr_val_ok_def, post_value_type_def, is_word_type_def, ghost_inv_at_def]) >>
 `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
     [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
   (irule (SRULE [] (Q.INST [`sha` |-> `F`] hash_fixed_alloca_code)) >>
    goal_assum (drule_at Any) >> simp[]) >>
 `same_blocks sm sh /\
  sh.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sh /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sh)` by
   (irule keccak_suffix_shape >> metis_tac[]) >>
 `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sm sh ++ rest` by
   suspend "code" >>
 `run_inst_seq_mem_ok (emitted_insts sm sh) s` by suspend "memory" >>
 `?u Gh tnh.
    run_inst_seq (emitted_insts sm sh) s = OK u /\
    u.vs_current_bb = s.vs_current_bb /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sh)),Gh,tnh)) /\
    eval_operand hash u = SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 payload)) /\
    op_taint tnh hash = {} /\ op_prov Gh hash = NONE /\
    (!p. not_fresh_at sm p ==> lookup_var p u = lookup_var p s) /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    (!H D. stmt_state_rel H ctx func cenv cx mid s /\
       ghost_inv_at D lo d cenv cx mid G tn s ==>
       stmt_state_rel H ctx func cenv cx mid u /\
       ghost_inv_at D lo d cenv cx mid Gh tnh u /\
       ghost_kept_at lo cenv mid sm G tn s Gh tnh)` by
   (`isPREFIX (emitted_insts sm sh) (DROP s.vs_inst_idx bb.bb_instructions)` by
      simp[IS_PREFIX_APPEND] >>
    drule_all (Q.SPEC `storage_trace_horizon mid.storage_trace` hash_fixed_keccak_joint_run) >>
    FAIL_TAC "joint interface") >>
 `typed_end = u` by metis_tac[] >> gvs[] >>
 suspend "finish"
QED

Resume method_id_hash_fixed_full_run[code]:
 gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
 qexistsl_tac [`l`, `l'`] >> simp[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

Resume method_id_hash_fixed_full_run[memory]:
 cheat
QED

Resume method_id_hash_fixed_full_run[finish]:
 cheat
QED

Finalise method_id_hash_fixed_full_run
