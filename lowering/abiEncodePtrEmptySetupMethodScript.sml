Theory abiEncodePtrEmptySetupMethod
Ancestors abiBuiltinEncodeMethod bodyPtrDefs bodyPtrPrecompileBuiltinsPrefixes
  bodyPtrPrecompileBuiltinsFreshFrame bodyPtrPrecompileBuiltinsSuffixGhost
  bodyPtrHashBuiltinsGhostFrame bodyPtrHashBuiltinsAllocFrame
  compileEnv emitHelper emitHelperProps exprLoweringProps fragGasSeqPtr
  ptrDiscipline venomState venomExecSemantics venomInst finite_map
  words list rich_list arithmetic pred_set

Theorem abi_encode_empty_method_ptr:
  abi_builtin_encode_method_id method_id (Var x) sa = ((),sb) /\
  ptr_covers G tn x s outsz /\ lookup_var x s = SOME (n2w p) /\
  not_fresh_at sa x /\ p < dimword (:256) /\
  (method_id <> NONE ==> 64 <= outsz /\ p+32 < dimword (:256)) /\
  ~ctx_has_dalloca ctx /\ ghost_inv rb cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
  (!v k. cenv.ce_return_buf = SOME (PtrVar (Var v) k) ==> not_fresh_at sa v) /\
  (!v k. cenv.ce_return_pc = SOME (PtrVar (Var v) k) ==> not_fresh_at sa v) /\
  (!name b k. method_id <> NONE /\ local_region cenv es.scopes s name b k ==>
      regions_disjoint (p+32) 32 b k) /\
  st.cs_next_var <= sa.cs_next_var /\
  ghost_kept cenv es st G0 tn0 s0 G tn ==>
  ?raw t H tm.
    run_inst_seq (emitted_insts sa sb) s = OK raw /\
    t = raw with vs_inst_idx := LENGTH sb.cs_current_insts /\
    inst_seq_ptr (cx_dead cx) 0 ctx func PG G tn (emitted_insts sa sb) s H tm /\
    ghost_inv rb cenv cx es H tm t /\
    ghost_kept cenv es st G0 tn0 s0 H tm /\
    ptr_covers H tm x t outsz /\ lookup_var x t = SOME (n2w p) /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ op_taint tm (Var v) = op_taint tn (Var v)) /\
    tm.t_mem = (case method_id of NONE => tn.t_mem | SOME mid =>
      tn.t_mem DIFF {i | p+32 <= i /\ i < p+64}) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 t.vs_memory = abi_builtin_encode_method_bytes mid)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `method_id`
  >- (gvs[abiBuiltinEncodeCodeTheory.abi_builtin_encode_method_id_def,
       comp_return_def, emitted_insts_def, run_inst_seq_def, inst_seq_ptr_def] >>
      gvs[hash_ghost_inv_inst_idx, ptr_covers_def, lookup_var_def]) >>
  rename1 `abi_builtin_encode_method_id (SOME mid) _ _ = _` >>
  `?raw H tm.
     run_inst_seq (emitted_insts sa sb) s = OK raw /\
     (!k. inst_seq_ptr (cx_dead cx) 0 ctx func PG G tn
       (emitted_insts sa sb) (s with vs_inst_idx := k) H tm) /\
     raw.vs_memory = (mstore (p+32) (mid << 224) s).vs_memory /\
     tm.t_mem = tn.t_mem DIFF {i | p+32 <= i /\ i < p+64} /\
     tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\
     (!v. not_fresh_at sa v ==> lookup_var v raw = lookup_var v s /\
       FLOOKUP H v = FLOOKUP G v /\ op_taint tm (Var v) = op_taint tn (Var v))` by
    (`(do dst <- emit_op ADD [Var x; Lit (n2w 32)];
          emit_void MSTORE [dst; Lit (mid << 224)] od) sa = ((),sb)` by
       gvs[abiBuiltinEncodeCodeTheory.abi_builtin_encode_method_id_def] >>
     `64 <= outsz /\ w2n (n2w p:bytes32) + 32 < dimword (:256) /\
      eval_operand (Lit (mid << 224)) s = SOME (mid << 224) /\
      op_taint tn (Lit (mid << 224)) = {} /\
      (!v. Lit (mid << 224) = Var v ==> not_fresh_at sa v)` by
       gvs[eval_operand_def, op_taint_def, w2n_n2w] >>
     drule_all (SRULE [] (Q.INST [`off` |-> `32`, `D` |-> `cx_dead cx`, `fn` |-> `func`] emitted_offset_word_store_checked)) >>
     disch_then (mp_tac o SPEC_ALL) >>
     simp[word_add_n2w, w2n_n2w, op_taint_def]) >>
  suspend "transport"
QED

Resume abi_encode_empty_method_ptr[transport]:
  `?dst. emitted_insts sa sb =
    [mk_inst sa.cs_next_id ADD [Var x; Lit 32w] [dst];
     mk_inst (sa.cs_next_id+1) MSTORE [Var dst; Lit (mid << 224)] []]` by
    (qpat_x_assum `abi_builtin_encode_method_id _ _ _ = _` mp_tac >>
     simp[abiBuiltinEncodeCodeTheory.abi_builtin_encode_method_id_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[emitted_insts_def, DROP_APPEND1] >>
     qexists `STRING #"%" (toString sa.cs_next_var)` >> simp[]) >>
  `tm.t_imm = tn.t_imm` by
    (irule bodyPtrIfExpBytesFrameTheory.inst_seq_ptr_immutable_frame >>
     first_x_assum (qspec_then `s.vs_inst_idx` assume_tac) >>
     goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
  `raw.vs_call_ctx = s.vs_call_ctx /\ raw.vs_accounts = s.vs_accounts /\
   raw.vs_transient = s.vs_transient /\ raw.vs_allocas = s.vs_allocas /\
   raw.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `run_inst_seq _ s = OK raw` mp_tac >>
     simp[run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       mk_inst_def, venomExecSemanticsTheory.exec_pure2_def,
       eval_operand_def] >>
     gvs[lookup_var_def] >>
     simp[update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
       venomExecSemanticsTheory.exec_write2_def,
       mstore_def, write_memory_with_expansion_def] >>
     strip_tac >> gvs[]) >>
  `!v. not_fresh_at st v ==> not_fresh_at sa v` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `ghost_kept cenv es st G0 tn0 s0 H tm` by
    (irule ghost_kept_subset_trans >> qexistsl [`G`, `tn`] >>
     simp[] >> metis_tac[]) >>
  `ghost_inv rb cenv cx es H tm raw` by
    (irule fresh_scratch_ghost_frame >>
     qexistsl [`G`, `func`, `32`, `p+32`, `s`, `tn`] >>
     simp[] >> conj_tac >- metis_tac[optionTheory.NOT_NONE_SOME] >>
     conj_tac
     >- (gvs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
     rpt strip_tac >> irule abiDecodeStaticPropsTheory.mem_bytes_at_mstore_outside >>
     decide_tac) >>
  `mem_bytes_at (p+32) 4 raw.vs_memory = abi_builtin_encode_method_bytes mid` by
    (simp[] >> irule abi_builtin_encode_method_window >>
     simp[venomMemPropsTheory.mload_mstore_same]) >>
  `ptr_covers H tm x raw outsz` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  qexistsl [`raw`, `raw with vs_inst_idx := LENGTH sb.cs_current_insts`, `H`, `tm`] >>
  qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `s.vs_inst_idx` assume_tac) >>
  gvs[hash_ghost_inv_inst_idx, ptr_covers_def, lookup_var_def] >>
  metis_tac[]
QED

Finalise abi_encode_empty_method_ptr
