Theory bodyFullAbiEncodeFinish
Ancestors
  bodyFullAbiEncodeStore bodyFullAbiEncodeOffset bodyFullAttributeAdd
  bodyPtrMakeArrayWordStore bodyPtrMakeArrayPrimitiveInstall
  typedMemoryCopy bodyFullPathHistory abiBuiltinEncodeCode
  exprSimAbiEncodeFinish emitHelperProps bodyPtrMakeArrayEmission
  venomState venomExecSemantics venomInst finite_map words pred_set arithmetic
  compileEnv ptrDiscipline emitHelper loweringStateRelDefs
  wordLoadStorePtr venomMemProps allocationPtr valueEncodingProps
  ptrSafeRun bodyPtrDefs abiEncoderPathProps

Theorem abi_encode_finish_add_origin[local]:
  emit_op ADD [left;Lit off] a = (dst,b) /\ fn_has_code a b func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\ allocas_from lo s /\
  eval_operand left s = SOME w /\ op_taint tn left = {} ==>
  ?q t G' tn'. dst = Var q /\
    t = (update_var q (w+off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,G',tn')) /\
    eval_operand dst t = SOME (w+off) /\ op_taint tn' dst = {} /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> q ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!x. not_fresh_at a x ==> x <> q)
Proof
  rpt strip_tac >> drule_all emit_op_fetch_boundary >> strip_tac >>
  rename1 `dst = Var q` >>
  qabbrev_tac `i = mk_inst a.cs_next_id ADD [left;Lit off] [q]` >>
  qabbrev_tac `u = update_var q (w+off) s` >>
  qabbrev_tac `G' = step_prov PG G i u` >>
  qabbrev_tac `tn' = step_taint i s u tn` >>
  `(!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (u with vs_inst_idx := SUC s.vs_inst_idx),G',tn')) /\
    op_taint tn' (Var q) = {} /\ tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> q ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))` by
    (mp_tac (Q.INST [`sm` |-> `a`, `sn` |-> `b`, `out` |-> `q`,
       `t` |-> `u with vs_inst_idx := SUC s.vs_inst_idx`]
       attribute_add_full_frame) >>
     simp[Abbr `i`, Abbr `u`, Abbr `G'`, Abbr `tn'`] >> metis_tac[]) >>
  qexistsl_tac [`q`, `u with vs_inst_idx := SUC s.vs_inst_idx`, `G'`, `tn'`] >>
  simp[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem abi_encode_finish_store_origin[local]:
  emit_void MSTORE [Var root;value] a = ((),b) /\ fn_has_code a b func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts /\
  allocas_from lo s /\ lookup_var root s = SOME (n2w p) /\ p < dimword(:256) /\
  p+32 <= s.vs_alloca_next /\ ptr_covers G tn root s 32 /\
  eval_operand value s = SOME w /\ op_taint tn value = {} ==>
  ?t tn'.
    t = (mstore p w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    tn' = step_taint (mk_inst a.cs_next_id MSTORE [Var root;value] []) s
       (mstore p w s) tn /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,G,tn')) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    mload p t = w /\ eval_operand (Var root) t = SOME (n2w p) /\
    (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==> mem_word_at p mem = w) /\
    typed_copy_state_frame a p 32 s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    tn'.t_var = tn.t_var /\ tn'.t_mem = tn.t_mem DIFF {i | p <= i /\ i < p+32} /\
    (!op. eval_operand op t = eval_operand op s /\ op_taint tn' op = op_taint tn op) /\
    (!x n. ptr_covers G tn x s n ==> ptr_covers G tn' x t n)
Proof
  rpt strip_tac >> drule_all emit_void_fetch_boundary >> strip_tac >>
  qexistsl_tac [`mstore p w s with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_taint (mk_inst a.cs_next_id MSTORE [Var root;value] []) s (mstore p w s) tn`] >>
  simp[] >> conj_tac >- suspend "path" >>
  `w2n (n2w p:256 word) = p` by simp[] >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`ARB`,`G`,`a.cs_next_id`] strip_assume_tac) >>
  ` (step_taint (mk_inst a.cs_next_id MSTORE [Var root;value] []) s (mstore p w s) tn).t_imm = tn.t_imm` by
    simp[step_taint_def, mk_inst_def, set_var_taint_def, store_taint_def,
      adopt_reset_def, step_writes_def, written_taint_def, imm_taint_def] >>
  `mload p (mstore p w s with vs_inst_idx := SUC s.vs_inst_idx) = w` by
    simp[mload_inst_idx, mload_mstore_same] >>
  `typed_copy_state_frame a p 32 s
     (mstore p w s with vs_inst_idx := SUC s.vs_inst_idx)` by suspend "frame" >>
  `!mem. mem_agree_outside
     (step_taint (mk_inst a.cs_next_id MSTORE [Var root;value] []) s (mstore p w s) tn).t_mem
     (mstore p w s).vs_memory mem ==> mem_word_at p mem = w` by suspend "robust" >>
  gvs[] >>
  gvs[mload_inst_idx, mload_mstore_same, mstore_def, lookup_var_def] >>
  simp[op_taint_def, ptr_covers_def, lookup_var_def] >>
  simp[eval_operand_def, op_taint_def, lookup_var_def]
QED

Resume abi_encode_finish_store_origin[path]:
  gen_tac >>
  `w2n (n2w p:256 word) = p` by simp[] >>
  drule_at (Pat `ptr_covers _ _ _ _ _`) abi_encode_mstore_origin_path >>
  simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def,
    codegenRelTheory.fixed_source_write_range_def,
    memSafeRunTheory.inst_dload_in_section_def, mk_inst_def, eval_operand_def] >>
  metis_tac[]
QED

Resume abi_encode_finish_store_origin[robust]:
  rpt strip_tac >> (metis_tac[mstore_raw_robust_word])
QED

Resume abi_encode_finish_store_origin[frame]:
  rewrite_tac[typed_copy_state_frame_def] >> conj_tac
  >- simp[venom_state_component_equality, mstore_def] >>
  conj_tac >- simp[lookup_var_def, mstore_def] >>
  simp[typed_copy_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> decide_tac) >>
  simp[mstore_memory_nondecreasing]
QED

Finalise abi_encode_finish_store_origin

Theorem abi_encode_finish_origin:
  abi_builtin_encode_finish (Var root) lenop k a = ((),b) /\
  fn_has_code a b func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  allocas_from lo s /\ alloca_inv s /\
  lookup_var root s = SOME (n2w p) /\ p < dimword(:256) /\ lo <= p /\
  p+32 <= s.vs_alloca_next /\ ptr_covers G tn root s 32 /\
  eval_operand lenop s = SOME (n2w len) /\ op_taint tn lenop = {} /\
  not_fresh_at a root /\ (!x. lenop = Var x ==> not_fresh_at a x) /\
  len+k < dimword(:256) ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,G',tn')) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    mload p t = n2w (len+k) /\
    eval_operand (Var root) t = SOME (n2w p) /\ ptr_covers G' tn' root t 32 /\
    (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
       mem_word_at p mem = n2w (len+k)) /\
    typed_copy_state_frame a p 32 s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    tn'.t_mem = tn.t_mem DIFF {i | p <= i /\ i < p+32} /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!op. (!x. op = Var x ==> not_fresh_at a x) ==>
       eval_operand op t = eval_operand op s /\
       op_taint tn' op = op_taint tn op /\ op_prov G' op = op_prov G op) /\
    (!x n. not_fresh_at a x /\ ptr_covers G tn x s n ==> ptr_covers G' tn' x t n) /\
    (fn_inst_ids_distinct func /\ alloca_history func s ==> alloca_history func t) /\
    (!D d ce cx es origin G0 tn0 s0.
       ghost_inv_at D lo d ce cx es G tn s /\
       ghost_kept_at lo ce es origin G0 tn0 s0 G tn /\
       local_ptrs_rel func ce es.scopes s /\
       (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at a x) /\
       (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
       (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
       (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at a x) /\
       (!x. not_fresh_at origin x ==> not_fresh_at a x) /\
       (!name off sz. local_region ce es.scopes s name off sz ==>
          regions_disjoint p 32 off sz) ==>
       ghost_inv_at D lo d ce cx es G' tn' t /\
       ghost_kept_at lo ce es origin G0 tn0 s0 G' tn')
Proof
  strip_tac >> Cases_on `0 < k`
  >- suspend "positive" >>
  `k = 0` by decide_tac >> gvs[abi_builtin_encode_finish_def] >>
  drule_all abi_encode_finish_store_origin >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`G`,`tn'`] >> gvs[] >>
  conj_tac >- suspend "zero_operands" >>
  conj_tac >- metis_tac[body_full_path_alloca_history] >>
  suspend "zero_ghost"
QED

Resume abi_encode_finish_origin[zero_operands]:
  simp[lookup_var_def, mstore_def]
QED

Resume abi_encode_finish_origin[zero_ghost]:
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `lookup_var _ _ = _`) abi_encode_mstore_frame_at >>
  simp[] >> metis_tac[]
QED

Resume abi_encode_finish_origin[positive]:
  gvs[abi_builtin_encode_finish_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [lenop;Lit (n2w k)] a = (dst,mid)` >>
  `cs_extends a mid /\ cs_extends mid b` by
    (gvs[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def,
       compileEnvTheory.cs_extends_def]) >>
  `fn_has_code a mid func /\ fn_has_code mid b func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all abi_encode_finish_add_origin >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choose_then `q` (qx_choose_then `u` (qx_choose_then `G1`
      (qx_choose_then `tn1` strip_assume_tac))))) >>
  suspend "positive_after_add"
QED

Resume abi_encode_finish_origin[positive_after_add]:
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\ allocas_from lo u` by
    (gvs[update_var_def, allocas_from_def] >> (gvs[update_var_def, allocas_from_def])) >>
  `lookup_var root u = SOME (n2w p) /\ ptr_covers G1 tn1 root u 32` by
    (simp[ptr_covers_def] >> gvs[ptr_covers_def] >> metis_tac[]) >>
  `p+32 <= u.vs_alloca_next` by simp[] >>
  drule_all abi_encode_finish_store_origin >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `t` (qx_choose_then `tn2` strip_assume_tac))) >>
  qexistsl_tac [`t`,`G1`,`tn2`] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK t,G1,tn2)` by
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`G1`,`u`,`tn1`] >> simp[]) >>
  simp[GSYM word_add_n2w, WORD_ADD_COMM,
    IgnAsm `u = _`, IgnAsm `t = _`, IgnAsm `tn2 = _`] >>
  conj_tac >- suspend "positive_frame" >>
  conj_tac >- suspend "positive_vars" >>
  conj_tac >- suspend "positive_operands" >>
  conj_tac >- suspend "positive_covers" >>
  conj_tac >- metis_tac[body_full_path_alloca_history] >>
  suspend "positive_ghost"
QED

Resume abi_encode_finish_origin[positive_frame]:
  gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
  conj_tac >- gvs[venom_state_component_equality, update_var_def, mstore_def] >>
  conj_tac >- (rpt strip_tac >>
    simp[lookup_var_def, mstore_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  gvs[update_var_def] >> metis_tac[]
QED

Resume abi_encode_finish_origin[positive_vars]:
  rpt strip_tac >> gvs[lookup_var_def, mstore_def, update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Resume abi_encode_finish_origin[positive_operands]:
  gen_tac >> Cases_on `op` >>
  simp[eval_operand_def, op_prov_def, op_taint_def] >>
  strip_tac >> metis_tac[eval_operand_def, op_taint_def]
QED

Resume abi_encode_finish_origin[positive_covers]:
  rpt strip_tac >> gvs[ptr_covers_def] >> metis_tac[]
QED

Resume abi_encode_finish_origin[positive_ghost]:
  rpt gen_tac >> strip_tac >>
  `ghost_inv_at D lo d ce cx es G1 tn1 u` by suspend "add_inv" >>
  `ghost_kept_at lo ce es origin G0 tn0 s0 G1 tn1` by
    (gvs[ghost_kept_at_def] >> metis_tac[]) >>
  `local_ptrs_rel func ce es.scopes u` by
    (simp[localPtrsPropsTheory.local_ptrs_rel_inst_idx] >>
     irule localPtrsPropsTheory.local_ptrs_rel_update_var >>
     simp[not_scope_ptr_def] >> metis_tac[]) >>
  `!name off sz. local_region ce es.scopes u name off sz ==>
      regions_disjoint p 32 off sz` by
    (gvs[local_region_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  qpat_assum `lookup_var root u = _`
    (mp_then Any mp_tac abi_encode_mstore_frame_at) >>
  disch_then (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
  disch_then (qspec_then `mid.cs_next_id` mp_tac) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  simp[IgnAsm `u = _`, IgnAsm `t = _`, IgnAsm `tn2 = _`] >>
  strip_tac >> gvs[] >> first_x_assum drule >> simp[]
QED

Resume abi_encode_finish_origin[add_inv]:
  `!x n. x <> q /\ ptr_covers G tn x s n ==> ptr_covers G1 tn1 x u n` by
    (rpt strip_tac >>
     qpat_x_assum `!x. x <> q ==> _` (qspec_then `x` mp_tac) >>
     simp[IgnAsm `u = _`] >> strip_tac >>
     gvs[ptr_covers_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_inv_at_def] >> strip_tac >>
  rewrite_tac[ghost_inv_at_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `p' <> q` by metis_tac[] >>
      conj_tac >- metis_tac[] >>
      rpt gen_tac >> strip_tac >>
      `lookup_var p' s = SOME w` by metis_tac[lookup_var_def] >>
      first_x_assum drule_all >> gvs[]) >>
  conj_tac
  >- (Cases_on `d` >> simp[return_buf_ptr_def, IgnAsm `u = _`] >>
      PairCases_on `x` >>
      fs[return_buf_ptr_def, IgnAsm `u = _`] >>
      metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- gvs[stor_taint_ok_at_def, update_var_def] >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[lookup_var_def]) >>
  conj_tac >- metis_tac[] >>
  gvs[update_var_def, allocas_from_def] >> metis_tac[]
QED

Finalise abi_encode_finish_origin
