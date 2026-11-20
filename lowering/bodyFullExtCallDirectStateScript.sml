Theory bodyFullExtCallDirectState
Ancestors
  bodyFullExtCallDirectPhase bodyFullExtCallDirectUnwrap bodyFullExtCallDirectStart
  abiEncodeValuesPhases abiEncoderWindowPhase
  abiEncoderWindowContract stateRelProj
  exprLoweringProps exprSimHypsDefs fragGasOriginPtr
  bodyPtrDefs loweringPosts loweringStateRelDefs context compileEnv
  vyperStorageFootprint venomState venomInst ptrDiscipline
  finite_map pred_set list arithmetic words pair freshWrites exprSimWordArgs wordArgsPtr
Libs horizonTypeLib

Definition extcall_direct_state_def:
  extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst selector a u Gu tu <=>
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee u /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee Gu tu u) /\
    wb_frame ce ee ee se s u /\ ghost_kept_at lo ce ee se G tn s Gu tu /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\
    u.vs_inst_idx = LENGTH a.cs_current_insts /\
    se.cs_next_var <= a.cs_next_var /\ se.cs_next_id <= shared /\ shared < a.cs_next_id /\
    not_fresh_at a root /\ not_fresh_at a dst /\
    eval_operand (Var root) u = SOME (n2w pbase) /\ ptr_covers Gu tu root u capacity /\
    eval_operand (Var dst) u = SOME (n2w (pbase+32)) /\
    ptr_covers Gu tu dst u (capacity-32) /\
    FLOOKUP u.vs_allocas shared = SOME (pbase,capacity) /\
    read_memory (pbase+28) 4 u = selector /\
    (!i. pbase+28 <= i /\ i < pbase+32 ==> i NOTIN tu.t_mem)
End

Theorem extcall_direct_state_resources:
  extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst selector a u Gu tu /\
  (?H. valid_horizon cx st0 H ee.storage_trace) ==>
  alloca_inv u /\ alloca_room ctx func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next /\
  ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts
Proof
  simp_tac bool_ss [extcall_direct_state_def] >> strip_tac >>
  metis_tac[stmt_state_rel_local_ptrs_alloca, stmt_state_rel_alloca_room, ghost_inv_at_def]
QED

(* Only writes into the payload and the designated private allocations
   are allowed between the compiler's two cuts. *)
Theorem extcall_direct_state_phase:
  extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst selector a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\ 32 <= capacity /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  ci_mono a c /\ window_phase ctx func a c ids outs u v /\
  abi_encode_exec_frame func u v /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK v,Gv,tv)) /\
  (!x. not_fresh_at a x ==>
    FLOOKUP Gv x = FLOOKUP Gu x /\ op_taint tv (Var x) = op_taint tu (Var x)) /\
  tv.t_stor = tu.t_stor /\ tv.t_trans = tu.t_trans /\ tv.t_imm = tu.t_imm /\
  shared NOTIN ids /\ (!aid. aid IN ids ==> se.cs_next_id <= aid) /\
  EVERY (\(p,n). pbase+32 <= p /\ p+n <= pbase+capacity) outs /\
  (!aid. aid IN shared INSERT ids ==>
    ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x) /\
  (!i. EVERY (\(p,n). i < p \/ p+n <= i) outs /\
    (!aid p n. aid IN ids /\ FLOOKUP v.vs_allocas aid = SOME (p,n) ==>
      i < p \/ p+n <= i) /\ i IN tv.t_mem ==> i IN tu.t_mem) ==>
  extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst selector c v Gv tv
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all extcall_direct_state_resources >> strip_tac >>
  qpat_x_assum `extcall_direct_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [extcall_direct_state_def]) >>
  `EVERY (\(p,n). pbase <= p /\ p+n <= pbase+capacity) outs /\
    EVERY (\(p,n). pbase+32 <= p) outs` by
    (qpat_assum `EVERY _ outs` mp_tac >>
     simp_tac (srw_ss()) [EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
     res_tac >> decide_tac) >>
  mp_tac (Q.INST [`front` |-> `se`,`st` |-> `a`,`en` |-> `c`,`s` |-> `u`,
    `t` |-> `v`,`b` |-> `pbase`,`cap` |-> `capacity`,`G` |-> `Gu`,`G'` |-> `Gv`,
    `tn` |-> `tu`,`tn'` |-> `tv`] extcall_direct_row_phase) >>
  impl_tac >- asm_rewrite_tac[] >>
  strip_tac >>
  mp_tac (Q.INST [`st` |-> `a`,`en` |-> `c`,`s` |-> `u`,`t` |-> `v`,
    `b` |-> `pbase`,`cap` |-> `capacity`,`tn` |-> `tu`,`tn'` |-> `tv`]
    extcall_direct_selector_frame) >>
  impl_tac >- asm_rewrite_tac[] >>
  strip_tac >>
  `!x w n. not_fresh_at a x /\ eval_operand (Var x) u = SOME w /\
    ptr_covers Gu tu x u n ==> eval_operand (Var x) v = SOME w /\ ptr_covers Gv tv x v n` by
    (rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     irule abi_encode_values_pointer_frame >>
     qpat_assum `window_phase ctx func a c ids outs u v` (irule_at Any) >>
     qexistsl_tac [`tu`,`Gu`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `!x w n. not_fresh_at a x /\ _ ==> eval_operand (Var x) v = _ /\ _`
    (fn th => MAP_EVERY (fn args => mp_tac (Q.SPECL args th) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac)
       [[`root`,`n2w pbase`,`capacity`],[`dst`,`n2w (pbase+32)`,`capacity-32`]]) >>
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s`
    (drule_then assume_tac) >>
  `wb_frame ce ee ee se s v /\ ghost_kept_at lo ce ee se G tn s Gv tv` by
    (conj_tac
     >- (irule (horizonTypeLib.at_horizon_named "H" exprSimWordArgsTheory.wb_frame_trans) >>
         qpat_assum `stmt_state_rel hz ctx func ce cx ee s` (irule_at Any) >>
         qpat_assum `wb_frame ce ee ee se s u` (irule_at Any) >>
         qpat_assum `wb_frame ce ee ee se u v` (irule_at Any) >> simp[]) >>
     irule (horizonTypeLib.at_horizon_named "H" wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     qpat_assum `stmt_state_rel hz ctx func ce cx ee s` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee se s u` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee se G tn s Gu tu` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee se Gu tu u Gv tv` (irule_at Any) >> simp[]) >>
  PURE_REWRITE_TAC [extcall_direct_state_def] >> asm_rewrite_tac[] >>
  qpat_assum `ci_mono a c` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  `not_fresh_at c root /\ not_fresh_at c dst` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem extcall_direct_state_unwrap:
  extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst selector a u Gu tu /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  local_ptrs_reserved ce se /\ 32 <= capacity /\ ci_mono a c /\
  (!name p n. local_region ce ee.scopes u name p n ==>
    pbase+capacity <= p \/ p+n <= pbase) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee v /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee Gv tv v) /\
  wb_frame ce ee ee a u v /\ ghost_kept_at lo ce ee a Gu tu u Gv tv /\
  (!x. not_fresh_at a x ==>
    lookup_var x v = lookup_var x u /\ FLOOKUP Gv x = FLOOKUP Gu x /\
    op_taint tv (Var x) = op_taint tu (Var x)) /\
  alloca_history func v /\ u.vs_alloca_next <= v.vs_alloca_next /\
  ~v.vs_halted /\ v.vs_current_bb = c.cs_current_bb /\
  v.vs_inst_idx = LENGTH c.cs_current_insts ==>
  extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst selector c v Gv tv
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `extcall_direct_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [extcall_direct_state_def]) >>
  mp_tac (Q.INST [`st` |-> `a`,`s` |-> `u`,`t` |-> `v`,`id` |-> `shared`,
    `b` |-> `pbase`,`sz` |-> `capacity`,`q` |-> `pbase+28`,`len` |-> `4`,
    `G` |-> `Gu`,`G'` |-> `Gv`,`tn` |-> `tu`,`tn'` |-> `tv`]
    (INST_TYPE [alpha |-> ``:num # num``] abi_encode_values_unwrap_window)) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  strip_tac >>
  `read_memory (pbase+28) 4 v = selector` by
    (PURE_REWRITE_TAC [memoryReadPropsTheory.read_memory_eq_mem_bytes_at] >>
     qpat_assum `mem_bytes_at (pbase+28) 4 v.vs_memory = _`
       (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `read_memory (pbase+28) 4 u = selector`
       (ACCEPT_TAC o REWRITE_RULE [memoryReadPropsTheory.read_memory_eq_mem_bytes_at])) >>
  `!i. pbase+28 <= i /\ i < pbase+32 ==> i NOTIN tv.t_mem` by
    (gen_tac >> disch_tac >>
     `i < pbase+28+4` by decide_tac >> metis_tac[]) >>
  `s.vs_alloca_next <= v.vs_alloca_next /\ se.cs_next_id <= a.cs_next_id` by decide_tac >>
  `!x w n. not_fresh_at a x /\ eval_operand (Var x) u = SOME w /\
    ptr_covers Gu tu x u n ==> eval_operand (Var x) v = SOME w /\ ptr_covers Gv tv x v n` by
    (rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     mp_tac (Q.INST [`st` |-> `a`, `p` |-> `x`, `s` |-> `u`, `t` |-> `v`,
       `G` |-> `Gu`, `G'` |-> `Gv`, `tn` |-> `tu`, `tn'` |-> `tv`]
       extcall_direct_unwrap_pointer) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  qpat_x_assum `!x w n. not_fresh_at a x /\ _ ==> eval_operand (Var x) v = _ /\ _`
    (fn th => MAP_EVERY (fn args => mp_tac (Q.SPECL args th) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac)
       [[`root`,`n2w pbase`,`capacity`],[`dst`,`n2w (pbase+32)`,`capacity-32`]]) >>
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s`
    (drule_then assume_tac) >>
  `wb_frame ce ee ee se s v /\ ghost_kept_at lo ce ee se G tn s Gv tv` by
    (conj_tac
     >- (irule (horizonTypeLib.at_horizon_named "H" exprSimWordArgsTheory.wb_frame_trans) >>
         qpat_assum `stmt_state_rel hz ctx func ce cx ee s` (irule_at Any) >>
         qpat_assum `wb_frame ce ee ee se s u` (irule_at Any) >>
         qpat_assum `wb_frame ce ee ee a u v` (irule_at Any) >> simp[]) >>
     irule (horizonTypeLib.at_horizon_named "H" wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     qpat_assum `stmt_state_rel hz ctx func ce cx ee s` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee se s u` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee se G tn s Gu tu` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee a Gu tu u Gv tv` (irule_at Any) >> simp[]) >>
  PURE_REWRITE_TAC [extcall_direct_state_def] >> asm_rewrite_tac[] >>
  qpat_assum `ci_mono a c` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  `not_fresh_at c root /\ not_fresh_at c dst` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem extcall_direct_state_arith:
  extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst selector a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\ 32 <= capacity /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  ci_mono a c /\ window_phase ctx func a c {} [] u v /\
  abi_encode_exec_frame func u v /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK v,Gv,tv)) /\
  (!x. not_fresh_at a x ==>
    FLOOKUP Gv x = FLOOKUP Gu x /\ op_taint tv (Var x) = op_taint tu (Var x)) /\
  tv.t_stor = tu.t_stor /\ tv.t_trans = tu.t_trans /\ tv.t_imm = tu.t_imm /\
  tv.t_mem = tu.t_mem ==>
  extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst selector c v Gv tv
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`ids` |-> `{}:num set`,`outs` |-> `[]:(num#num) list`]
    extcall_direct_state_phase) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [IN_INSERT] >> metis_tac[]) >>
  disch_then ACCEPT_TAC
QED
