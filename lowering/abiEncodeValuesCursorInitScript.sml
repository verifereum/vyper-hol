Theory abiEncodeValuesCursorInit
Ancestors
  loweringShapeRules loweringShapeDefs
  abiEncodeValuesCode abiEncoderWindowJointPhases abiEncoderWindowPhase
  abiEncoderRegisteredEffect abiEncoderWindowContract abiEncoderTuple
  exprSimAbiEncodeExecFrame fragGasOriginPtr fragExec exprLoweringProps
  allocaSiteResource entryDecodeStructure emitHelperProps emitHelper compileEnv ptrDiscipline
  valueEncodingDefs contractABI venomState venomMemDefs venomInst
  words finite_map pred_set list arithmetic

(* The destination and cursor have different registered allocation IDs.
   Initialization touches the cursor alone, even when all rows are static. *)
Theorem abi_encode_values_cursor_init_edges:
  emit_op ALLOCA [Lit 32w] st = (cursor,mid) /\
  emit_void MSTORE [cursor; Lit (n2w hl)] mid = ((),en) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) /\
  FLOOKUP s.vs_allocas dst_site = SOME (dst_base,capacity) /\ dst_site < st.cs_next_id /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
     s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t slot p G' tn'.
    (?v bb a m.
      v.vs_inst_idx = SUC s.vs_inst_idx /\
      LENGTH en.cs_current_insts = s.vs_inst_idx + 2 /\
      lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      lookup_block v.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME a /\
      get_instruction bb v.vs_inst_idx = SOME m /\
      a.inst_id = st.cs_next_id /\ m.inst_id = mid.cs_next_id /\
      fragGasOrigin$gas_origin_edge F explicit ctx func s [] (OK v) /\
      fragGasOrigin$gas_origin_edge F explicit ctx func v [] (OK t)) /\
    cursor = Var p /\ not_fresh_at en p /\
    eval_operand cursor t = SOME (n2w slot) /\ ptr_covers G' tn' p t 32 /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (slot,32) /\ st.cs_next_id < en.cs_next_id /\
    FLOOKUP t.vs_allocas dst_site = SOME (dst_base,capacity) /\
    venomMemDefs$regions_disjoint (dst_base,capacity) (slot,32) /\
    slot + 32 <= t.vs_alloca_next /\ mem_word_at slot t.vs_memory = n2w hl /\
    (!i. slot <= i /\ i < slot + 32 ==> i NOTIN tn'.t_mem) /\
    window_phase ctx func st en {st.cs_next_id} [] s t /\ abi_encode_exec_frame func s t /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size func t <= w2n t.vs_initial_fmp) /\
    (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem DIFF {i | slot <= i /\ i < slot + 32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >>
  `eval_operand (Lit (n2w hl)) s = SOME (n2w hl) /\
   op_taint tn (Lit (n2w hl)) = {} /\
   (!x. Lit (n2w hl) = Var x ==> not_fresh_at st x)` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all window_cursor_init_joint_edges >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choose_then `t` (qx_choose_then `slot`
      (qx_choose_then `p` (qx_choose_then `G'`
        (qx_choose_then `tn'` (CONJUNCTS_THEN2 assume_tac strip_assume_tac))))))) >>
  `st.cs_next_id < en.cs_next_id` by
    (drule emit_op_next_id >> drule emit_void_next_id >> simp[]) >>
  `alloca_inv t` by metis_tac[window_phase_resources] >>
  `FLOOKUP t.vs_allocas dst_site = SOME (dst_base,capacity)` by
    metis_tac[window_phase_effect, abi_encoder_registered_effect_allocated] >>
  `dst_site <> st.cs_next_id` by decide_tac >>
  `venomMemDefs$regions_disjoint (dst_base,capacity) (slot,32)` by
    metis_tac[alloca_site_registered_disjoint] >>
  `!x. not_fresh_at st x ==> p <> x` by
    (drule emit_op_facts >> strip_tac >> qpat_x_assum `cursor = Var p` (fn th => fs[th]) >> metis_tac[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size func t <= w2n t.vs_initial_fmp)` by
    metis_tac[window_exec_frame_alloca_budget] >>
  qexistsl_tac [`t`,`slot`,`p`,`G'`,`tn'`] >>
  asm_rewrite_tac[] >> simp[op_taint_def, FLOOKUP_UPDATE] >>
  metis_tac[window_phase_vars]
QED

Theorem abi_encode_values_cursor_init:
  emit_op ALLOCA [Lit 32w] st = (cursor,mid) /\
  emit_void MSTORE [cursor; Lit (n2w hl)] mid = ((),en) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) /\
  FLOOKUP s.vs_allocas dst_site = SOME (dst_base,capacity) /\ dst_site < st.cs_next_id /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
     s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t slot p G' tn'.
    cursor = Var p /\ not_fresh_at en p /\
    eval_operand cursor t = SOME (n2w slot) /\ ptr_covers G' tn' p t 32 /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (slot,32) /\ st.cs_next_id < en.cs_next_id /\
    FLOOKUP t.vs_allocas dst_site = SOME (dst_base,capacity) /\
    venomMemDefs$regions_disjoint (dst_base,capacity) (slot,32) /\
    slot + 32 <= t.vs_alloca_next /\ mem_word_at slot t.vs_memory = n2w hl /\
    (!i. slot <= i /\ i < slot + 32 ==> i NOTIN tn'.t_mem) /\
    window_phase ctx func st en {st.cs_next_id} [] s t /\ abi_encode_exec_frame func s t /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size func t <= w2n t.vs_initial_fmp) /\
    (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem DIFF {i | slot <= i /\ i < slot + 32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >> drule_all abi_encode_values_cursor_init_edges >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choose_then `t` (qx_choose_then `slot`
      (qx_choose_then `p` (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac)))))) >>
  qexistsl_tac [`t`,`slot`,`p`,`G'`,`tn'`] >> asm_rewrite_tac[]
QED
