(* Runtime materialization at the reached LocCode operand. *)
Theory bodyCopyRuntimeRhsRunMods
Ancestors
  bodyFullUnwrapCodeRuntimeRun exprPtrUnwrapCodeCopyShape exprPtrUnwrapCodeEdges
  exprPtrCodeCopyEndpoint exprPtrUnwrapAllocSemantic exprPtrUnwrapRetained
  fragGasOriginPtrDead ghostPcTransportPtr allocasBelowFmpUpdatesProps
  immutableCopyExecution valueEncodingDefs valueEncodingProps
  exprSimCopy exprSimStorageCopy bufferAllocationExecution venomState
  exprPtrUnwrapAllocSeparation exprPtrUnwrapAllocEntry exprPtrUnwrapAllocationFrame
  exprLoweringProps compileEnv ptrDiscipline loweringStateRelDefs exprPtrUnwrapAllocation
  bodyPtrDefs entrySinkExtraction arithmetic loweringHalt venomInst exprPtrUnwrapFrames
  abiDecodeStaticProps[qualified] exprSimAbiEncodeMemoryLength[qualified] venomExecSemantics

Theorem runtime_copy_representation[local]:
  val_in_memory rt v (w2n src) a.vs_data_section /\ val_wf rt v /\
  w2n src + type_memory_size rt < dimword (:256) /\
  w2n dst + type_memory_size rt < dimword (:256) /\
  z.vs_memory = (immutable_transfers F F src dst (type_slot_size rt) 0 a).vs_memory ==>
  val_in_memory rt v (w2n dst) z.vs_memory
Proof
  strip_tac >> irule valueEncodingPropsTheory.val_in_memory_relocate >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`a.vs_data_section`, `type_memory_size rt`, `w2n src`] >> simp[] >>
  Cases_on `type_slot_size rt = 0`
  >- simp[type_memory_size_slots, mem_bytes_at_def] >>
  `immutable_transfers F F src dst (type_slot_size rt) 0 a =
   write_memory_with_expansion (w2n dst)
     (mem_bytes_at (w2n src) (type_memory_size rt) a.vs_data_section) a` by
    (qspecl_then [`type_slot_size rt`, `w2n src`, `w2n dst`, `0`, `a`] mp_tac
       immutable_runtime_transfers_snapshot >>
     simp[type_memory_size_slots, mem_bytes_at_def] >>
     gvs[type_memory_size_slots]) >>
  simp[] >>
  qspecl_then [`w2n dst`,
    `mem_bytes_at (w2n src) (type_memory_size rt) a.vs_data_section`, `a`] mp_tac
    write_memory_mem_bytes_at_same >> simp[]
QED

Theorem runtime_copy_allocation_frame[local]:
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel H ctx func ce cx ee s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ nb < dimword (:256) /\
  buf.buf_operand = Var root /\
  (dst:bytes32) = n2w (buffer_allocation_base s sm.cs_next_id) /\
  u = update_var root dst (buffer_allocation_fields s sm.cs_next_id nb) /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\ copy_runtime_frame mid a sc z /\
  Gm = step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
  (!x. not_fresh_at mid x ==> FLOOKUP Gf x = FLOOKUP Gm x) /\
  lookup_var root a = SOME dst /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  eval_operand (Var root) z = SOME dst /\
  FLOOKUP Gf root = SOME (w2n dst,nb) /\
  FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dst,nb) /\
  (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
     FLOOKUP z.vs_allocas id = SOME entry) /\
  (!id b len. id < sm.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (b,len) ==>
     regions_disjoint (w2n dst) nb b len) /\
  (!name b len. local_region ce ee.scopes s name b len ==>
     w2n dst + nb <= b \/ b+len <= w2n dst) /\
  a.vs_memory = s.vs_memory /\ a.vs_data_section = s.vs_data_section /\
  z.vs_data_section = s.vs_data_section /\
  z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
  z.vs_call_ctx = s.vs_call_ctx /\ z.vs_immutables = s.vs_immutables /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z)
Proof
  strip_tac >>
  `buffer_allocation_base s sm.cs_next_id < dimword (:256)` by
    (drule_all unwrap_alloc_site_bound >> decide_tac) >>
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  `not_fresh_at mid root` by
    (drule_all (Q.INST [`src` |-> `Lit 0w`] allocated_copy_operands_old
       |> SIMP_RULE (srw_ss()) [copy_old_operand_def]) >> simp[]) >>
  `copy_static z = copy_static a /\ lookup_var root z = SOME dst` by
    fs[copy_runtime_frame_def] >>
  `z.vs_allocas = a.vs_allocas /\ z.vs_data_section = a.vs_data_section /\
   z.vs_accounts = a.vs_accounts /\ z.vs_transient = a.vs_transient /\
   z.vs_call_ctx = a.vs_call_ctx` by (drule copy_static_fields >> simp[]) >>
  `z.vs_immutables = a.vs_immutables /\ z.vs_initial_fmp = a.vs_initial_fmp /\
   z.vs_fmp = a.vs_fmp` by
    (qpat_x_assum `copy_static _ = _` (mp_tac o Q.AP_TERM
       `\st. (st.vs_immutables,st.vs_initial_fmp,st.vs_fmp)`) >> simp[copy_static_def]) >>
  `a.vs_memory = s.vs_memory /\ a.vs_data_section = s.vs_data_section /\
   a.vs_accounts = s.vs_accounts /\ a.vs_transient = s.vs_transient /\
   a.vs_call_ctx = s.vs_call_ctx /\ a.vs_immutables = s.vs_immutables` by
    (simp[buffer_allocation_fields_def, update_var_def] >>
     Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >> simp[]) >>
  `w2n dst = buffer_allocation_base s sm.cs_next_id` by
    simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `FLOOKUP Gf root = SOME (w2n dst,nb)` by
    (drule fragExecPtrTheory.step_prov_alloca >>
     disch_then (qspecl_then [`PG`,`G`,`Lit (n2w nb)`,`root`] mp_tac) >>
     simp[finite_mapTheory.FLOOKUP_UPDATE]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (strip_tac >> `allocas_below_fmp u` by (drule_all unwrap_alloc_below_fmp >> simp[]) >>
     `allocas_below_fmp a` by
       (qpat_x_assum `a = _` SUBST1_TAC >> simp[allocas_below_fmp_updates]) >>
     `allocas_below_fmp z <=> allocas_below_fmp a` by
       (irule allocas_below_fmp_fields >> asm_rewrite_tac[]) >>
     fs[]) >>
  `z.vs_allocas = u.vs_allocas` by fs[] >>
  qpat_x_assum `a = _` kall_tac >>
  qpat_x_assum `u = update_var _ _ _` kall_tac >>
  qpat_x_assum `dst = _` kall_tac >>
  qpat_x_assum `w2n dst = _` (assume_tac o SYM) >>
  simp[eval_operand_def] >> conj_tac
  >- (rpt strip_tac >> qpat_assum `!id b len. _ ==> regions_disjoint _ _ _ _`
       (drule_all_then ACCEPT_TAC)) >>
  rpt strip_tac >> drule_all unwrap_alloc_local_separation >> simp[]
QED

Theorem runtime_copy_taint[local]:
  out = mid DIFF {i | b <= i /\ i < b+n} /\
  (!i. i < b \/ b+n <= i ==> (i IN out <=> i IN input)) ==>
  out = input DIFF {i | b <= i /\ i < b+n}
Proof
  strip_tac >> simp[pred_setTheory.EXTENSION] >> gen_tac >>
  rename1 `i IN mid /\ _ <=> _` >>
  Cases_on `b <= i /\ i < b+n` >> simp[] >>
  qpat_x_assum `!j. _ ==> (j IN out <=> _)` (qspec_then `i` mp_tac) >>
  `i < b \/ b+n <= i` by decide_tac >> simp[]
QED

(* No linked lookup is needed once the reached operand has been related
   to the data section. This path reads neither storage nor dead memory. *)
Theorem copy_runtime_rhs_endpoint_mods:
  ~ce.ce_is_ctor /\ p.ptr_location = LocCode /\ ~is_word_type ty /\
  unwrap_value ce (LocatedValue ty p) sm = (op,sc) /\
  type_memory_bytes ce ty = type_memory_size rt /\
  fn_has_code sm sc func /\ fn_inst_ids_distinct func /\
  stmt_state_rel H ctx func ce cx ee s /\ local_ptrs_reserved ce sm /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  eval_operand p.ptr_operand s = SOME src /\ op_taint tn p.ptr_operand = {} /\
  val_wf rt v /\ val_in_memory rt v (w2n src) s.vs_data_section /\
  w2n src + type_memory_size rt <= LENGTH s.vs_data_section /\
  w2n src + type_memory_size rt < dimword (:256) ==>
  ?z Gf tf root dst u.
    op = Var root /\ eval_operand op z = SOME dst /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ allocas_from lo z /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    lo <= w2n dst /\ w2n dst + type_memory_size rt <= z.vs_alloca_next /\
    w2n dst + type_memory_size rt < dimword (:256) /\
    sm.cs_next_id < sc.cs_next_id /\
    FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dst,type_memory_size rt) /\
    FLOOKUP Gf root = SOME (w2n dst,type_memory_size rt) /\
    ptr_covers Gf tf root z (type_memory_size rt) /\
    val_in_memory rt v (w2n dst) z.vs_memory /\
    tf.t_mem = tn.t_mem DIFF {i | w2n dst <= i /\ i < w2n dst+type_memory_size rt} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
       FLOOKUP z.vs_allocas id = SOME entry) /\
    (!id b len. id < sm.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (b,len) ==>
       regions_disjoint (w2n dst) (type_memory_size rt) b len) /\
    (!name b len. local_region ce ee.scopes s name b len ==>
       w2n dst + type_memory_size rt <= b \/ b+len <= w2n dst) /\
    (!off len. off+len <= w2n dst \/ w2n dst+type_memory_size rt <= off ==>
       mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    z.vs_data_section = s.vs_data_section /\ z.vs_accounts = s.vs_accounts /\
    z.vs_transient = s.vs_transient /\ z.vs_call_ctx = s.vs_call_ctx /\
    z.vs_immutables = s.vs_immutables /\
    root = STRING #"%" (toString sm.cs_next_var) /\
    MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [root])
      (fn_insts func) /\
    exec_alloca (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [root])
      s (n2w (type_memory_size rt) : bytes32) = OK u /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n dst,type_memory_size rt) /\
    copy_static z = copy_static u /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    sm.cs_next_var < sc.cs_next_var /\
    (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==>
      val_in_memory rt v (w2n dst) mem)
Proof
  strip_tac >>
  `compile_ensure_in_memory p.ptr_operand LocCode (type_memory_size rt)
     ((type_memory_size rt + 31) DIV 32) F ce.ce_imm_alloca sm = (op,sc)` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     simp[unwrap_runtime_code_route]) >>
  qabbrev_tac `nb = type_memory_size rt` >>
  `(nb + 31) DIV 32 = type_slot_size rt` by
    simp[Abbr `nb`, type_memory_size_slots, arithmeticTheory.ADD_DIV_ADD_DIV] >>
  drule_all ensure_runtime_code_layout >> strip_tac >>
  qpat_assum `(nb + 31) DIV 32 = _` (fn th =>
    qpat_x_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`
      (assume_tac o REWRITE_RULE [th])) >>
  `nb = 32 * type_slot_size rt` by simp[Abbr `nb`, type_memory_size_slots] >>
  `nb < dimword (:256) /\ w2n src + 32 * type_slot_size rt < dimword (:256) /\
   w2n src + 32 * type_slot_size rt <= LENGTH s.vs_data_section` by decide_tac >>
  drule_all runtime_code_copy_origin_execution >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`,
    `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
    strip_assume_tac) >>
  rename1 `copy_runtime_frame mid a sc z` >>
  rename1 `lookup_var root a = SOME dst` >>
  suspend "physical"
QED

Resume copy_runtime_rhs_endpoint_mods[physical]:
  qpat_assum `dst = _` (fn th =>
    qpat_x_assum `u = update_var _ _ _` (assume_tac o REWRITE_RULE [GSYM th])) >>
  `!x. not_fresh_at mid x ==> FLOOKUP HG x = FLOOKUP Gm x` by simp[] >>
  drule_all runtime_copy_allocation_frame >> strip_tac >>
  `copy_old_operand mid p.ptr_operand /\ copy_old_operand mid (Var root)` by
    (drule_all allocated_copy_operands_old >> simp[copy_old_operand_def]) >>
  `!x. p.ptr_operand = Var x ==> x <> root` by
    (rpt strip_tac >> drule_all unwrap_alloc_old_operand_distinct >> simp[]) >>
  `eval_operand p.ptr_operand a = SOME src` by
    (drule_all unwrap_alloc_operand_frame >> simp[]) >>
  `eval_operand (Var root) a = SOME dst` by simp[eval_operand_def] >>
  qpat_assum `buf.buf_operand = _` (fn th =>
    qpat_x_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`
      (assume_tac o REWRITE_RULE [th])) >>
  drule_all exprPtrCodeCopyPostTheory.code_copy_same_endpoint_memory >> strip_tac >>
  `val_in_memory rt v (w2n dst) z.vs_memory` by
    (irule runtime_copy_representation >>
     qpat_assum `Abbrev (nb = _)` (fn th =>
       pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
     asm_rewrite_tac[] >> qexistsl [`a`,`src`] >> asm_rewrite_tac[]) >>
  `lo <= w2n dst` by
    (qpat_assum `allocas_from lo z` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then drule >> simp[]) >>
  `sm.cs_next_id < sc.cs_next_id /\ sm.cs_next_var < sc.cs_next_var` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     `ci_mono mid sc` by
       (qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`
          (mp_tac o Q.AP_TERM `SND`) >>
        metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND]) >>
     fs[ci_mono_def]) >>
  `buffer_allocation_base s sm.cs_next_id < dimword (:256)` by
    (drule_all unwrap_alloc_site_bound >> decide_tac) >>
  `32 * type_slot_size rt <= nb` by decide_tac >>
  drule_all unwrap_code_exterior_frames >> strip_tac >>
  `tf.t_mem = tn.t_mem DIFF {i | w2n dst <= i /\ i < w2n dst+nb}` by
    (qpat_assum `nb = 32 * _` (fn th =>
       qpat_x_assum `tf.t_mem = _` (assume_tac o REWRITE_RULE [GSYM th])) >>
     drule_all runtime_copy_taint >> strip_tac >> first_assum ACCEPT_TAC) >>
  `tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
    fs[step_taint_def, mk_inst_def, adopt_reset_def, store_taint_def, imm_taint_def] >>
  suspend "certificate"
QED

Resume copy_runtime_rhs_endpoint_mods[certificate]:
  `root = STRING #"%" (toString sm.cs_next_var)` by
    (drule compile_alloc_buffer_parts >> simp[]) >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts func)` by
    (drule unwrap_alloc_generated_code >> strip_tac >> drule_all exprSimAllocTheory.buffer_alloc_code >> simp[]) >>
  `exec_alloca (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s (n2w nb : bytes32) = OK u` by
    (qpat_assum `step_inst_base _ _ = OK u` mp_tac >>
     simp[NoAsms, step_inst_base_opcode_eqs, mk_inst_def]) >>
  `copy_static z = copy_static u` by
    (`copy_static z = copy_static a` by fs[copy_runtime_frame_def] >>
     qpat_assum `a = u with vs_inst_idx := _` SUBST1_TAC >> simp[copy_static_def]) >>
  `FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n dst,nb)` by
    (qpat_assum `copy_static z = copy_static u` (mp_then Any strip_assume_tac copy_static_fields) >>
     qpat_assum `z.vs_allocas = u.vs_allocas` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `LENGTH s.vs_memory <= LENGTH z.vs_memory` by suspend "length" >>
  `!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==>
      val_in_memory rt v (w2n dst) mem` by suspend "robust" >>
  qpat_x_assum `dst = _` kall_tac >> qpat_x_assum `nb = 32 * _` kall_tac >>
  qpat_x_assum `z.vs_memory = _` kall_tac >>
  qexistsl [`z with vs_inst_idx := LENGTH sc.cs_current_insts`,`HG`,`tf`,`root`,`dst`,`u`] >>
  fs[lookup_var_def, eval_operand_def, allocas_below_fmp_updates] >> conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >> qpat_assum `!id b len. _ ==> regions_disjoint _ _ _ _`
        (drule_all_then ACCEPT_TAC)) >>
  conj_tac
  >- (rpt strip_tac >> qpat_assum `!n b len. local_region _ _ _ _ _ _ ==> _`
        (drule_then ACCEPT_TAC)) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _`
        (drule_then ACCEPT_TAC)) >>
  qpat_assum `u = update_var _ _ _` (fn th =>
    qpat_assum `copy_static z = copy_static u` (mp_tac o REWRITE_RULE [th])) >>
  simp[NoAsms, copy_static_def]
QED

Resume copy_runtime_rhs_endpoint_mods[length]:
  qpat_assum `z.vs_memory = _` SUBST1_TAC >>
  qpat_assum `a.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
  Cases_on `type_slot_size rt = 0` >- simp[immutable_transfers_def] >>
  qspecl_then [`type_slot_size rt`,`w2n src`,`w2n dst`,`0`,`a`] mp_tac
    immutable_runtime_transfers_snapshot >>
  simp[NoAsms] >> impl_tac >- decide_tac >>
  disch_then SUBST1_TAC >>
  irule exprSimAbiEncodeMemoryLengthTheory.abi_encode_write_memory_length
QED

Resume copy_runtime_rhs_endpoint_mods[robust]:
  gen_tac >> disch_tac >> irule val_in_memory_mem_agree >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`nb`,`z.vs_memory`] >>
  conj_tac >- simp[Abbr `nb`] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_assum `mem_agree_outside _ _ _` (irule o REWRITE_RULE[mem_agree_outside_def]) >>
  qpat_assum `tf.t_mem = tn.t_mem DIFF _` SUBST1_TAC >> simp[pred_setTheory.IN_DIFF]
QED

Finalise copy_runtime_rhs_endpoint_mods


(* Compatibility projection: the original interface need not expose ALLOCA. *)
Theorem copy_runtime_rhs_run_mods:
  ~ce.ce_is_ctor /\ p.ptr_location = LocCode /\ ~is_word_type ty /\
  unwrap_value ce (LocatedValue ty p) sm = (op,sc) /\
  type_memory_bytes ce ty = type_memory_size rt /\
  fn_has_code sm sc func /\ fn_inst_ids_distinct func /\
  stmt_state_rel H ctx func ce cx ee s /\ local_ptrs_reserved ce sm /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  eval_operand p.ptr_operand s = SOME src /\ op_taint tn p.ptr_operand = {} /\
  val_wf rt v /\ val_in_memory rt v (w2n src) s.vs_data_section /\
  w2n src + type_memory_size rt <= LENGTH s.vs_data_section /\
  w2n src + type_memory_size rt < dimword (:256) ==>
  ?z Gf tf root dst.
    op = Var root /\ eval_operand op z = SOME dst /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ allocas_from lo z /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    lo <= w2n dst /\ w2n dst + type_memory_size rt <= z.vs_alloca_next /\
    w2n dst + type_memory_size rt < dimword (:256) /\
    sm.cs_next_id < sc.cs_next_id /\
    FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dst,type_memory_size rt) /\
    FLOOKUP Gf root = SOME (w2n dst,type_memory_size rt) /\
    ptr_covers Gf tf root z (type_memory_size rt) /\
    val_in_memory rt v (w2n dst) z.vs_memory /\
    tf.t_mem = tn.t_mem DIFF {i | w2n dst <= i /\ i < w2n dst+type_memory_size rt} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
       FLOOKUP z.vs_allocas id = SOME entry) /\
    (!id b len. id < sm.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (b,len) ==>
       regions_disjoint (w2n dst) (type_memory_size rt) b len) /\
    (!name b len. local_region ce ee.scopes s name b len ==>
       w2n dst + type_memory_size rt <= b \/ b+len <= w2n dst) /\
    (!off len. off+len <= w2n dst \/ w2n dst+type_memory_size rt <= off ==>
       mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    z.vs_data_section = s.vs_data_section /\ z.vs_accounts = s.vs_accounts /\
    z.vs_transient = s.vs_transient /\ z.vs_call_ctx = s.vs_call_ctx /\
    z.vs_immutables = s.vs_immutables
Proof
  disch_then (mp_tac o MATCH_MP copy_runtime_rhs_endpoint_mods) >>
  disch_then (qx_choosel_then [`z`,`Gf`,`tf`,`root`,`dst`,`u`] strip_assume_tac) >>
  qexistsl [`z`,`Gf`,`tf`,`root`,`dst`] >> asm_rewrite_tac[]
QED
