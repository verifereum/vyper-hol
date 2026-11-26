(* Normalize a constructor's saved reason value at the post-head cursor.
   The immutable source may belong to any module in the linked unit. *)
Theory bodyReasonCtorCodeMods
Ancestors
  bodyReasonHeadUnwrapMods bodyFullUnwrapCodeCtorRun bodyFullUnwrapCodeCtorFrame
  bodyPtrBopInRepresentation fragGasOriginPtrDead exprSimWordArgs wordArgsPtr
  exprPtrUnwrapAllocSemantic exprPtrUnwrapAllocEntry exprPtrUnwrapAllocationFrame
  exprPtrUnwrapAllocSeparation exprPtrUnwrapAllocation exprPtrUnwrapCodeCopyShape
  exprSimCopy exprSimStorageCopy exprSimAlloc exprSimProps exprLoweringProps
  loweringPosts loweringStateRelDefs stateRelProj bodyPtrDefs exprSimMemDefs
  bodyFullShadowBodyInv bodyFullPostsMods ptrDiscipline robustCopyTransportPtr
  immutableCopyExecution bufferAllocationExecution exprSimAbiEncodeMemoryLength
  context compileEnv venomState venomInst venomExecSemantics valueEncodingProps
  ghostPcTransportPtr freshWrites localPtrsProps finite_map words arithmetic
  bodyFullHashKeccakFixed exprLowering fragExec bodyPtrMakeArrayMemoryFrame
  bodyPtrBopHashFootprint appendStorageGhostPtr

Theorem reason_ctor_base_ready[local]:
  stmt_state_rel H ctx func cenv cx ee sh /\
  local_ptrs_reserved cenv sm /\ sm.cs_next_var <= sb.cs_next_var /\
  ghost_inv_at_mods D lo d cenv cx ee G tn s /\ lo <> 0 /\
  (!x. not_fresh_at sm x ==> FLOOKUP Gh x = FLOOKUP G x /\
    op_taint th (Var x) = op_taint tn (Var x)) /\
  cenv.ce_imm_alloca = SOME region ==>
  eval_operand region sh = SOME 0w /\ copy_old_operand sb region /\
  op_taint th region = {} /\ op_prov Gh region = NONE
Proof
  strip_tac >> drule_all_then assume_tac membership_immutable_base_value >>
  Cases_on `region` >> simp[copy_old_operand_def, op_taint_def, op_prov_def] >>
  drule_all_then assume_tac local_ptrs_reserved_imm_base >>
  `not_fresh_at sb s'` by (irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  fs[ghost_inv_at_mods_def, op_taint_def]
QED

Theorem reason_ctor_code_copy_origin_execution_mods:
  cenv.ce_is_ctor /\ p.ptr_location = LocCode /\ ~is_word_type ty /\
  ty = post_value_type cenv e /\ type_memory_bytes cenv ty = type_memory_size rt /\
  type_memory_size rt < dimword (:256) /\
  evaluate_type (get_tenv cx) ty = SOME rt /\ value_has_type rt v /\
  read_result cx tv ee = (INL v,ee) /\
  vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv (LocatedValue ty p) s /\
  unwrap_value cenv (LocatedValue ty p) sb = (op,sc) /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ sm.cs_next_var <= sb.cs_next_var /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  stmt_state_rel H ctx func cenv cx ee sh /\
  alloca_history func sh /\ allocas_from lo sh /\ lo <= sh.vs_alloca_next /\
  ~sh.vs_halted /\ sh.vs_current_bb = sb.cs_current_bb /\
  sh.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx ty tv (LocatedValue ty p) ee Gh th sh /\
  eval_operand p.ptr_operand sh = eval_operand p.ptr_operand s /\
  (!rty w. evaluate_type (get_tenv cx) ty = SOME rty /\
    eval_operand p.ptr_operand sh = SOME w ==>
    w2n w + type_memory_size rty <= lo /\
    (!mem. mem_agree_outside th.t_mem sh.vs_memory mem ==>
      val_in_memory rty v (w2n w) mem)) /\
  ghost_inv_at_mods D lo d cenv cx ee G tn s /\
  (!x. not_fresh_at sm x ==> FLOOKUP Gh x = FLOOKUP G x /\
    op_taint th (Var x) = op_taint tn (Var x)) ==>
  ?z Gf tf.
    (!D'. gas_origin_ptr_path (D',lo,explicit,ctx,func,PG) (sh,Gh,th) []
      (OK z,Gf,tf)) /\
    stmt_state_rel H ctx func cenv cx ee z /\
    wb_frame cenv ee ee sb sh z /\ ghost_kept_at lo cenv ee sb Gh th sh Gf tf /\
    expr_val_rel cx ty v op z /\ ptr_val_ok cx ty v op Gf tf z /\
    expr_store_bound cx ty v op z /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ sh.vs_alloca_next <= z.vs_alloca_next /\
    allocas_from lo z /\ lo <= z.vs_alloca_next /\
    (!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x sh /\
      FLOOKUP Gf x = FLOOKUP Gh x /\ op_taint tf (Var x) = op_taint th (Var x)) /\
    (!x k. not_fresh_at sb x /\ ptr_covers Gh th x sh k ==> ptr_covers Gf tf x z k) /\
    (!id entry. FLOOKUP sh.vs_allocas id = SOME entry ==> FLOOKUP z.vs_allocas id = SOME entry)
Proof
  strip_tac >>
  `?src. eval_operand p.ptr_operand sh = SOME src` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[vv_holds_mods_def] >> simp[] >> metis_tac[]) >>
  `w2n src + type_memory_size rt <= lo /\
   (!mem. mem_agree_outside th.t_mem sh.vs_memory mem ==>
     val_in_memory rt v (w2n src) mem)` by
    (qpat_assum `!rty w. _ ==> _` (qspecl_then [`rt`,`src`] mp_tac) >> simp[]) >>
  `op_taint th p.ptr_operand = {} /\ op_prov Gh p.ptr_operand = NONE` by
    fs[ptr_vv_ok_def] >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sb x` by
    (gen_tac >> disch_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  drule_at (Pat `stmt_state_rel _ _ _ _ _ _ sh`) stmt_state_rel_allocas_below_fmp >>
  disch_tac >>
  qabbrev_tac `nb = type_memory_size rt` >>
  qabbrev_tac `n = type_slot_size rt` >>
  `nb = 32*n` by simp[Abbr `nb`, Abbr `n`, type_memory_size_slots] >>
  `(nb+31) DIV 32 = n` by simp[ADD_DIV_ADD_DIV] >>
  `n <> 0 ==> !region. cenv.ce_imm_alloca = SOME region ==>
    eval_operand region sh = SOME 0w /\ copy_old_operand sb region /\
    op_taint th region = {} /\ op_prov Gh region = NONE` by
    (disch_tac >> gen_tac >> disch_tac >> `lo <> 0` by decide_tac >>
     drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`) reason_ctor_base_ready >>
     disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ sh`)) >>
     disch_then irule >> simp[] >> qexists_tac `sm` >> simp[]) >>
  `?buf mid. compile_alloc_buffer nb sb = (buf,mid) /\
    compile_imm_copy_to_memory T cenv.ce_imm_alloca p.ptr_operand buf.buf_operand n 0 mid =
      ((),sc) /\ op = buf.buf_operand` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     simp[unwrap_value_def, compile_ensure_in_memory_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[]) >>
  `ci_mono sb mid /\ ci_mono mid sc` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_imm_copy_to_memory, pairTheory.SND] >>
  `fn_has_code sb mid func /\ fn_has_code mid sc func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `w2n src + 32*n <= lo` by decide_tac >>
  drule_all ctor_code_copy_origin_execution >>
  disch_then (qspecl_then [`explicit`,`PG`,
    `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
    strip_assume_tac) >>
  rename1 `copy_runtime_frame mid a sc raw` >>
  rename1 `lookup_var root a = SOME dst` >>
  suspend "normalize"
QED

Resume reason_ctor_code_copy_origin_execution_mods[normalize]:
  `op = Var root` by simp[] >>
  `buffer_allocation_base sh sb.cs_next_id < dimword(:256)` by
    (drule_all unwrap_alloc_site_bound >> decide_tac) >>
  `w2n dst = buffer_allocation_base sh sb.cs_next_id` by simp[] >>
  `u = update_var root dst (buffer_allocation_fields sh sb.cs_next_id nb)` by simp[] >>
  `a.vs_memory = sh.vs_memory` by (drule unwrap_alloc_runtime_frame >> simp[]) >>
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  `copy_static raw = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x raw = lookup_var x a)` by
    (qpat_assum `copy_runtime_frame mid a sc raw` (mp_tac o REWRITE_RULE [copy_runtime_frame_def]) >>
     simp[copy_static_def]) >>
  `raw.vs_allocas = u.vs_allocas` by (drule copy_static_fields >> simp[]) >>
  `lo <= w2n dst` by
    (qpat_assum `allocas_from lo raw` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then (qspecl_then [`sb.cs_next_id`,`w2n dst`,`nb`] match_mp_tac) >>
     qpat_assum `raw.vs_allocas = u.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `32*n <= nb` by decide_tac >>
  drule_all ctor_code_copy_exterior_frames >> strip_tac >>
  `wb_frame cenv ee ee sb sh sh` by simp[wb_frame_refl] >>
  `ghost_kept_at lo cenv ee sb Gh th sh Gh th` by simp[ghost_kept_at_refl] >>
  `wb_frame cenv ee ee sb sh (raw with vs_inst_idx := LENGTH sc.cs_current_insts) /\
   ghost_kept_at lo cenv ee sb Gh th sh HG tf` by
    (drule_all (Q.INST [`sa` |-> `sb`, `es` |-> `ee`, `s0` |-> `s`,
       `Gi` |-> `G`, `ti` |-> `tn`] (SPEC_ALL ctor_code_copy_retained_frames) |>
       SRULE [LESS_EQ_REFL]) >> simp[]) >>
  `not_fresh_at mid root` by (drule_all allocated_copy_operands_old >> simp[]) >>
  `lookup_var root raw = SOME dst` by simp[] >>
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts func)` by
    (drule unwrap_alloc_generated_code >> strip_tac >> drule_all buffer_alloc_code >> gvs[]) >>
  `raw.vs_memory = (immutable_transfers F T src dst n 0 a).vs_memory` by
    suspend "snapshot" >>
  `LENGTH sh.vs_memory <= LENGTH raw.vs_memory` by suspend "memory_length" >>
  `stmt_state_rel H ctx func cenv cx ee raw` by suspend "state_rel" >>
  suspend "value"
QED

Resume reason_ctor_code_copy_origin_execution_mods[snapshot]:
  Cases_on `n = 0`
  >- gvs[compile_imm_copy_zero, copy_runtime_frame_def, emitted_insts_refl,
         run_inst_seq_def, immutable_transfers_def] >>
  `!op. (!x. op = Var x ==> x <> root) ==> eval_operand op a = eval_operand op sh` by
    (gen_tac >> disch_tac >> qpat_assum `a = _` SUBST1_TAC >>
     irule unwrap_alloc_operand_frame >> metis_tac[]) >>
  `!region. cenv.ce_imm_alloca = SOME region ==>
    eval_operand region a = SOME 0w /\ copy_old_operand mid region` by
    (gen_tac >> disch_tac >>
     `eval_operand region sh = SOME 0w /\ copy_old_operand sb region` by simp[] >>
     `!x. region = Var x ==> x <> root` by
       (fs[copy_old_operand_def] >> metis_tac[unwrap_alloc_old_operand_distinct]) >>
     metis_tac[copy_old_operand_mono, ci_mono_def]) >>
  drule_all allocated_copy_operands_old >> strip_tac >>
  `!x. p.ptr_operand = Var x ==> x <> root` by metis_tac[unwrap_alloc_old_operand_distinct] >>
  `eval_operand p.ptr_operand a = SOME src` by metis_tac[] >>
  `eval_operand buf.buf_operand a = SOME dst /\ copy_old_operand mid buf.buf_operand` by
    gvs[eval_operand_def, copy_old_operand_def, lookup_var_def] >>
  drule_all copy_ctor_run >> strip_tac >> fs[copy_runtime_frame_def] >> metis_tac[]
QED

Resume reason_ctor_code_copy_origin_execution_mods[memory_length]:
  Cases_on `n = 0` >- fs[immutable_transfers_def] >>
  `w2n src + nb < dimword(:256)` by decide_tac >>
  `regions_disjoint (w2n src) nb (w2n dst) nb` by
    (rewrite_tac[regions_disjoint_def] >> decide_tac) >>
  qpat_assum `raw.vs_memory = _` SUBST1_TAC >>
  qpat_assum `a.vs_memory = sh.vs_memory` (SUBST1_TAC o SYM) >>
  `((immutable_transfers F T src dst n 0 a).vs_memory =
    (write_memory_with_expansion (w2n dst) (mem_bytes_at (w2n src) nb a.vs_memory) a).vs_memory)` by
    (unabbrev_all_tac >> irule copy_ctor_memory_snapshot >> asm_rewrite_tac[]) >>
  pop_assum SUBST1_TAC >> irule abi_encode_write_memory_length
QED

Resume reason_ctor_code_copy_origin_execution_mods[state_rel]:
  `!x. not_fresh_at sb x ==> lookup_var x raw = lookup_var x u` by metis_tac[] >>
  irule copy_buffer_state_rel_frame >>
  qexistsl_tac [`w2n dst`,`mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]`,
    `u`,`sb`,`nb`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (simp_tac bool_ss [mk_inst_def, instruction_accessors, instruction_accfupds,
       combinTheory.K_THM] >> (first_assum ACCEPT_TAC ORELSE NO_TAC)),
    qpat_assum `!name b len. _ ==> regions_disjoint _ _ _ _`
      (MATCH_ACCEPT_TAC o REWRITE_RULE [regions_disjoint_def]),
    qpat_assum `!off len. _ ==> mem_bytes_at off len raw.vs_memory = _`
      (fn th => qpat_assum `u.vs_memory = sh.vs_memory`
         (fn eq => PURE_REWRITE_TAC [eq] >> ACCEPT_TAC th)),
    qpat_assum `LENGTH sh.vs_memory <= LENGTH raw.vs_memory`
      (fn th => qpat_assum `u.vs_memory = sh.vs_memory`
         (fn eq => PURE_REWRITE_TAC [eq] >> ACCEPT_TAC th))]
QED

Resume reason_ctor_code_copy_origin_execution_mods[value]:
  `w2n src + nb < dimword(:256)` by decide_tac >>
  `regions_disjoint (w2n src) nb (w2n dst) nb` by
    (rewrite_tac[regions_disjoint_def] >> decide_tac) >>
  `val_wf rt v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `val_footprint rt v <= nb /\ val_store_size rt v <= nb` by
    simp[Abbr `nb`, val_footprint_le, val_store_size_le] >>
  `!i. i < w2n dst ==> (i IN tm.t_mem <=> i IN th.t_mem)` by
    (drule_all unwrap_alloc_taint_frame >> disch_then (qspec_then `th` mp_tac) >>
     simp[] >> metis_tac[]) >>
  `!mem. mem_agree_outside tm.t_mem a.vs_memory mem ==>
    val_in_memory rt v (w2n src) mem` by
    (gen_tac >> disch_tac >> irule robust_val_in_memory_shrinking_frame >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`th.t_mem`, `tm.t_mem`, `sh.vs_memory`, `a.vs_memory`, `nb`] >>
     simp[] >> rpt strip_tac >> `i < w2n dst` by decide_tac >> metis_tac[]) >>
  `!i. i < nb ==> (w2n dst+i IN tf.t_mem <=> w2n src+i IN tm.t_mem)` by
    (rpt strip_tac >> qpat_assum `!j. j IN tf.t_mem <=> _`
       (qspec_then `w2n dst+i` SUBST1_TAC) >>
     `w2n dst <= w2n dst+i /\ w2n dst+i < w2n dst+32*n /\
      w2n dst+i-w2n dst = i` by decide_tac >> simp[]) >>
  qabbrev_tac `z = raw with vs_inst_idx := LENGTH sc.cs_current_insts` >>
  `ptr_val_ok cx ty v (Var root) HG tf z` by
    (simp[NoAsms, Abbr `z`] >> irule ctor_code_copy_ptr_val_ok >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`a`, `dst`, `nb`, `src`, `tm`, `rt`] >>
     qpat_assum `Abbrev (nb = type_memory_size rt)`
       (PURE_REWRITE_TAC o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `Abbrev (n = type_slot_size rt)`
       (PURE_REWRITE_TAC o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand (Var root) z = SOME dst` by
    (qpat_assum `lookup_var root raw = SOME dst` mp_tac >>
     simp[NoAsms, Abbr `z`, eval_operand_def, lookup_var_def]) >>
  `expr_val_rel cx ty v op z /\ expr_store_bound cx ty v op z` by suspend "read" >>
  qexistsl_tac [`z`,`HG`,`tf`] >>
  conj_tac >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> fs[Abbr `z`]) >>
  simp[Abbr `z`, stmt_state_rel_inst_idx, ptr_covers_inst_idx] >>
  suspend "preserve"
QED

Resume reason_ctor_code_copy_origin_execution_mods[read]:
  `val_in_memory rt v (w2n dst) z.vs_memory` by
    (qpat_assum `ptr_val_ok cx ty v (Var root) HG tf z`
       (strip_assume_tac o REWRITE_RULE [ptr_val_ok_def]) >>
     qpat_assum `~is_word_type ty ==> ptr_mem_ok _ _ _ _ _ _ _`
       (drule_then assume_tac) >>
     drule_all_then ACCEPT_TAC ptr_mem_ok_representation) >>
  conj_tac
  >- (simp[NoAsms, expr_val_rel_def] >> qexists_tac `dst` >>
      qpat_assum `op = Var root` (PURE_REWRITE_TAC o single) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `evaluate_type (get_tenv cx) ty = SOME rt`
        (fn ev => qpat_assum `~is_word_type ty`
          (fn nw => simp[NoAsms, ev, nw])) >> first_assum ACCEPT_TAC) >>
  simp[expr_store_bound_def] >> simp[NoAsms, Abbr `z`] >> decide_tac
QED

Resume reason_ctor_code_copy_origin_execution_mods[preserve]:
  rpt conj_tac
  >- (qpat_assum `ty = post_value_type cenv e` (PURE_REWRITE_TAC o single o GSYM) >>
      first_assum ACCEPT_TAC)
  >- (gen_tac >> disch_tac >>
      qpat_assum `!x. not_fresh_at sb x ==> lookup_var x raw = _ /\ _`
        (drule_then (mp_tac o CONJUNCT1)) >> simp[NoAsms, lookup_var_def])
  >- (rpt strip_tac >> irule ptr_covers_old_transport >>
      qexistsl_tac [`Gh`,`sh`,`sb`,`th`] >>
      conj_tac >- (gen_tac >> disch_tac >>
        qpat_assum `!x. not_fresh_at sb x ==> lookup_var x raw = _ /\ _`
          (drule_then (fn thm => mp_tac thm >> tautLib.TAUT_TAC))) >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `nb = 32*n` (PURE_REWRITE_TAC o single o GSYM) >>
  qpat_assum `!id entry. FLOOKUP sh.vs_allocas id = SOME entry ==> FLOOKUP u.vs_allocas id = SOME entry`
    mp_tac >>
  qpat_assum `u = update_var root dst _` (PURE_REWRITE_TAC o single) >>
  simp[NoAsms, update_var_def]
QED

Finalise reason_ctor_code_copy_origin_execution_mods
