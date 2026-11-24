(* The allocation and immutable word-copy suffix of a nonword LocCode read. *)
Theory entryCreateUnwrapCode
Ancestors
  entryCreateStmtCases entryCreatePathScope entryCreateFocusSpec
  bodyFullUnwrapCodeCopy createSizeLocationCode createSizeCutRegion
  createSizeEdgePC createSizeCutCode exprPtrUnwrapAllocation exprSimCopy
  exprLowering exprLoweringProps compileEnv context fragExec fragGasSeqAbort
  fragGasOrigin gasEvents instIdxIndep venomInst venomInstProofs1
  venomExecSemantics venomState createMarkedPath createSizePrefixReplay
  entryCreateCompletedCut exprSimAbiGasBridge stmtReasonLitFragMemory
  loweringShapeDefs
  arithmetic list rich_list relation pred_set pair

Theorem unwrap_code_copy_layout[local]:
  unwrap_value ce (LocatedValue ty p) a = (op,b) /\
  p.ptr_location = LocCode /\ ~is_word_type ty ==>
  same_blocks a b /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;ILOAD;DLOAD;MSTORE])
    (emitted_insts a b)
Proof
  strip_tac >> qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ a = (buf,mid)` >>
  `same_blocks a mid` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emitHelperTheory.emit_op_def, same_blocks_def,
          fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[]) >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  Cases_on `ce.ce_is_ctor` >> fs[] >>
  FIRST [drule code_ctor_copy_insts, drule code_copy_insts] >> strip_tac >>
  `emitted_insts mid b = is` by
    (qpat_assum `b.cs_current_insts = _` (fn th =>
       pure_rewrite_tac[emitted_insts_def, th, DROP_LENGTH_APPEND]) >> REFL_TAC) >>
  `emitted_insts a b = emitted_insts a mid ++ emitted_insts mid b` by
    (irule emitted_insts_append >> simp[]) >>
  (conj_tac >- metis_tac[same_blocks_trans] >>
   conj_tac >- (pure_rewrite_tac[APPEND_ASSOC] >> simp[]) >>
   fs[EVERY_MEM, mk_inst_def] >> rpt strip_tac >> gvs[] >>
   qpat_x_assum `!j. MEM j (emitted_insts _ _) ==> _`
     (qspec_then `i` mp_tac) >> simp[] >> strip_tac >> simp[])
QED

(* Confine the concrete list run, not an arbitrary zero-mark path reaching
   the same cursor. No instruction at the exit is traversed. *)
Theorem unwrap_code_list_prefix[local]:
  !code s t.
    ~s.vs_halted /\ s.vs_current_bb = b.cs_current_bb /\
    s.vs_inst_idx + LENGTH code = LENGTH b.cs_current_insts /\
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
                i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) code /\
    run_inst_seq code s = OK t ==>
    create_expr_prefix a b E C f s [] (t with vs_inst_idx := LENGTH b.cs_current_insts)
Proof
  Induct
  >- (simp[run_inst_seq_def] >> rpt strip_tac >>
      `s with vs_inst_idx := LENGTH b.cs_current_insts = s` by simp[venom_state_component_equality] >>
      simp[create_expr_prefix_marked]) >>
  rpt gen_tac >> simp[Once run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  rename1 `step_inst_base h s = OK u` >>
  `isPREFIX (h::code) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[Once rich_listTheory.IS_PREFIX] >>
  drule instruction_prefix_cursor >> strip_tac >>
  `u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted` by
    (drule_all step_inst_base_preserves_all >> simp[]) >>
  qabbrev_tac `m = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `run_inst_seq code m = OK (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    (`EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
     simp[Abbr `m`, run_inst_seq_inst_idx, exec_result_map_def]) >>
  `create_expr_prefix a b E C f m [] (t with vs_inst_idx := LENGTH b.cs_current_insts)` by
    (first_x_assum (qspecl_then [`m`, `t with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
     gvs[Abbr `m`, ADD_CLAUSES]) >>
  `gas_origin_edge F E C f s [] (OK m)` by
    (simp[gas_origin_edge_def] >>
     qexists_tac `0` >>
     simp[step_inst_non_invoke, gas_events_step_def, Abbr `m`]) >>
  `create_prefix_step a b E C f s [] m` by
    (`s.vs_inst_idx <> LENGTH b.cs_current_insts` by decide_tac >>
     simp[create_prefix_step_def] >> metis_tac[]) >>
  `create_expr_prefix a b E C f s [] m` by
    (simp[create_expr_prefix_marked] >> irule RTC_SINGLE >> simp[create_marked_edge_def]) >>
  drule_all entryCreatePathScopeTheory.create_expr_prefix_append >> simp[]
QED

Theorem unwrap_code_list_scope[local]:
  same_blocks a b /\ b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  create_cut_code {} a b /\ fn_has_code a b f /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;ILOAD;DLOAD;MSTORE]) (emitted_insts a b) /\
  ~s.vs_halted /\ create_operand_at a s /\ create_operand_at b z /\
  (?raw. run_inst_seq (emitted_insts a b) s = OK raw /\
         z = raw with vs_inst_idx := LENGTH b.cs_current_insts) ==>
  create_operand_full_scope a b E C f s [] (OK z)
Proof
  strip_tac >>
  `b.cs_current_bb = a.cs_current_bb /\ emitted_blocks a b = []` by
    fs[same_blocks_def, emitted_blocks_def] >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  `EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
                i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) (emitted_insts a b)` by
    (fs[create_cut_code_def, frag_code_def, EVERY_MEM] >>
     qx_gen_tac `j` >> strip_tac >>
     qpat_assum `!i. MEM i _ ==> i.inst_opcode = ALLOCA \/ _`
       (drule_then strip_assume_tac) >>
     gvs[is_terminator_def] >> metis_tac[]) >>
  `create_expr_prefix a b E C f s [] (raw with vs_inst_idx := LENGTH b.cs_current_insts)` by
    (irule unwrap_code_list_prefix >> fs[create_operand_at_def] >>
     qexists_tac `emitted_insts a b` >> simp[]) >>
  fs[create_operand_at_def, create_operand_full_scope_def] >> metis_tac[LENGTH_APPEND]
QED

Theorem unwrap_code_region_fetch[local]:
  same_blocks a b /\ create_cut_code {} a b /\ fn_has_code a b f /\
  create_operand_at a s /\ create_expr_prefix a b E C f s marks u /\
  create_operand_fetch a b f u i ==>
  MEM i (emitted_insts a b)
Proof
  strip_tac >>
  `emitted_blocks a b = [] /\ added_labels a b = []` by
    fs[same_blocks_def, emitted_blocks_def, added_labels_def, all_blocks_def,
       DROP_LENGTH_TOO_LONG] >>
  drule_all create_cut_region_rules >> simp[] >> strip_tac >>
  `create_cut_region a b s` by fs[create_operand_at_def] >>
  `create_cut_region a b u` by
    (irule RTC_lifts_invariants >>
     qexists_tac `\p q. ?chunk. create_prefix_step a b E C f p chunk q` >>
     qexists_tac `s` >> simp[] >> conj_tac
     >- (simp[create_prefix_step_def, PULL_EXISTS] >> metis_tac[]) >>
     drule create_expr_prefix_rtc_project >>
     disch_then (qspec_then `\p q. ?chunk. create_prefix_step a b E C f p chunk q` mp_tac) >>
     metis_tac[]) >>
  fs[create_operand_fetch_def, create_operand_at_def] >>
  `MEM i (frag_code a b)` by metis_tac[] >> gvs[frag_code_def]
QED

Theorem unwrap_code_native_cut[local]:
  same_blocks a b /\ create_cut_code {} a b /\ fn_has_code a b f /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;ILOAD;DLOAD;MSTORE]) (emitted_insts a b) /\
  create_operand_at a s ==>
  create_operand_cut a b E C f tops cx st0 source (es,s)
Proof
  rw[create_operand_cut_def] >> drule create_interior_visit_cases >> strip_tac
  >- (drule_all unwrap_code_region_fetch >> strip_tac >> gvs[] >>
      irule entryCreateStmtCasesTheory.create_cut_noncreate_visit >> fs[EVERY_MEM] >>
      first_x_assum drule >> rpt strip_tac >> gvs[]) >>
  drule_all unwrap_code_region_fetch >> strip_tac >> fs[EVERY_MEM] >>
  first_x_assum drule >> rpt strip_tac >> gvs[]
QED

(* The ordinary copy post, at the actual first exit of the unwrap code.
   The cut is independent of successful completion of the list run. *)
Theorem create_unwrap_code_copy_site:
  vv = LocatedValue t p /\ p.ptr_location = LocCode /\ ~is_word_type t /\
  compile_expr cenv ty e sa = (vv,sm) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    ~is_word_type (post_value_type cenv e) ==>
    type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val, ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) s = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  create_operand_cut sb sc explicit ctx func (cx_tops cx) cx st0
    (read_result cx tv) (ee,s) /\
  ?v z G' tn'.
    create_operand_full_scope sb sc explicit ctx func s [] (OK z) /\
    read_result cx tv ee = (INL v, ee) /\
    vv_own cenv cx (post_value_type cenv e) sb sc ee (Value v)
      (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK z, G', tn') /\
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sa sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sb sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sa sm ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z \/
     vv_at cenv cx (post_value_type cenv e) sb sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at sb x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sb s z /\
    ghost_kept_at lo cenv ee sb G tn s G' tn'
Proof
  strip_tac >>
  `same_blocks sb sc /\ sc.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sc /\
   EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;ILOAD;DLOAD;MSTORE]) (emitted_insts sb sc)` by
    (irule unwrap_code_copy_layout >> metis_tac[]) >>
  `create_cut_code {} sb sc` by metis_tac[create_unwrap_cut_code, SND] >>
  `create_operand_at sb s` by simp[create_operand_at_def] >>
  conj_tac >- (irule unwrap_code_native_cut >> simp[]) >>
  Cases_on `cenv.ce_is_ctor` >>
  FIRST [drule_all unwrap_code_copy_ctor_origin_run,
         drule_all unwrap_code_copy_runtime_origin_run] >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`readval`,`endstate`,`endG`,`endtn`] strip_assume_tac)) >>
  `create_operand_at sc endstate` by simp[create_operand_at_def] >>
  `create_operand_full_scope sb sc explicit ctx func s [] (OK endstate)` by
    (irule unwrap_code_list_scope >> simp[] >> metis_tac[]) >>
  qexistsl [`readval`,`endstate`,`endG`,`endtn`] >> simp[]
QED
