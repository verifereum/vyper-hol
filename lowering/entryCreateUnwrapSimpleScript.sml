(* The forcing suffix of a normal VV result, with its own first exit. *)
Theory entryCreateUnwrapSimple
Ancestors
  entryCreateFocusSpec bodyFullUnwrap bodyFullUnwrapWord bodyFullUnwrapIdentity
  entryCreatePathScope createSizePrefixReplay createMarkedPath
  loweringShapeRules fragExec fragGasOrigin gasEvents dftGasFromListTraceDefs
  exprLowering exprLoweringProps context compileEnv emitHelper emitHelperProps abiEncoderProps
  fragGasSeqAbort rich_list instIdxIndep entryCreateCompletedCut
  venomExecSemantics venomInst venomInstProps venomState list relation arithmetic pair
  bodySimFull bodyPtrDefs loweringPosts exprSimMemDefs vyperStorageFootprint
  ptrDiscipline venomMemDefs exprSimUnwrap

Definition unwrap_simple_def:
  unwrap_simple vv <=>
    case vv of
      StackValue _ _ => T
    | LocatedValue t p => is_word_type t \/ p.ptr_location = LocMemory
End

Theorem unwrap_simple_emit_layout[local]:
  MEM opc [MLOAD; SLOAD; TLOAD; DLOAD; ILOAD; CALLDATALOAD] /\
  emit_op opc args a = (op,b) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\
    ~MEM i.inst_opcode [INVOKE; GAS; CREATE; CREATE2] /\
    ~is_terminator i.inst_opcode) (emitted_insts a b)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[emit_op_eq, frag_ids_def, mk_inst_def, is_terminator_def]
QED

Theorem unwrap_simple_code_layout[local]:
  compile_imm_load_word ctor imm arg a = (op,b) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\
    ~MEM i.inst_opcode [INVOKE; GAS; CREATE; CREATE2] /\
    ~is_terminator i.inst_opcode) (emitted_insts a b)
Proof
  Cases_on `ctor` >> simp[compile_imm_load_word_runtime]
  >- (Cases_on `imm` >> simp[compile_imm_load_word_no_base]
      >- (strip_tac >> drule_at (Pat `emit_op _ _ _ = _`) unwrap_simple_emit_layout >> simp[]) >>
      simp[compile_imm_load_word_def, comp_bind_def, emit_op_eq] >> strip_tac >>
      qpat_x_assum `_ = b` (SUBST1_TAC o SYM) >>
      pure_rewrite_tac[emitted_insts_def, compile_state_accfupds] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
      simp[DROP_LENGTH_APPEND, frag_ids_def, mk_inst_def, is_terminator_def]) >>
  strip_tac >> drule_at (Pat `emit_op _ _ _ = _`) unwrap_simple_emit_layout >> simp[]
QED

Theorem unwrap_simple_layout[local]:
  unwrap_simple vv /\ unwrap_value ce vv a = (op,b) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\
    ~MEM i.inst_opcode [INVOKE; GAS; CREATE; CREATE2] /\
    ~is_terminator i.inst_opcode) (emitted_insts a b)
Proof
  Cases_on `vv` >> simp[unwrap_simple_def, unwrap_value_def]
  >- simp[comp_return_def, emitted_insts_refl] >>
  rename1 `is_word_type t \/ p.ptr_location = LocMemory` >>
  Cases_on `is_word_type t`
  >- (Cases_on `p.ptr_location` >> simp[compile_ptr_load_def] >>
      strip_tac >>
      FIRST [drule unwrap_simple_code_layout >> simp[],
             drule_at (Pat `emit_op _ _ _ = _`) unwrap_simple_emit_layout >> simp[]]) >>
  simp[] >> strip_tac >> gvs[comp_return_def, emitted_insts_refl]
QED

(* The run is over the emitted list itself, not an arbitrary run ending
   at the suffix exit. Each cons uses a fetch strictly before that exit. *)
Theorem unwrap_simple_prefix[local]:
  !code s u.
    ~s.vs_halted /\
    b.cs_current_bb = s.vs_current_bb /\
    LENGTH b.cs_current_insts = s.vs_inst_idx + LENGTH code /\
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_id IN frag_ids a b /\
      ~MEM i.inst_opcode [INVOKE; GAS; CREATE; CREATE2] /\
      ~is_terminator i.inst_opcode) code /\
    run_inst_seq code s = OK u ==>
    create_operand_full_scope a b E C f s []
      (OK (u with vs_inst_idx := LENGTH b.cs_current_insts))
Proof
  Induct >- simp[run_inst_seq_def, create_operand_full_scope_def] >>
  rpt gen_tac >> strip_tac >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = h::(code ++ rest)` by
    (Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[IS_PREFIX_APPEND]) >>
  drule DROP_EQ_CONS >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME h` by simp[get_instruction_def] >>
  Cases_on `step_inst_base h s` >> gvs[Once run_inst_seq_def] >>
  rename1 `step_inst_base h s = OK m` >>
  `step_inst 0 C h s = OK m` by simp[step_inst_non_invoke] >>
  `~m.vs_halted /\ m.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow, step_preserves_halted] >>
  qabbrev_tac `v = m with vs_inst_idx := SUC s.vs_inst_idx` >>
  `gas_origin_edge F E C f s [] (OK v)` by
    (simp[gas_origin_edge_def] >> qexists_tac `0` >>
     simp[Abbr `v`, gas_events_step_def]) >>
  `create_prefix_step a b E C f s [] v` by
    (simp[create_prefix_step_def] >> qexistsl_tac [`bb`,`h`] >> simp[] >> decide_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
  first_x_assum (qspecl_then [`v`,`u with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  impl_tac >- simp[Abbr `v`, IS_PREFIX_APPEND, ADD_CLAUSES,
                   run_inst_seq_inst_idx, exec_result_map_def] >>
  simp[create_operand_full_scope_def] >> strip_tac >>
  fs[create_expr_prefix_marked] >>
  irule RTC_TRANS >> qexists_tac `(v,[])` >> simp[] >>
  irule RTC_SINGLE >> simp[create_marked_edge_def]
QED

Theorem unwrap_simple_fetch[local]:
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ code /\
  fn_has_code a b f /\ s.vs_current_bb = a.cs_current_bb /\
  LENGTH a.cs_current_insts <= s.vs_inst_idx /\
  s.vs_inst_idx <= LENGTH b.cs_current_insts /\
  create_operand_fetch a b f s i ==>
  s.vs_inst_idx < LENGTH b.cs_current_insts /\ MEM i code
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  gvs[create_operand_fetch_def, create_operand_at_def] >>
  `s.vs_inst_idx < LENGTH b.cs_current_insts` by (fs[LENGTH_APPEND] >> decide_tac) >> simp[] >>
  qabbrev_tac `j = s.vs_inst_idx - LENGTH a.cs_current_insts` >>
  `j < LENGTH code /\ j + LENGTH a.cs_current_insts = s.vs_inst_idx` by
    (fs[Abbr `j`, LENGTH_APPEND] >> decide_tac) >>
  qpat_assum `!j. j < LENGTH code ==> _` (qspec_then `j` mp_tac) >>
  qpat_assum `j + _ = s.vs_inst_idx` (pure_rewrite_tac o single) >>
  simp[EL_MEM]
QED

Theorem unwrap_simple_native_bound[local]:
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ code /\ fn_has_code a b f /\
  EVERY (\i. i.inst_id IN frag_ids a b /\
    ~MEM i.inst_opcode [INVOKE; GAS; CREATE; CREATE2] /\
    ~is_terminator i.inst_opcode) code ==>
  !x y. RTC (create_operand_native_step a b E C f p) x y ==>
    !d k s left d' k' t right. x = (d,k,s,left) /\ y = (d',k',t,right) /\
      s.vs_current_bb = a.cs_current_bb /\
      LENGTH a.cs_current_insts <= s.vs_inst_idx /\
      s.vs_inst_idx <= LENGTH b.cs_current_insts ==>
      t.vs_current_bb = a.cs_current_bb /\
      LENGTH a.cs_current_insts <= t.vs_inst_idx /\
      t.vs_inst_idx <= LENGTH b.cs_current_insts
Proof
  strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >> simp[] >>
  simp[FORALL_PROD] >>
  rpt gen_tac >> disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  gvs[] >>
  rename1 `create_operand_native_step _ _ _ _ _ _ (_,_,u,_) (_,_,v,_)` >>
  qpat_x_assum `create_operand_native_step _ _ _ _ _ _ _ _`
    (strip_assume_tac o BETA_RULE o REWRITE_RULE[create_operand_native_step_def, LET_THM]) >>
  `u.vs_inst_idx <= LENGTH b.cs_current_insts` by simp[] >>
  drule_all unwrap_simple_fetch >> strip_tac >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode` by fs[EVERY_MEM] >>
  fs[create_prefix_step_def, create_operand_fetch_def] >> gvs[] >>
  qpat_x_assum `gas_origin_edge _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[gas_origin_edge_def]) >>
  gvs[exit_result_def]
  >- metis_tac[step_preserves_control_flow] >>
  qpat_x_assum `OK _ = step_inst _ _ _ _` (assume_tac o SYM) >>
  fs[exit_result_def]
QED

Theorem unwrap_simple_visit[local]:
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ code /\ fn_has_code a b f /\
  EVERY (\i. i.inst_id IN frag_ids a b /\
    ~MEM i.inst_opcode [INVOKE; GAS; CREATE; CREATE2] /\
    ~is_terminator i.inst_opcode) code /\
  create_interior_visit a b E C f (p,d,k) s (before,(key,g,i,t),after) ==>
  g = f /\ ~MEM i.inst_opcode [CREATE;CREATE2;INVOKE]
Proof
  pure_rewrite_tac[create_interior_visit_def, LET_THM, create_operand_at_def, PAIR_EQ] >>
  BETA_TAC >> pure_rewrite_tac[PAIR_EQ] >> strip_tac >>
  `s.vs_inst_idx <= LENGTH b.cs_current_insts` by simp[] >>
  `u.vs_current_bb = a.cs_current_bb /\ LENGTH a.cs_current_insts <= u.vs_inst_idx /\
   u.vs_inst_idx <= LENGTH b.cs_current_insts` by
    metis_tac[unwrap_simple_native_bound, LESS_EQ_REFL] >>
  drule_all unwrap_simple_fetch >> strip_tac >>
  `inst.inst_opcode <> INVOKE /\ ~MEM inst.inst_opcode [CREATE;CREATE2;INVOKE]` by fs[EVERY_MEM] >>
  gvs[trace_step_noninvoke]
QED

Theorem unwrap_simple_run_scope[local]:
  unwrap_simple vv /\ unwrap_value cenv vv sb = (op,sc) /\
  fn_has_code sb sc func /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  run_inst_seq (emitted_insts sb sc) s = OK u ==>
  create_operand_full_scope sb sc explicit ctx func s []
    (OK (u with vs_inst_idx := LENGTH sc.cs_current_insts))
Proof
  strip_tac >> drule_all unwrap_simple_layout >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sb sc) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >>
     qexists_tac `l` >> simp[DROP_APPEND, DROP_LENGTH_NIL] >>
     `LENGTH sb.cs_current_insts -
       (LENGTH sb.cs_current_insts + LENGTH (emitted_insts sb sc)) = 0` by decide_tac >>
     simp[]) >>
  irule unwrap_simple_prefix >> simp[] >>
  qexists_tac `emitted_insts sb sc` >> gvs[LENGTH_APPEND, arithmeticTheory.ADD_COMM]
QED

Theorem unwrap_simple_compiled_visit[local]:
  unwrap_simple vv /\ unwrap_value cenv vv sb = (op,sc) /\
  fn_has_code sb sc func /\
  create_interior_visit sb sc explicit ctx func (p,d,k) s
    (before,(key,f,i,t),after) ==>
  f = func /\ ~MEM i.inst_opcode [CREATE;CREATE2;INVOKE]
Proof
  strip_tac >> drule_all unwrap_simple_layout >> strip_tac >>
  drule_all unwrap_simple_visit >> simp[]
QED

Theorem unwrap_simple_allocas_below_fmp[local]:
  stmt_state_rel H ctx func cenv cx ee s /\ ctx_has_dalloca ctx ==>
  allocas_below_fmp s
Proof
  strip_tac >>
  `alloca_inv s /\ fmp_room ctx func s` by fs[stmt_state_rel_def] >>
  qpat_x_assum `alloca_inv s` mp_tac >>
  qpat_x_assum `fmp_room ctx func s` mp_tac >>
  simp[allocas_below_fmp_def, fmp_room_def,
       venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
  rpt strip_tac >> res_tac >> decide_tac
QED

(* Each semantic supplier chooses the endpoint before the horizon. The
   emitted run (or the identity equation) certifies that same endpoint. *)
val SIMPLE_PIECE_TAC = fn th =>
  mp_tac th >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[] >> NO_TAC) >>
  disch_then (qx_choose_then `v` (qx_choose_then `z`
    (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac)))) >>
  `create_operand_full_scope sb sc explicit ctx func s [] (OK z)` by
    (FIRST
      [qpat_assum `z = s` (fn th => PURE_REWRITE_TAC[th]) >>
       `sc = sb` by fs[unwrap_value_def, comp_return_def] >>
       simp[create_operand_full_scope_def],
       qpat_assum `z = _ with vs_inst_idx := _` (fn th => PURE_REWRITE_TAC[th]) >>
       drule_all unwrap_simple_run_scope >> simp[]]) >>
  qexistsl [`v`, `z`, `G'`, `tn'`] >> simp[];

Theorem create_unwrap_simple_site:
  unwrap_simple vv /\
  compile_expr cenv ty e sa = (vv,sm) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
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
  (!p d k before key f i t after.
    create_interior_visit sb sc explicit ctx func (p,d,k) s
      (before,(key,f,i,t),after) ==>
    f = func /\ ~MEM i.inst_opcode [CREATE;CREATE2;INVOKE]) /\
  ?v z G' tn'.
    create_operand_full_scope sb sc explicit ctx func s [] (OK z) /\
    read_result cx tv ee = (INL v, ee) /\
    (!ann p. vv = LocatedValue ann p /\ ~is_word_type ann /\
      (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
       p.ptr_location = LocCode) ==>
      vv_own cenv cx (post_value_type cenv e) sb sc ee (Value v)
        (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK z, G', tn') /\
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sa sc ee tv
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
  strip_tac >> conj_tac
  >- (rpt gen_tac >> disch_tac >> drule_all unwrap_simple_compiled_visit >> simp[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    (disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- fs[storage_trace_domain_def]) >>
     simp[vv_post_def] >> strip_tac >> drule_all unwrap_simple_allocas_below_fmp >> simp[]) >>
  Cases_on `vv`
  >- (rename1 `StackValue t0 op0` >>
      SIMPLE_PIECE_TAC (Q.INST [`vv` |-> `StackValue t0 op0`] unwrap_stack_origin_ptr_run)) >>
  rename1 `LocatedValue t p` >>
  Cases_on `p.ptr_location = LocCalldata`
  >- (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
      impl_tac >- fs[storage_trace_domain_def] >> simp[vv_post_calldata]) >>
  Cases_on `is_word_type t`
  >- (Cases_on `p.ptr_location` >>
      TRY (qpat_x_assum `LocCalldata <> LocCalldata` mp_tac >> simp[] >> NO_TAC) >>
      FIRST (map (fn th => SIMPLE_PIECE_TAC (Q.INST [`vv` |-> `LocatedValue t p`] th))
        [unwrap_memory_word_origin_ptr_run, unwrap_slot_word_origin_ptr_run,
         unwrap_code_word_origin_ptr_run])) >>
  `p.ptr_location = LocMemory` by fs[unwrap_simple_def] >>
  SIMPLE_PIECE_TAC (Q.INST [`vv` |-> `LocatedValue t p`] unwrap_memory_origin_ptr_run)
QED
