(* Storage and transient aggregate forcing, restricted to its own suffix. *)
Theory entryCreateUnwrapSlot
Ancestors
  entryCreateFocusSpec entryCreatePathScope createSizeLocationCode
  createSizeCutRegion exprPtrUnwrapEnsureShape exprPtrUnwrapAllocation
  exprPtrUnwrapStorageLayout exprSimStorageCopy copyExecution exprLoweringProps
  abiEncoderProps exprSimAbiDecodeSiteCoverage fragExec compileEnv emitHelper
  context loweringHalt loweringPosts venomInst venomState venomRunBounded dftGasFromListTracePrefix
  bodyFullIfExpReach entryCreateBodyCut exprSimAbiGasBridge gasContext
  list rich_list arithmetic relation pair entryCreateSlotWalkScope entryCreateCompletedCut bodyFullUnwrapSlotSelectedPost bodyFullUnwrapSlotCursor ptrDiscipline bodyPtrDefs exprSimMemDefs fragGasOriginPtr venomMemDefs exprLowering vyperStorageFootprint finite_map pred_set bodySim

Theorem unwrap_slot_copy_opcodes[local]:
  (opc = SLOAD \/ opc = TLOAD) /\
  MEM i (frag_code a (slot_copy_final a src dst n opc)) ==>
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2 /\
  i.inst_opcode <> GAS
Proof
  Cases_on `opc = SLOAD` >>
  gvs[frag_code_def, slot_copy_emitted_blocks, slot_copy_blocks_def,
      slot_copy_final_def, slot_copy_init_insts_def, slot_copy_cond_insts_def,
      slot_copy_body_insts_def, rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem unwrap_slot_ensure_opcodes:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb n ctor imm a = (op,b) /\
  MEM i (frag_code a b) ==>
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2 /\
  i.inst_opcode <> GAS
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ensure_slot_memory_split >> strip_tac >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  `a.cs_blocks = sm.cs_blocks` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def,
          comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  `!j. MEM j (frag_code a sm) ==> j.inst_opcode = ALLOCA` by
    simp[frag_code_def, emitted_blocks_def, mk_inst_def] >>
  Cases_on `n = 1`
  >- (gvs[] >> drule storage_copy_word_layout >> strip_tac >>
      `cs_extends sm b` by metis_tac[same_blocks_def,cs_extends_same_block] >>
      drule_all abi_decode_frag_code_compose >> strip_tac >>
      first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
      Cases_on `loc = LocStorage` >>
      gvs[frag_code_def, emitted_blocks_def, same_blocks_def, mk_inst_def]) >>
  `?lab. compile_slot_to_memory src buf.buf_operand n loc sm = (lab,b)` by metis_tac[] >>
  pop_assum strip_assume_tac >>
  drule_all compile_slot_to_memory_boundary >> strip_tac >>
  drule_all abi_decode_frag_code_compose >> strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `loc = LocStorage` >> gvs[] >> metis_tac[unwrap_slot_copy_opcodes]
QED

Theorem create_unwrap_slot_copy_cut:
  unwrap_value cenv (LocatedValue t p) a = (op,b) /\
  p.ptr_location = slot_loc tr /\ ~is_word_type t /\
  fn_has_code a b fn /\ body_inv tops ctx cenv cx /\ MEM fn ctx.ctx_functions ==>
  create_operand_cut a b explicit ctx fn tops cx st0 source (es,s)
Proof
  strip_tac >> drule_all unwrap_slot_ensure_layout >> strip_tac >>
  `create_cut_code {} a b` by metis_tac[create_unwrap_cut_code,SND] >>
  `!i. MEM i (frag_code a b) ==>
       i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2` by
    (rpt strip_tac >> Cases_on `tr` >> gvs[slot_loc_def] >>
     metis_tac[unwrap_slot_ensure_opcodes]) >>
  drule_all create_cut_region_rules >> strip_tac >>
  simp[create_operand_cut_def] >> rpt strip_tac >>
  `create_cut_region a b s` by fs[create_interior_visit_def,create_operand_at_def] >>
  drule create_interior_visit_cases >> strip_tac >>
  fs[create_operand_fetch_def,create_operand_at_def] >>
  `create_cut_region a b u` by metis_tac[create_expr_prefix_cut_region] >>
  `MEM inst (frag_code a b)` by metis_tac[] >>
  gvs[create_body_cut_def,inst_create_size_ok_def]
QED

Theorem create_unwrap_slot_copy_site:
  vv = LocatedValue t p /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\ ~is_word_type t /\
  compile_expr cenv ty e sa = (vv,sm) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  (!bb i. lookup_block sc.cs_current_bb func.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH sc.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids sb sc) /\
  body_inv (cx_tops cx) ctx cenv cx /\ MEM func ctx.ctx_functions /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
  >- (qpat_x_assum `vv = LocatedValue t p` SUBST_ALL_TAC >>
      irule create_unwrap_slot_copy_cut >> simp[] >> qexistsl [`cenv`,`op`,`p`,`t`] >>
      simp[] >> qpat_assum `p.ptr_location = LocStorage \/ _` strip_assume_tac
      >- (qexists_tac `F` >> simp[slot_loc_def]) >>
      qexists_tac `T` >> simp[slot_loc_def]) >>
  mp_tac (Q.INST [`exit_ok` |-> `create_expr_prefix sb sc explicit ctx func s []`]
    unwrap_slot_copy_post_with_exit) >>
  (impl_tac >-
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     drule_all ensure_slot_copy_walk_scope >> strip_tac >>
     drule_all unwrap_ensure_slot_origin_execution_walk >>
     disch_then (qspecl_then [`explicit`,`PG`,`G`]
       (qx_choosel_then [`root`,`wd`,`a`,`G0`,`tn0`,`Gf`,`tnf`,`z`,`mid`,`buf`,`u`]
         strip_assume_tac)) >>
     drule slot_copy_walk_create_prefix >> strip_tac >>
     qexistsl [`root`,`wd`,`a`,`G0`,`tn0`,`Gf`,`tnf`,`z`,`mid`,`buf`,`u`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`v`,`z`,`G'`,`tn'`] strip_assume_tac) >>
  qexistsl [`v`,`z`,`G'`,`tn'`] >>
  simp[create_operand_full_scope_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
