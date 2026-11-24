(* Straight administrative forcing after the selected VV child. *)
Theory ctorCopyStraightUnwrap
Ancestors
  bodyFullUnwrapIdentity bodyFullUnwrapWord bodyFullUnwrapCodeCopy bodyFullUnwrapSlot
  ctorCopySingleUnwrapRun exprSimAbiEncodeArgsMaterializePath
  exprPtrUnwrapMarked abiDecodeStaticProps exprLowering exprLoweringProps emitHelperProps
  compileEnv context venomInst vyperStorageFootprint exprSimMemDefs loweringPosts
  bodyPtrDefs fragGasOriginPtr ptrDiscipline allocaHistory
  venomMemDefs valueCopyBytes bodyFullUnwrapSlotOrigin exprPtrUnwrapEnsureShape
  abiBufferAllocationCode copyExecution list

Theorem copied_head_word_load_straight[local]:
  compile_ptr_load ctor imm loc src sb = (op,sc) ==>
  dec_straight sb sc /\ EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sb sc)
Proof
  Cases_on `loc` >> simp[compile_ptr_load_def] >>
  TRY (strip_tac >> conj_tac
    >- (drule dec_straight_emit_op >> simp[is_terminator_def]) >>
    drule emitted_insts_emit_op >> simp[mk_inst_def] >> NO_TAC) >>
  Cases_on `ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def,comp_bind_def] >>
  TRY (strip_tac >> conj_tac
    >- (drule dec_straight_emit_op >> simp[is_terminator_def]) >>
    drule emitted_insts_emit_op >> simp[mk_inst_def] >> NO_TAC) >>
  pairarg_tac >> simp[] >> strip_tac >>
  `dec_straight sb cs'` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac dec_straight_emit_op) >>
     simp[is_terminator_def]) >>
  `dec_straight cs' sc` by
    (qpat_assum `emit_op ILOAD _ _ = _` (mp_then Any mp_tac dec_straight_emit_op) >>
     simp[is_terminator_def]) >>
  conj_tac >- metis_tac[dec_straight_trans] >>
  `emitted_insts sb sc = emitted_insts sb cs' ++ emitted_insts cs' sc` by
    (irule emitted_insts_append >> fs[dec_straight_def, inst_extends_def]) >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op ILOAD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  simp[mk_inst_def]
QED

(* The loop appends three blocks, unlike the singleton allocation and copy. *)
Theorem straight_slot_copy_single[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb n ctor imm sa = (op,sb) /\
  dec_straight sa sb ==> n = 1
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  Cases_on `n = 1` >> simp[] >>
  qpat_assum `n <> 1` (fn th =>
    drule_all ensure_slot_memory_split >>
    disch_then (qx_choosel_then [`buf`,`sm`] (strip_assume_tac o REWRITE_RULE [th]))) >>
  `sb.cs_blocks = sa.cs_blocks` by
    (qpat_assum `dec_straight _ _` (mp_tac o REWRITE_RULE [dec_straight_def]) >> simp[]) >>
  drule compile_alloc_buffer_code >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `sm.cs_blocks = sa.cs_blocks` by
    (qpat_assum `same_blocks _ _` (mp_tac o REWRITE_RULE [same_blocks_def]) >> simp[]) >>
  drule_all compile_slot_to_memory_boundary >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `sb = slot_copy_final _ _ _ _ _` (mp_tac o Q.AP_TERM `\x. LENGTH x.cs_blocks`) >>
  simp[slot_copy_final_def, slot_copy_blocks_def]
QED

(* Attach the singleton list execution to the very same low-level witness
   that supplies the origin/pointer path to the integrated slot post. *)
Theorem straight_slot_origin_side[local]:
  unwrap_slot_origin_side_producer ctx func lo explicit PG
    (\sa sb s t. dec_straight sa sb ==>
      ?raw. run_inst_seq (emitted_insts sa sb) s = OK raw /\
            t = raw with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  pure_rewrite_tac[unwrap_slot_origin_side_producer_def] >> rpt gen_tac >>
  disch_then (fn pre =>
    map_every assume_tac (CONJUNCTS pre) >> qx_gen_tac `g` >>
    mp_tac (Q.INST [`G` |-> `g`] (MATCH_MP unwrap_ensure_slot_origin_execution pre))) >>
  disch_then (qx_choosel_then [`root`,`dst`,`a`,`G0`,`tn0`,`Gf`,`tnf`,`t`,`sm`,`buf`,`u`]
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  qexistsl [`root`,`dst`,`a`,`G0`,`tn0`,`Gf`,`tnf`,`t`,`sm`,`buf`,`u`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  BETA_TAC >> disch_tac >>
  `n = 1` by (irule straight_slot_copy_single >> metis_tac[]) >>
  qpat_assum `n = 1` (fn th =>
    qpat_assum `compile_ensure_in_memory _ _ _ _ _ _ _ = _`
      (assume_tac o REWRITE_RULE [th])) >>
  qpat_assum `(n = 1 ==> t = _ /\ _)` (drule_then strip_assume_tac) >>
  irule ctor_single_unwrap_endpoint_run >>
  conj_tac
  >- (qexistsl [`a`,`buf`,`ctor`,`dst`,`imm`,`p`,`loc`,`nb`,`op`,`root`,`sm`,`src`,`u`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `func` >> first_assum ACCEPT_TAC
QED

(* Instantiate a producer with the current VV. Its concrete endpoint is
   also the witness for the supplied observation law. *)
val UNWRAP_PIECE_TAC = fn th =>
  mp_tac th >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (qx_choosel_then [`v`,`z`,`G'`,`tn'`]
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  qexistsl [`v`,`z`,`G'`,`tn'`] >>
  conj_tac
  >- ((simp[] >> NO_TAC) ORELSE
      (TRY (qpat_assum `(dec_straight _ _ ==> ?u. run_inst_seq _ _ = OK u /\ _)`
        (drule_then assume_tac)) >>
       qpat_assum `?u. run_inst_seq _ _ = OK u /\ _`
         (qx_choose_then `raw` strip_assume_tac) >>
       qpat_assum `!u. dec_straight _ _ /\ _ ==> R _ _`
         (qspec_then `raw` mp_tac) >> simp[])) >>
  simp[];

Theorem copied_head_straight_unwrap_observed:
  R s s /\
  (!u. dec_straight sb sc /\
       EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sb sc) /\
       run_inst_seq (emitted_insts sb sc) s = OK u ==>
       R s (u with vs_inst_idx := LENGTH sc.cs_current_insts)) /\
  (!t p. vv = LocatedValue t p /\ ~is_word_type t /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
    (type_memory_bytes cenv t + 31) DIV 32 = 1) /\
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
  ?v z G' tn'.
    R s z /\ read_result cx tv ee = (INL v, ee) /\
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
  strip_tac >> Cases_on `vv`
  >- (rename1 `StackValue t0 op0` >>
      UNWRAP_PIECE_TAC (Q.INST [`vv` |-> `StackValue t0 op0`] unwrap_stack_origin_ptr_run)) >>
  rename1 `LocatedValue t p` >>
  `p.ptr_location <> LocCalldata` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- fs[storage_trace_domain_def]) >>
     strip_tac >> imp_res_tac vv_post_not_calldata) >>
  Cases_on `is_word_type t`
  >- suspend "word" >>
  Cases_on `p.ptr_location = LocMemory`
  >- UNWRAP_PIECE_TAC (Q.INST [`vv` |-> `LocatedValue t p`] unwrap_memory_origin_ptr_run) >>
  Cases_on `p.ptr_location = LocCode`
  >- suspend "code" >>
  suspend "single_slot"
QED

Resume copied_head_straight_unwrap_observed[word]:
  `dec_straight sb sc /\ EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sb sc)` by
    (qpat_assum `is_word_type t` (fn th =>
       qpat_assum `unwrap_value _ _ _ = _`
         (mp_tac o MATCH_MP copied_head_word_load_straight o
          REWRITE_RULE [unwrap_value_def,th])) >> disch_then ACCEPT_TAC) >>
  Cases_on `p.ptr_location` >>
  TRY (qpat_x_assum `LocCalldata <> LocCalldata` mp_tac >> simp[] >> NO_TAC) >>
  FIRST (map (fn th => UNWRAP_PIECE_TAC (Q.INST [`vv` |-> `LocatedValue t p`] th) >>
                      NO_TAC)
    [unwrap_memory_word_origin_ptr_run, unwrap_slot_word_origin_ptr_run,
     unwrap_code_word_origin_ptr_run])
QED

Resume copied_head_straight_unwrap_observed[code]:
  `dec_straight sb sc /\ EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sb sc)` by
    (drule_all materialize_unwrap_code_straight_free >> simp[]) >>
  Cases_on `cenv.ce_is_ctor`
  >- UNWRAP_PIECE_TAC (Q.INST [`vv` |-> `LocatedValue t p`] unwrap_code_copy_ctor_origin_run) >>
  UNWRAP_PIECE_TAC (Q.INST [`vv` |-> `LocatedValue t p`] unwrap_code_copy_runtime_origin_run)
QED

Resume copied_head_straight_unwrap_observed[single_slot]:
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by
    (Cases_on `p.ptr_location` >> gvs[]) >>
  `(type_memory_bytes cenv t + 31) DIV 32 = 1` by
    (first_x_assum irule >> simp[]) >>
  `dec_straight sb sc /\ EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sb sc)` by
    (qpat_assum `unwrap_value _ _ _ = _` (mp_tac o REWRITE_RULE [unwrap_value_def]) >>
     Cases_on `p.ptr_location` >> gvs[] >> strip_tac >>
     qpat_assum `compile_ensure_in_memory _ _ _ _ _ _ _ = _`
       (mp_then Any mp_tac ctor_single_unwrap_straight_free) >> simp[]) >>
  UNWRAP_PIECE_TAC (SIMP_RULE bool_ss [straight_slot_origin_side]
    (Q.INST [`vv` |-> `LocatedValue t p`,
      `Side` |-> `\a b u v. dec_straight a b ==>
        ?raw. run_inst_seq (emitted_insts a b) u = OK raw /\
              v = raw with vs_inst_idx := LENGTH b.cs_current_insts`]
      unwrap_slot_copy_origin_ptr_no_dead_side))
QED
Finalise copied_head_straight_unwrap_observed
