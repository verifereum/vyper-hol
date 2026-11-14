(* Slice's read-only length/data capture, on a common full endpoint. *)
Theory bodyFullBuiltinSliceDynamicCapture
Ancestors
  bodyFullUnwrapRun bodyPtrSignedConvertSourceFixed
  exprSimSliceMemory exprSimSliceCaptureControl builtinBytesMemory
  instSeqPtrLo fragGasSeqPtr bodyPtrDefs exprSimSliceOrdinaryFrame
  venomState venomExecSemantics exprLoweringProps list
  wordArgsPtr bodyPtrBopOperandRetention bodyPtrPrecompileBuiltinsGhost
  stmtSimLogArgs loweringPosts exprSimWordArgs
  logTopicFramePtr stmtSimLogTopics abiEncodeOwnership exprSimHashBoundary
  exprSimConvertBytes bodyPtrBytestringBuiltinsCalldataReserved
  valueEncodingProofs valueEncodingDefs compileEnv vyperValue
  supportedTypes vyperTypeSystem vyperTyping ptrDiscipline
  bodyPtrBytestringBuiltinsWindowGhost loweringStateRelDefs
  bodyPtrBytestringBuiltinsAllocation

Theorem slice_dynamic_capture_full_run:
  compile_bytestring_src (Var src) sa = ((len,data),sb) /\
  fn_has_code sa sb func /\ not_fresh_at sa src /\
  lookup_var src s = SOME p /\ ptr_covers G tn src s capacity /\
  32 <= capacity /\ w2n p + 32 < dimword (:256) /\
  mload (w2n p) s = n2w (LENGTH bs) /\
  mem_bytes_at (w2n p + 32) (LENGTH bs) s.vs_memory = bs /\
  (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  w2n p + 32 <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u G' tn'.
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    eval_operand len u = SOME (n2w (LENGTH bs)) /\
    eval_operand data u = SOME (p+32w) /\
    op_taint tn' len = {} /\ op_prov G' len = NONE /\
    mem_bytes_at (w2n p + 32) (LENGTH bs) u.vs_memory = bs /\
    (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn'.t_mem) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    u = s with vs_vars := u.vs_vars /\
    (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!n. 32+n <= capacity ==>
       ?dp. data = Var dp /\ ptr_covers G' tn' dp u n) /\
    (?lp dp. len = Var lp /\ data = Var dp /\
       not_fresh_at sb lp /\ not_fresh_at sb dp)
Proof
  strip_tac >>
  `?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
       eval_operand len u = SOME (mload (w2n p) s) /\
       eval_operand data u = SOME (p+32w) /\
       u = s with vs_vars := u.vs_vars /\
       (!x. not_fresh_at sa x ==> FLOOKUP u.vs_vars x = FLOOKUP s.vs_vars x)` by
    (irule slice_bytestring_src_run >> qexists_tac `Var src` >>
     simp[eval_operand_def]) >>
  `!i. w2n p <= i /\ i < w2n p + 32 ==> i NOTIN tn.t_mem` by
    (rpt strip_tac >> gvs[]) >>
  drule_all compile_bytestring_src_fixed_frame >>
  disch_then (qspecl_then [`ARB`,`func`,`PG`]
    (qx_choose_then `lp` (qx_choose_then `dp`
      (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))))) >>
  `emitted_insts sa sb =
     [mk_inst sa.cs_next_id MLOAD [Var src] [lp];
      mk_inst (sa.cs_next_id+1) ADD [Var src;Lit 32w] [dp]]` by
    (drule slice_bytestring_src_shape >> simp[]) >>
  `run_inst_seq
     [mk_inst sa.cs_next_id MLOAD [Var src] [lp];
      mk_inst (sa.cs_next_id+1) ADD [Var src;Lit 32w] [dp]] s = OK u` by
    metis_tac[] >>
  mp_tac (Q.SPECL [`ARB`,`ctx`,`func`,`PG`,`G`,`tn`,`s`,`src`,`lp`,`dp`,
    `sa.cs_next_id`,`sa.cs_next_id+1`,`p`,`capacity`,`u`]
    bytestring_source_uniform_checks) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `HG` (qx_choose_then `tm` strip_assume_tac)) >>
  `HG = H /\ tm = th` by
    (qpat_assum `!k. inst_seq_ptr ARB _ _ _ _ _ _ _ _ H th`
       (qspec_then `s.vs_inst_idx` mp_tac) >>
     qpat_assum `!k. inst_seq_ptr ARB _ _ _ _ _ _ _ _ HG tm`
       (qspec_then `s.vs_inst_idx` mp_tac) >>
     qpat_assum `emitted_insts sa sb = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >>
     metis_tac[inst_seq_ptr_ghost_unique]) >>
  qpat_assum `HG = H` SUBST_ALL_TAC >>
  qpat_assum `tm = th` SUBST_ALL_TAC >>
  `u = update_var dp (p+32w) (update_var lp (mload (w2n p) s) s)` by
    (irule bytestring_source_run_endpoint >>
     qexistsl_tac [`sa.cs_next_id`,`sa.cs_next_id+1`,`src`] >> simp[] >> fs[]) >>
  `ptr_covers
     (step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var src] [lp])
       (update_var lp (mload (w2n p) s) s))
     (step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [lp]) s
       (update_var lp (mload (w2n p) s) s) tn)
     src (update_var lp (mload (w2n p) s) s) capacity` by
    (irule wordLoadStorePtrTheory.mload_preserves_ptr_covers >> fs[]) >>
  `lookup_var src (update_var lp (mload (w2n p) s) s) = SOME p` by
    fs[lookup_var_def,update_var_def,finite_mapTheory.FLOOKUP_UPDATE] >>
  `!n. 32+n <= capacity ==> ptr_covers H th dp u n` by
    (gen_tac >> disch_tac >>
     qpat_assum `H = step_prov _ _ _ _` (fn eq => once_rewrite_tac[eq]) >>
     qpat_assum `th = step_taint _ _ _ _` (fn eq => once_rewrite_tac[eq]) >>
     qpat_assum `u = update_var dp _ _` (fn eq => rewrite_tac[eq]) >>
     qspecl_then [`PG`,
       `step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var src] [lp])
          (update_var lp (mload (w2n p) s) s)`,
       `step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [lp]) s
          (update_var lp (mload (w2n p) s) s) tn`,
       `update_var lp (mload (w2n p) s) s`,`sa.cs_next_id+1`,`src`,`dp`,
       `p`,`32`,`capacity`,`n`,`Lit 32w`]
       mp_tac pointer_offset_covers >>
     (impl_tac >- simp[eval_operand_def,op_taint_def]) >> simp[]) >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H th` by
    (gen_tac >>
     drule_all compile_bytestring_src_fixed_frame >>
     disch_then (qspecl_then [`D`,`func`,`PG`] strip_assume_tac) >>
     qpat_x_assum `!k. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _`
       (qspec_then `s.vs_inst_idx` mp_tac) >>
     qpat_assum `!k. inst_seq_ptr ARB _ _ _ _ _ _ (emitted_insts sa sb) _ H th`
       (qspec_then `s.vs_inst_idx` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >>
     metis_tac[inst_seq_ptr_ghost_unique]) >>
  qpat_x_assum `H = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `th = step_taint _ _ _ _` kall_tac >>
  qpat_x_assum `u = update_var dp _ _` kall_tac >>
  qexistsl_tac [`u`,`H`,`th`] >> simp[] >>
  gen_tac >> irule emitted_origin_ptr_path >> simp[] >>
      qexistsl_tac [`emitted_insts sa sb`,`sa`] >> simp[] >>
      drule slice_bytestring_src_control >> strip_tac >> simp[] >>
      conj_tac >- simp[EVERY_MEM,venomInstTheory.is_terminator_def] >>
      conj_tac >- metis_tac[compile_bytestring_src_mem_ok, eval_operand_def] >>
      irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >>
      qpat_assum `!D. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H th`
        (qspec_then `D` mp_tac) >>
      qpat_assum `emitted_insts sa sb = _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[]
QED

(* Full child posts frame the captured window on their actual endpoint. *)
Theorem slice_dynamic_capture_full_frame:
  expr_sim_inv cenv cx env es /\ expr_sim_inv cenv cx env' es1 /\
  stmt_state_rel H ctx func cenv cx es s /\
  expr_val_at cenv cx (BaseT bt) sa sb es v src s /\
  evaluate_type (get_tenv cx) (BaseT bt) = SOME vt /\
  ~is_word_type (BaseT bt) /\ eval_operand src s = SOME p /\
  32 + LENGTH bs <= val_footprint vt v /\
  mem_bytes_at (w2n p + 32) (LENGTH bs) s.vs_memory = bs /\
  (!i. w2n p + 32 <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn.t_mem) /\
  local_ptrs_reserved cenv sb /\ sb.cs_next_id <= sc.cs_next_id /\
  sb.cs_next_var <= sc.cs_next_var /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  (!z. src = Var z ==> not_fresh_at sb z) /\ (!l. src <> Label l) /\
  expr_post H ctx func cenv cx start es sb sc s es1 v1 op1 t /\
  expr_post H ctx func cenv cx length es1 sc sd t es2 v2 op2 u /\
  ghost_kept_at lo cenv es sb G tn s G1 tn1 /\
  ghost_kept_at lo cenv es1 sc G1 tn1 t G2 tn2 ==>
  mem_bytes_at (w2n p + 32) (LENGTH bs) u.vs_memory = bs /\
  (!i. w2n p + 32 <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn2.t_mem) /\
  (!op w. (!z. op = Var z ==> not_fresh_at sb z /\ not_fresh_at sc z) /\
          (!l. op <> Label l) /\ eval_operand op s = SOME w ==>
          eval_operand op u = SOME w) /\
  (!dp n. not_fresh_at sb dp /\ not_fresh_at sc dp /\
          ptr_covers G tn dp s n ==> ptr_covers G2 tn2 dp u n)
Proof
  strip_tac >>
  `wb_frame cenv es es1 sb s t` by
    (irule expr_post_frame >> goal_assum (drule_at Any)) >>
  `!n b sz. local_region cenv es1.scopes t n b sz <=>
             local_region cenv es.scopes s n b sz` by
    (rpt gen_tac >> drule_all log_frame_local_region >> simp[]) >>
  `ghost_kept_at lo cenv es sb G tn s G2 tn2` by
    (irule ghost_kept_at_trans >> goal_assum (drule_at Any) >>
     qexistsl_tac [`G1`,`sc`,`tn1`] >>
     gvs[expr_post_def]) >>
  `ghost_kept cenv es sb G tn s G2 tn2` by
    (qpat_x_assum `ghost_kept_at lo cenv es sb G tn s G2 tn2` mp_tac >>
     simp[ghost_kept_def, ghost_kept_at_def] >> metis_tac[]) >>
  `log_arg_clear cenv cx (BaseT bt) v` by
    (irule log_arg_clear_base >> goal_assum (drule_at Any)) >>
  conj_tac >- (drule_all slice_dynamic_payload_two_operands >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> spose_not_then assume_tac >>
      `w2n p <= i /\ i < w2n p + val_footprint vt v` by decide_tac >>
      drule_all bop_argument_taint_kept >> metis_tac[]) >>
  conj_tac >- metis_tac[slice_two_posts_operands] >>
  rpt strip_tac >>
  `?w. eval_operand (Var dp) s = SOME w` by
    gvs[ptr_covers_def, eval_operand_def] >>
  `eval_operand (Var dp) u = SOME w` by
    (irule slice_captured_operand_two_posts >> simp[] >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  irule ghost_kept_ptr_covers >>
  goal_assum (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
  qexists_tac `w` >> simp[]
QED

(* Adapt the successful source child at its actual capture endpoint. *)
Theorem slice_dynamic_capture_source_post:
  expr_post (H:(bool # bytes32 # type_value) list # num list) ctx func cenv cx e es0 sa sm s0 es v srcop s /\
  post_value_type cenv e = BaseT bt /\
  (?cap. bt = BytesT (Dynamic cap) \/ bt = StringT cap) /\
  evaluate_type (get_tenv cx) (BaseT bt) = SOME vt /\ value_has_type vt v /\
  expr_sim_inv cenv cx env es /\
  ptr_val_ok cx (BaseT bt) v srcop G tn s /\
  ghost_inv_at ghost_D floor d cenv cx es G tn s /\
  compile_bytestring_src srcop sm = ((len,data),sc) /\ fn_has_code sm sc func /\
  (!z. srcop = Var z ==> not_fresh_at sm z) /\ (!l. srcop <> Label l) /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u G' tn' src p bs.
    srcop = Var src /\ eval_operand srcop s = SOME p /\
    (v = BytesV bs \/ (?str. v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
    val_footprint vt v = 32 + LENGTH bs /\
    run_inst_seq (emitted_insts sm sc) s = OK u /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (u with vs_inst_idx := LENGTH sc.cs_current_insts),G',tn')) /\
    eval_operand len u = SOME (n2w (LENGTH bs)) /\
    eval_operand data u = SOME (p+32w) /\
    op_taint tn' len = {} /\ op_prov G' len = NONE /\
    mem_bytes_at (w2n p + 32) (LENGTH bs) u.vs_memory = bs /\
    (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn'.t_mem) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    u = s with vs_vars := u.vs_vars /\
    (!x. not_fresh_at sm x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!n. n <= LENGTH bs ==>
       ?dp. data = Var dp /\ ptr_covers G' tn' dp u n) /\
    expr_post H ctx func cenv cx e es0 sa sc s0 es v srcop u /\
    ghost_inv_at ghost_D floor d cenv cx es G' tn' u /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\
    ptr_covers G' tn' src u (32+LENGTH bs) /\
    (?dp. data = Var dp /\ ptr_covers G' tn' dp u (LENGTH bs)) /\
    (?lp dp. len = Var lp /\ data = Var dp /\
       not_fresh_at sc lp /\ not_fresh_at sc dp)
Proof
  strip_tac >>
  `stmt_state_rel H ctx func cenv cx es s /\
   expr_val_rel cx (BaseT bt) v srcop s /\
   expr_val_at cenv cx (BaseT bt) sa sm es v srcop s` by
    gvs[expr_post_def] >>
  `~is_word_type (BaseT bt) /\ supported_scalar_type (BaseT bt) /\
   is_bytestring_type (BaseT bt)` by
    (gvs[supported_scalar_type_def, supported_word_type_def,
         supported_string_type_def, is_word_type_def, is_bytestring_type_def]) >>
  `log_arg_rel cenv cx sa sm es s (srcop,BaseT bt) v` by
    (simp[log_arg_rel_def] >> irule log_arg_clear_base >>
     goal_assum (drule_at Any)) >>
  `?p. eval_operand srcop s = SOME p` by gvs[expr_val_rel_def] >>
  drule_all expr_val_rel_memory >> strip_tac >>
  `?bs. (v = BytesV bs \/ (?str. v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
        val_footprint vt v = 32 + LENGTH bs /\
        mem_word_at (w2n p) s.vs_memory = n2w (LENGTH bs) /\
        mem_bytes_at (w2n p + 32) (LENGTH bs) s.vs_memory = bs` by
    (gvs[] >> Cases_on `v` >>
     gvs[evaluate_type_def, value_has_type_def, val_footprint_def,
         val_in_memory_def] >> metis_tac[]) >>
  drule_all log_arg_footprint_bound >> strip_tac >>
  `LENGTH bs < dimword (:256) /\ w2n p + 32 < dimword (:256)` by decide_tac >>
  drule_all ptr_val_ok_log_bytestring_window >> strip_tac >>
  `w2n p + 32 <= s.vs_alloca_next` by
    (drule_all abi_encode_owned_footprint_frontier >> decide_tac) >>
  `mload (w2n p) s = n2w (LENGTH bs)` by
    metis_tac[mem_word_at_eq_mload_proof] >>
  `lookup_var src s = SOME p` by gvs[eval_operand_def] >>
  `32 <= 32 + LENGTH bs` by simp[] >>
  `not_fresh_at sm src` by metis_tac[] >>
  qpat_x_assum `srcop = Var src` SUBST_ALL_TAC >>
  drule_all slice_dynamic_capture_full_run >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `stmt_state_rel H ctx func cenv cx es u` by
    (irule stmt_state_rel_reserved_vars_update >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def,loweringStateRelDefsTheory.state_rel_def] >>
  `stor_taint_ok_at ghost_D tn' u /\
   allocas_from floor u /\ floor <= u.vs_alloca_next` by
    (qpat_assum `ghost_inv_at ghost_D floor _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `u = s with vs_vars := _` mp_tac >>
     qpat_assum `tn'.t_stor = tn.t_stor` mp_tac >>
     qpat_assum `tn'.t_trans = tn.t_trans` mp_tac >>
     qpat_assum `tn'.t_imm = tn.t_imm` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ghost_inv_at_def,stor_taint_ok_at_def,allocas_from_def,
       venom_state_component_equality] >>
     metis_tac[]) >>
  `ghost_inv_at ghost_D floor d cenv cx es G' tn' u` by
    (mp_tac (Q.INST [`D` |-> `ghost_D`,`lo` |-> `floor`,
       `sa` |-> `sm`,`G` |-> `G`,`tn` |-> `tn`,`s` |-> `s`,
       `es` |-> `es`,`fn` |-> `func`,`HG` |-> `G'`,`tm` |-> `tn'`,
       `es'` |-> `es`,`s'` |-> `u`]
       ghost_inv_at_local_window_transport) >>
     (impl_tac >- (simp[] >> gvs[venom_state_component_equality] >> metis_tac[])) >>
     disch_then ACCEPT_TAC) >>
  `sm.cs_next_id <= sc.cs_next_id` by
    (qspec_then `sm` mp_tac (Q.SPEC `Var src` ci_mono_compile_bytestring_src) >>
     simp[ci_mono_def]) >>
  `eval_operand (Var src) u = SOME p` by
    (gvs[eval_operand_def] >> metis_tac[]) >>
  `expr_post H ctx func cenv cx e es0 sa sc s0 es v (Var src) u` by
    (irule convert_readonly_expr_post >> simp[] >>
     qexistsl_tac [`s`,`sm`,`Var src`] >> simp[] >>
     gvs[venom_state_component_equality] >> metis_tac[]) >>
  qexistsl_tac [`u`,`G'`,`tn'`,`src`,`p`,`bs`] >> simp[] >>
  gvs[allocas_from_def, venom_state_component_equality,
      ptr_covers_def, eval_operand_def] >> metis_tac[]
QED
