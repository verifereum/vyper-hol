(* Layout-converting stores into memory locals, after expression evaluation. *)
Theory stmtSimMemoryWiden
Ancestors
  list rich_list abiEncoderObserver venomInst venomExecSemantics finite_map exprSim exprSimHyps stmtSim stmtSimDeclMem
  stmtSimAssignMem stmtSimAssignTupleMem typedMemoryCopy
  memoryLocalRhsProps valueCopyBytes
  stmtSimAssignStore fragExec stmtSimDeclStore stmtSimDecl localPtrsProps
  exprLoweringProps venomState venomMemDefs
  stmtLowering exprLowering compileEnv valueEncoding vyperTypeSystem
  vyperInterpreter vyperState
  vyperTypeInitialState vyperContext vyperTypeInvariants placeTypingProps
  vyperStorageLayoutSafety vyperLookupStorage vyperTypeStoragePreservation
Libs
  monadsyntax wordsLib intLib

Theorem abi_collision_scalar_probe[local]:
  evaluate_type_builtin cx (AbiEncode T NONE)
    (TupleT [BaseT (UintT 256)]) [] [IntV 32] =
      INL (BytesV (REPLICATE 31 0w ++ [32w])) /\
  typed_val_to_w256 (BaseTV (BytesT (Fixed 32)))
    (BytesV (REPLICATE 31 0w ++ [32w])) = 32w
Proof
  EVAL_TAC
QED

Theorem abi_collision_source_probe[local]:
  !cenv cx es.
    (do raw <- eval_expr cx
       (TypeBuiltin (BaseT (BytesT (Fixed 32))) (AbiEncode T NONE)
         (TupleT [BaseT (UintT 256)])
         [Literal (BaseT (UintT 256)) (IntL 32)]);
        read_result cx raw od) es =
      (INL (BytesV (REPLICATE 31 0w ++ [32w])),es) /\
    lowered_value_type cenv
       (TypeBuiltin (BaseT (BytesT (Fixed 32))) (AbiEncode T NONE)
         (TupleT [BaseT (UintT 256)])
         [Literal (BaseT (UintT 256)) (IntL 32)]) =
       BaseT (BytesT (Dynamic 32))
Proof
  rpt gen_tac >> EVAL_TAC
QED

Theorem abi_collision_compile_probe[local]:
  !ce lc rt.
    let st = <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
                cs_current_bb := "entry"; cs_current_insts := [];
                cs_blocks := []; cs_data_sections := [] |> in
    let c = ce with <| ce_vars := FEMPTY |+ ("x",PtrVar (Var "%0") 64);
                      ce_struct_fields := FEMPTY; ce_is_ctor := F;
                      ce_alloca_locals := T |> in
    let out = SND (compile_stmt c lc rt
       (AnnAssign "x" (BaseT (BytesT (Dynamic 32)))
        (TypeBuiltin (BaseT (BytesT (Fixed 32))) (AbiEncode T NONE)
         (TupleT [BaseT (UintT 256)])
         [Literal (BaseT (UintT 256)) (IntL 32)]))
        (st with cs_next_var := 1)) in
    let bb = <| bb_label := "entry"; bb_instructions :=
          out.cs_current_insts ++ [mk_inst 16 STOP [] []] |> in
    case run_block 30 ctx bb (init_venom_state "entry") of
      Halt s => mload 0 s = 0w /\
        ~val_in_memory (BaseTV (BytesT (Dynamic 32)))
          (BytesV (REPLICATE 31 0w ++ [32w])) 0 s.vs_memory
    | _ => F
Proof
  rpt gen_tac >> EVAL_TAC
QED

Theorem abi_collision_value_post_probe[local]:
  !ce cx sa sb es op s.
    eval_operand op s = SOME 32w ==>
    expr_val_rel cx (BaseT (BytesT (Fixed 32)))
      (BytesV (REPLICATE 31 0w ++ [32w])) op s /\
    expr_val_at ce cx (BaseT (BytesT (Fixed 32))) sa sb es
      (BytesV (REPLICATE 31 0w ++ [32w])) op s
Proof
  rpt strip_tac >>
  simp[expr_val_rel_def, expr_val_at_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def, abi_collision_scalar_probe]
QED

Theorem abi_collision_trace_probe[local]:
  !ce sa op sb.
    ce.ce_struct_fields = FEMPTY /\ ~ce.ce_is_ctor /\
    lower_value compile_expr ce (BaseT (BytesT (Fixed 32)))
      (TypeBuiltin (BaseT (BytesT (Fixed 32))) (AbiEncode T NONE)
         (TupleT [BaseT (UintT 256)])
         [Literal (BaseT (UintT 256)) (IntL 32)]) sa = (op,sb) ==>
    let v = (\k. "%" ++ toString (sa.cs_next_var + k)) in
    let i = sa.cs_next_id in
    let trace =
      [mk_inst i ALLOCA [Lit 32w] [v 0];
       mk_inst (i+1) ADD [Var (v 0); Lit 0w] [v 1];
       mk_inst (i+2) MSTORE [Var (v 1); Lit 32w] [];
       mk_inst (i+3) ALLOCA [Lit 64w] [v 2];
       mk_inst (i+4) ADD [Var (v 2); Lit 32w] [v 3];
       mk_inst (i+5) MCOPY [Var (v 3); Var (v 0); Lit 32w] [];
       mk_inst (i+6) MSTORE [Var (v 2); Lit 32w] [];
       mk_inst (i+7) MLOAD [Var (v 2)] [v 4]] in
    op = Var (v 4) /\
    sb = sa with <| cs_next_var := sa.cs_next_var + 5;
                   cs_next_id := i + 8;
                   cs_current_insts := sa.cs_current_insts ++ trace |> /\
    emitted_insts sa sb = trace
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, Once compile_expr_def, compile_multi_exprs_def,
       vyperASTTheory.expr_type_def, compile_literal_vv_def,
       unwrap_value_def, as_ptr_val_def, comp_bind_def, comp_return_def] >>
  simp[Once compile_type_builtin_dispatch_component_eq, compile_multi_exprs_def,
       lower_value_def, Once compile_expr_def,
       vyperASTTheory.expr_type_def, compile_literal_vv_def,
       unwrap_value_def, as_ptr_val_def, comp_bind_def, comp_return_def] >>
  simp[Once compile_expr_component_eq, compile_literal_vv_def,
       unwrap_value_def, is_word_type_def, comp_return_def,
       type_memory_bytes_def, type_to_abi_enc_info_def,
       abi_size_bound_def, compile_store_abi_tuple_def] >>
  simp[is_abi_dynamic_def, abi_embedded_static_size_def, abi_static_size_def,
       builtinAbiTheory.lower_abi_encode_def,
       abiEncoderTheory.compile_abi_encode_child_def, contextTheory.compile_alloc_buffer_def,
       as_ptr_val_def, unwrap_value_def, contextTheory.mk_ptr_def,
       is_word_type_def, contextTheory.compile_ptr_load_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def, fresh_var_def, fresh_id_def,
       emit_def, comp_bind_def, comp_return_def, comp_ignore_bind_def,
       as_ptr_val_def, unwrap_value_def, contextTheory.mk_ptr_def,
       is_word_type_def, contextTheory.compile_ptr_load_def] >>
  strip_tac >> gvs[emitted_insts_def, APPEND_ASSOC,
       rich_listTheory.DROP_LENGTH_APPEND] >>
  `((i2w 32):bytes32) = 32w` by EVAL_TAC >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> conj_tac >> REFL_TAC
QED

Theorem abi_collision_trace_structure[local]:
  !ce sa op sb.
    ce.ce_struct_fields = FEMPTY /\ ~ce.ce_is_ctor /\
    lower_value compile_expr ce (BaseT (BytesT (Fixed 32)))
      (TypeBuiltin (BaseT (BytesT (Fixed 32))) (AbiEncode T NONE)
         (TupleT [BaseT (UintT 256)])
         [Literal (BaseT (UintT 256)) (IntL 32)]) sa = (op,sb) ==>
    cs_extends sa sb /\ sb.cs_blocks = sa.cs_blocks /\
    sb.cs_current_bb = sa.cs_current_bb /\
    isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)
Proof
  rpt strip_tac >> drule_all abi_collision_trace_probe >>
  simp[] >> strip_tac >>
  gvs[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND,
      venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]
QED

Theorem collision_emitted_inst_mem[local]:
  fn_has_code sa sb func /\ MEM inst (emitted_insts sa sb) ==>
  MEM inst (fn_insts func)
Proof
  strip_tac >>
  gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  gvs[emitted_insts_def, MEM_APPEND] >>
  metis_tac[rich_listTheory.MEM_DROP_IMP]
QED

Theorem collision_alloca_reused[local]:
  !ctx func ce cx es s inst n b sz.
    stmt_state_rel ctx func ce cx es s /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = w2n n /\ b + sz <= s.vs_alloca_next /\
    s.vs_alloca_next < dimword (:256)
Proof
  rpt strip_tac
  >- (gvs[stmt_state_rel_def] >> metis_tac[])
  >- (gvs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
      metis_tac[]) >>
  irule alloca_room_next_lt >> qexistsl_tac [`ctx`, `func`] >>
  gvs[stmt_state_rel_def]
QED

Theorem collision_alloca_fresh[local]:
  !ctx func ce cx es s inst n.
    stmt_state_rel ctx func ce cx es s /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
    s.vs_alloca_next + w2n n < dimword (:256) /\
    alloca_room ctx func
      (s with <|vs_allocas := s.vs_allocas |+
                   (inst.inst_id,(s.vs_alloca_next,w2n n));
                vs_alloca_next := s.vs_alloca_next + w2n n|>)
Proof
  rpt gen_tac >> strip_tac >> irule alloca_room_fresh >>
  gvs[stmt_state_rel_def, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem collision_alloca_local_frame[local]:
  !ctx func ce cx es s inst q n b sz.
    stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
    not_local_ptr ce es.scopes q /\
    ((FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz)) \/
     (FLOOKUP s.vs_allocas inst.inst_id = NONE /\ b = s.vs_alloca_next)) /\
    local_region ce es.scopes s n lo len ==>
    regions_disjoint b sz lo len
Proof
  rpt gen_tac >> strip_tac
  >- (irule local_ptrs_rel_alloca_disjoint >>
      gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  gvs[stmt_state_rel_def, state_rel_def] >>
  `regions_disjoint lo len s.vs_alloca_next sz` by
    (irule local_ptrs_rel_above_frontier >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem collision_allocas_separate[local]:
  !s a b x nx y ny.
    alloca_inv s /\ a <> b /\
    FLOOKUP s.vs_allocas a = SOME (x,nx) /\
    FLOOKUP s.vs_allocas b = SOME (y,ny) ==>
    x + nx <= y \/ y + ny <= x
Proof
  rpt strip_tac >> fs[alloca_inv_def, allocas_non_overlapping_def] >>
  first_x_assum drule_all >> decide_tac
QED

Theorem collision_allocation_sites[local]:
  !ce sa sb op func es.
    ce.ce_struct_fields = FEMPTY /\ ~ce.ce_is_ctor /\
    lower_value compile_expr ce (BaseT (BytesT (Fixed 32)))
      (TypeBuiltin (BaseT (BytesT (Fixed 32))) (AbiEncode T NONE)
         (TupleT [BaseT (UintT 256)])
         [Literal (BaseT (UintT 256)) (IntL 32)]) sa = (op,sb) /\
    fn_has_code sa sb func /\ local_ptrs_reserved ce sa ==>
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
      ["%" ++ toString sa.cs_next_var]) (fn_insts func) /\
    MEM (mk_inst (sa.cs_next_id+3) ALLOCA [Lit 64w]
      ["%" ++ toString (sa.cs_next_var+2)]) (fn_insts func) /\
    not_local_ptr ce es.scopes ("%" ++ toString sa.cs_next_var) /\
    not_local_ptr ce es.scopes ("%" ++ toString (sa.cs_next_var+2))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_collision_trace_probe >> simp[] >> strip_tac >>
  rpt conj_tac
  >- (irule collision_emitted_inst_mem >>
      goal_assum (drule_at Any) >> simp[])
  >- (irule collision_emitted_inst_mem >>
      goal_assum (drule_at Any) >> simp[])
  >- (irule local_ptrs_reserved_fresh >>
      goal_assum (drule_at Any) >> simp[]) >>
  irule local_ptrs_reserved_fresh >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem collision_prior_alloca_frame[local]:
  !s aid b sz id base len first.
    alloca_inv s /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
    aid < first /\ first <= id /\
    (FLOOKUP s.vs_allocas id = SOME (base,len) \/
     (FLOOKUP s.vs_allocas id = NONE /\ base = s.vs_alloca_next)) ==>
    regions_disjoint b sz base len
Proof
  rpt gen_tac >> strip_tac
  >- (`aid <> id` by decide_tac >>
      drule_all collision_allocas_separate >>
      simp[compileEnvTheory.regions_disjoint_def]) >>
  gvs[alloca_inv_def, alloca_next_valid_def,
      compileEnvTheory.regions_disjoint_def] >> metis_tac[]
QED

Theorem collision_memory_frame[local]:
  !ce es s0 s b1 b2 sa.
    (!n b sz. local_region ce es.scopes s0 n b sz ==>
       regions_disjoint b sz b1 32 /\ regions_disjoint b sz b2 64) /\
    (!aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\
       aid < sa.cs_next_id ==>
       regions_disjoint b sz b1 32 /\ regions_disjoint b sz b2 64) /\
    (!b sz. regions_disjoint b sz b1 32 /\ regions_disjoint b sz b2 64 ==>
       mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory) ==>
    locals_kept ce es s0 s /\
    (!aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\
       aid < sa.cs_next_id ==>
       mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule locals_kept_regions >> rpt strip_tac >>
      first_x_assum irule >> metis_tac[]) >>
  metis_tac[]
QED

Theorem collision_expr_post_bridge[local]:
  !ctx func ce cx es sa sb s0 s op.
    stmt_state_rel ctx func ce cx es s /\
    eval_operand op s = SOME 32w /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
       lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
       FLOOKUP s.vs_allocas aid = SOME b) /\
    (!aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\
       aid < sa.cs_next_id ==>
       mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
    locals_kept ce es s0 s ==>
    expr_post ctx func ce cx
      (TypeBuiltin (BaseT (BytesT (Fixed 32))) (AbiEncode T NONE)
         (TupleT [BaseT (UintT 256)])
         [Literal (BaseT (UintT 256)) (IntL 32)])
      es sa sb s0 es (BytesV (REPLICATE 31 0w ++ [32w])) op s
Proof
  rpt gen_tac >> strip_tac >>
  drule abi_collision_value_post_probe >>
  disch_then (qspecl_then [`ce`, `cx`, `sa`, `sb`, `es`] strip_assume_tac) >>
  simp[expr_post_def, vyperASTTheory.expr_type_def] >> metis_tac[]
QED

Theorem collision_alloca_step[local]:
  !s i q n b.
    (FLOOKUP s.vs_allocas i = NONE /\ b = s.vs_alloca_next) \/
    (?sz. FLOOKUP s.vs_allocas i = SOME (b,sz)) ==>
    venomExecSemantics$step_inst_base (mk_inst i ALLOCA [Lit n] [q]) s =
      OK (update_var q (n2w b)
        (if FLOOKUP s.vs_allocas i = NONE then
           s with <|vs_allocas := s.vs_allocas |+ (i,(b,w2n n));
                    vs_alloca_next := b + w2n n|>
         else s))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[Once venomExecSemanticsTheory.step_inst_base_def,
      venomExecSemanticsTheory.exec_alloca_def,
      venomInstTheory.mk_inst_def, eval_operand_def]
QED

Theorem collision_stage_run[local]:
  !s p q base i.
    lookup_var p s = SOME base ==>
    run_inst_seq
      [mk_inst i ADD [Var p;Lit 0w] [q];
       mk_inst (i+1) MSTORE [Var q;Lit 32w] []] s =
    OK (mstore (w2n base) 32w (update_var q base s))
Proof
  rpt gen_tac >> strip_tac >>
  simp[run_inst_seq_def, Once venomExecSemanticsTheory.step_inst_base_def,
       venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_pure2_def,
       eval_operand_def] >>
  simp[Once venomExecSemanticsTheory.step_inst_base_def,
       venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_write2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem collision_copy_run[local]:
  !s src dst tmp sw dw i.
    lookup_var src s = SOME sw /\ lookup_var dst s = SOME dw /\
    tmp <> src ==>
    run_inst_seq
      [mk_inst i ADD [Var dst;Lit 32w] [tmp];
       mk_inst (i+1) MCOPY [Var tmp;Var src;Lit 32w] []] s =
    OK (mcopy (w2n (dw + 32w)) (w2n sw) 32
          (update_var tmp (dw + 32w) s))
Proof
  rpt gen_tac >> strip_tac >>
  simp[run_inst_seq_def, Once venomExecSemanticsTheory.step_inst_base_def,
       venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_pure2_def,
       eval_operand_def] >>
  simp[Once venomExecSemanticsTheory.step_inst_base_def,
       venomInstTheory.mk_inst_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  gvs[lookup_var_def]
QED

Theorem collision_finish_run[local]:
  !s p q base i.
    lookup_var p s = SOME base ==>
    run_inst_seq
      [mk_inst i MSTORE [Var p;Lit 32w] [];
       mk_inst (i+1) MLOAD [Var p] [q]] s =
    OK (update_var q 32w (mstore (w2n base) 32w s))
Proof
  rpt gen_tac >> strip_tac >>
  simp[run_inst_seq_def, Once venomExecSemanticsTheory.step_inst_base_def,
       venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_write2_def, eval_operand_def] >>
  simp[Once venomExecSemanticsTheory.step_inst_base_def, venomInstTheory.mk_inst_def,
       venomExecSemanticsTheory.exec_read1_def, eval_operand_def,
       emitHelperPropsTheory.eval_operand_mstore,
       venomMemPropsTheory.mload_mstore_same]
QED

Theorem collision_stage_allocated_run[local]:
  !s i p q b allocated.
    ((FLOOKUP s.vs_allocas i = NONE /\ b = s.vs_alloca_next) \/
     (?sz. FLOOKUP s.vs_allocas i = SOME (b,sz))) /\
    b < dimword (:256) /\
    allocated = (if FLOOKUP s.vs_allocas i = NONE then
      s with <|vs_allocas := s.vs_allocas |+ (i,(b,32));
               vs_alloca_next := b + 32|> else s) ==>
    run_inst_seq
      [mk_inst i ALLOCA [Lit 32w] [p];
       mk_inst (i+1) ADD [Var p;Lit 0w] [q];
       mk_inst (i+2) MSTORE [Var q;Lit 32w] []] s =
    OK (mstore b 32w (update_var q (n2w b)
                       (update_var p (n2w b) allocated)))
Proof
  rpt gen_tac >> strip_tac >>
  `venomExecSemantics$step_inst_base
     (mk_inst i ALLOCA [Lit 32w] [p]) s =
     OK (update_var p (n2w b) allocated)` by
    (gvs[Once venomExecSemanticsTheory.step_inst_base_def,
         venomExecSemanticsTheory.exec_alloca_def,
         venomInstTheory.mk_inst_def, eval_operand_def]) >>
  `lookup_var p (update_var p (n2w b) allocated) = SOME (n2w b)` by
    simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  drule collision_stage_run >>
  disch_then (qspecl_then [`q`, `i+1`] assume_tac) >>
  gvs[wordsTheory.w2n_n2w] >>
  simp[Once run_inst_seq_def]
QED

Theorem collision_encode_run[local]:
  !s i src dst tmp out sw b allocated addressed copied.
    lookup_var src s = SOME sw /\ dst <> src /\ tmp <> src /\ tmp <> dst /\
    ((FLOOKUP s.vs_allocas i = NONE /\ b = s.vs_alloca_next) \/
     (?sz. FLOOKUP s.vs_allocas i = SOME (b,sz))) /\
    b < dimword (:256) /\
    allocated = (if FLOOKUP s.vs_allocas i = NONE then
      s with <|vs_allocas := s.vs_allocas |+ (i,(b,64));
               vs_alloca_next := b + 64|> else s) /\
    addressed = update_var dst (n2w b) allocated /\
    copied = mcopy (w2n (((n2w b):bytes32) + 32w)) (w2n sw) 32
               (update_var tmp (n2w b + 32w) addressed) ==>
    run_inst_seq
      [mk_inst i ALLOCA [Lit 64w] [dst];
       mk_inst (i+1) ADD [Var dst;Lit 32w] [tmp];
       mk_inst (i+2) MCOPY [Var tmp;Var src;Lit 32w] [];
       mk_inst (i+3) MSTORE [Var dst;Lit 32w] [];
       mk_inst (i+4) MLOAD [Var dst] [out]] s =
    OK (update_var out 32w (mstore b 32w copied))
Proof
  rpt gen_tac >> strip_tac >>
  `venomExecSemantics$step_inst_base
     (mk_inst i ALLOCA [Lit 64w] [dst]) s = OK addressed` by
    (gvs[Once venomExecSemanticsTheory.step_inst_base_def,
         venomExecSemanticsTheory.exec_alloca_def,
         venomInstTheory.mk_inst_def, eval_operand_def]) >>
  `lookup_var src addressed = SOME sw /\
   lookup_var dst addressed = SOME (n2w b)` by
    (gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `run_inst_seq
     [mk_inst (i+1) ADD [Var dst;Lit 32w] [tmp];
      mk_inst (i+2) MCOPY [Var tmp;Var src;Lit 32w] []] addressed = OK copied` by
    (qspecl_then [`addressed`, `src`, `dst`, `tmp`] mp_tac collision_copy_run >>
     simp[] >> disch_then (qspec_then `i+1` mp_tac) >> simp[]) >>
  `lookup_var dst copied = SOME (n2w b)` by
    (gvs[venomExecSemanticsTheory.mcopy_def, write_memory_with_expansion_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE]) >>
  drule collision_finish_run >>
  disch_then (qspecl_then [`out`, `i+3`] assume_tac) >>
  qpat_assum `run_inst_seq [mk_inst _ ADD _ _; _] _ = _`
    (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then
    `[mk_inst (i+3) MSTORE [Var dst;Lit 32w] [];
      mk_inst (i+4) MLOAD [Var dst] [out]]` assume_tac) >>
  gvs[APPEND, wordsTheory.w2n_n2w] >>
  simp[Once run_inst_seq_def]
QED

Theorem collision_mstore_state_rel[local]:
  !ctx func ce cx es s inst p b sz at w.
    stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\ not_local_ptr ce es.scopes p /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    b <= at /\ at + 32 <= b + sz ==>
    stmt_state_rel ctx func ce cx es (mstore at w s)
Proof
  rpt gen_tac >> strip_tac >>
  `immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es
     (mstore at w s)` by
    (irule loweringSliceTheory.immutables_rel_mstore_alloca >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  irule intCallResultTheory.result_state_memory_frame >> simp[] >>
  qexists_tac `s` >> reverse conj_tac
  >- simp[mstore_def, lookup_var_def] >>
  rpt strip_tac >> irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
  `regions_disjoint b sz b' sz'` by
    (irule local_ptrs_rel_alloca_disjoint >>
     goal_assum (drule_at Any) >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem collision_mcopy_state_rel[local]:
  !ctx func ce cx es s inst p b sz at src len.
    stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\ not_local_ptr ce es.scopes p /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    b <= at /\ at + len <= b + sz ==>
    stmt_state_rel ctx func ce cx es (venomExecSemantics$mcopy at src len s)
Proof
  rpt gen_tac >> strip_tac >>
  `immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es
     (venomExecSemantics$mcopy at src len s)` by
    (irule loweringSliceTheory.immutables_rel_mem_agree >> qexists_tac `s` >>
     conj_tac
     >- simp[venomExecSemanticsTheory.mcopy_def,
             immutableMemoryFrameTheory.immutable_write_memory_capacity,
             arithmeticTheory.MAX_DEF] >>
     conj_tac >- simp[venomExecSemanticsTheory.mcopy_def, write_memory_with_expansion_def] >>
     reverse conj_tac >- gvs[stmt_state_rel_def, state_rel_def] >>
     rpt strip_tac >> irule valueCopyTheory.mem_bytes_at_mcopy_disjoint >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def, immutable_alloca_sep_def] >> strip_tac >>
     qpat_x_assum `ce.ce_is_ctor ==> _` drule >> disch_then drule_all >> strip_tac >>
     qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> _` drule_all >>
     simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  irule intCallResultTheory.result_state_memory_frame >> simp[] >>
  qexists_tac `s` >> reverse conj_tac
  >- simp[venomExecSemanticsTheory.mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  rpt strip_tac >> irule valueCopyTheory.mem_bytes_at_mcopy_disjoint >>
  `regions_disjoint b sz b' sz'` by
    (irule local_ptrs_rel_alloca_disjoint >> goal_assum (drule_at Any) >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem collision_stage_state_run[local]:
  !ctx func ce cx es s i p q.
    stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
    MEM (mk_inst i ALLOCA [Lit 32w] [p]) (fn_insts func) /\
    not_local_ptr ce es.scopes p /\ not_local_ptr ce es.scopes q /\ p <> q ==>
    ?t w. run_inst_seq
      [mk_inst i ALLOCA [Lit 32w] [p];
       mk_inst (i+1) ADD [Var p;Lit 0w] [q];
       mk_inst (i+2) MSTORE [Var q;Lit 32w] []] s = OK t /\
      stmt_state_rel ctx func ce cx es t /\ lookup_var p t = SOME w /\
      FLOOKUP t.vs_allocas i = SOME (w2n w,32)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `inst = mk_inst i ALLOCA [Lit 32w] [p]` >>
  `?s1. venomExecSemantics$exec_alloca inst s (32w:bytes32) = OK s1` by
    (simp[venomExecSemanticsTheory.exec_alloca_def, Abbr `inst`, venomInstTheory.mk_inst_def] >>
     Cases_on `FLOOKUP s.vs_allocas i` >> simp[] >> PairCases_on `x` >> simp[]) >>
  `stmt_state_rel ctx func ce cx es s1 /\
   ?w. lookup_var p s1 = SOME w /\ FLOOKUP s1.vs_allocas i = SOME (w2n w,32)` by
    (drule loweringSliceTheory.stmt_state_rel_exec_alloca >>
     disch_then (qspecl_then [`inst`, `p`, `32w`, `s1`] mp_tac) >>
     gvs[Abbr `inst`, venomInstTheory.mk_inst_def] >> metis_tac[]) >>
  qabbrev_tac `s2 = update_var q w s1` >>
  `stmt_state_rel ctx func ce cx es s2` by
    (simp[Abbr `s2`] >> irule stmt_state_rel_update_var >> simp[]) >>
  `stmt_state_rel ctx func ce cx es (mstore (w2n w) 32w s2)` by
    (irule collision_mstore_state_rel >> simp[] >>
     qexistsl_tac [`w2n w`, `mk_inst i ALLOCA [Lit 32w] [p]`, `p`, `32`] >>
     gvs[Abbr `s2`, Abbr `inst`, update_var_def, venomInstTheory.mk_inst_def]) >>
  qexistsl_tac [`mstore (w2n w) 32w s2`, `w`] >> simp[] >>
  conj_tac
  >- (drule collision_stage_run >> disch_then (qspecl_then [`q`, `i+1`] assume_tac) >>
      simp[Once run_inst_seq_def, Once venomExecSemanticsTheory.step_inst_base_def,
           venomInstTheory.mk_inst_def] >>
      gvs[Abbr `inst`, Abbr `s2`, venomInstTheory.mk_inst_def]) >>
  gvs[Abbr `s2`, mstore_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem collision_stage_framed_run[local]:
  !ctx func ce cx es s i p q.
    stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
    MEM (mk_inst i ALLOCA [Lit 32w] [p]) (fn_insts func) /\
    not_local_ptr ce es.scopes p /\ not_local_ptr ce es.scopes q /\ p <> q ==>
    ?t b. run_inst_seq
      [mk_inst i ALLOCA [Lit 32w] [p];
       mk_inst (i+1) ADD [Var p;Lit 0w] [q];
       mk_inst (i+2) MSTORE [Var q;Lit 32w] []] s = OK t /\
      stmt_state_rel ctx func ce cx es t /\ lookup_var p t = SOME (n2w b) /\
      FLOOKUP t.vs_allocas i = SOME (b,32) /\ b + 32 < dimword (:256) /\
      (FLOOKUP s.vs_allocas i = SOME (b,32) \/
       (FLOOKUP s.vs_allocas i = NONE /\ b = s.vs_alloca_next)) /\
      (!x. x <> p /\ x <> q ==> lookup_var x t = lookup_var x s) /\
      (!aid z. FLOOKUP s.vs_allocas aid = SOME z ==>
         FLOOKUP t.vs_allocas aid = SOME z) /\
      (!a n. regions_disjoint a n b 32 ==>
         mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  `?b. (FLOOKUP s.vs_allocas i = SOME (b,32) \/
         (FLOOKUP s.vs_allocas i = NONE /\ b = s.vs_alloca_next)) /\
       b + 32 < dimword (:256)` by
    (Cases_on `FLOOKUP s.vs_allocas i`
     >- (qexists_tac `s.vs_alloca_next` >> simp[] >>
         drule collision_alloca_fresh >>
         disch_then (qspecl_then [`mk_inst i ALLOCA [Lit 32w] [p]`, `32w`] mp_tac) >>
         gvs[venomInstTheory.mk_inst_def]) >>
     PairCases_on `x` >>
     drule collision_alloca_reused >>
     disch_then (qspecl_then [`mk_inst i ALLOCA [Lit 32w] [p]`, `32w`, `x0`, `x1`] mp_tac) >>
     gvs[venomInstTheory.mk_inst_def] >> strip_tac >> qexists_tac `x0` >> simp[] >> decide_tac) >>
  qabbrev_tac `allocated = if FLOOKUP s.vs_allocas i = NONE then
    s with <|vs_allocas := s.vs_allocas |+ (i,(b,32));
             vs_alloca_next := b + 32|> else s` >>
  qabbrev_tac `t = mstore b 32w (update_var q (n2w b)
                    (update_var p (n2w b) allocated))` >>
  `run_inst_seq [mk_inst i ALLOCA [Lit 32w] [p];
       mk_inst (i+1) ADD [Var p;Lit 0w] [q];
       mk_inst (i+2) MSTORE [Var q;Lit 32w] []] s = OK t` by
    (simp[Abbr `t`] >> irule collision_stage_allocated_run >>
     gvs[Abbr `allocated`] >> decide_tac) >>
  `stmt_state_rel ctx func ce cx es t` by
    (drule_all collision_stage_state_run >> strip_tac >> gvs[]) >>
  qexistsl_tac [`t`, `b`] >> simp[] >> rpt conj_tac
  >- gvs[Abbr `t`, mstore_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
  >- (Cases_on `FLOOKUP s.vs_allocas i = NONE` >>
      gvs[Abbr `t`, Abbr `allocated`, mstore_def, update_var_def, FLOOKUP_UPDATE])
  >- (rpt strip_tac >> simp[Abbr `t`, Abbr `allocated`, mstore_def,
                           lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      IF_CASES_TAC >> simp[])
  >- (rpt strip_tac >> Cases_on `FLOOKUP s.vs_allocas i = NONE` >>
      gvs[Abbr `t`, Abbr `allocated`, mstore_def, update_var_def, FLOOKUP_UPDATE] >>
      Cases_on `aid = i` >> gvs[]) >>
  rpt strip_tac >> simp[Abbr `t`] >>
  dep_rewrite.DEP_REWRITE_TAC[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >>
  gvs[compileEnvTheory.regions_disjoint_def, Abbr `allocated`, update_var_def,
      lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `i = aid` >> gvs[]
QED

Theorem collision_encode_framed_run[local]:
  !ctx func ce cx es s i src dst tmp out sw.
    stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
    MEM (mk_inst i ALLOCA [Lit 64w] [dst]) (fn_insts func) /\
    lookup_var src s = SOME sw /\
    not_local_ptr ce es.scopes dst /\ not_local_ptr ce es.scopes tmp /\
    not_local_ptr ce es.scopes out /\ ALL_DISTINCT [src;dst;tmp;out] ==>
    ?t b. run_inst_seq
      [mk_inst i ALLOCA [Lit 64w] [dst];
       mk_inst (i+1) ADD [Var dst;Lit 32w] [tmp];
       mk_inst (i+2) MCOPY [Var tmp;Var src;Lit 32w] [];
       mk_inst (i+3) MSTORE [Var dst;Lit 32w] [];
       mk_inst (i+4) MLOAD [Var dst] [out]] s = OK t /\
      stmt_state_rel ctx func ce cx es t /\ lookup_var out t = SOME 32w /\
      FLOOKUP t.vs_allocas i = SOME (b,64) /\ b + 64 < dimword (:256) /\
      (FLOOKUP s.vs_allocas i = SOME (b,64) \/
       (FLOOKUP s.vs_allocas i = NONE /\ b = s.vs_alloca_next)) /\
      (!x. x <> dst /\ x <> tmp /\ x <> out ==>
         lookup_var x t = lookup_var x s) /\
      (!aid z. FLOOKUP s.vs_allocas aid = SOME z ==>
         FLOOKUP t.vs_allocas aid = SOME z) /\
      (!a n. regions_disjoint a n b 64 ==>
         mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  `?b. (FLOOKUP s.vs_allocas i = SOME (b,64) \/
         (FLOOKUP s.vs_allocas i = NONE /\ b = s.vs_alloca_next)) /\
       b + 64 < dimword (:256)` by
    (Cases_on `FLOOKUP s.vs_allocas i`
     >- (qexists_tac `s.vs_alloca_next` >> simp[] >>
         drule collision_alloca_fresh >>
         disch_then (qspecl_then [`mk_inst i ALLOCA [Lit 64w] [dst]`, `64w`] mp_tac) >>
         gvs[venomInstTheory.mk_inst_def]) >>
     PairCases_on `x` >> drule collision_alloca_reused >>
     disch_then (qspecl_then [`mk_inst i ALLOCA [Lit 64w] [dst]`, `64w`, `x0`, `x1`] mp_tac) >>
     gvs[venomInstTheory.mk_inst_def] >> strip_tac >> qexists_tac `x0` >> simp[] >> decide_tac) >>
  (qabbrev_tac `allocated = if FLOOKUP s.vs_allocas i = NONE then
    s with <|vs_allocas := s.vs_allocas |+ (i,(b,64));
             vs_alloca_next := b + 64|> else s` >>
  qabbrev_tac `addressed = update_var dst (n2w b) allocated` >>
  qabbrev_tac `added = update_var tmp (((n2w b):bytes32) + 32w) addressed` >>
  qabbrev_tac `copied = mcopy (b+32) (w2n sw) 32 added` >>
  qabbrev_tac `t = update_var out 32w (mstore b 32w copied)` >>
  `w2n (((n2w b):bytes32) + 32w) = b+32` by
    (`b+32 < dimword (:256)` by decide_tac >>
     simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w] >>
     gvs[wordsTheory.dimword_def]) >>
  `run_inst_seq
      [mk_inst i ALLOCA [Lit 64w] [dst];
       mk_inst (i+1) ADD [Var dst;Lit 32w] [tmp];
       mk_inst (i+2) MCOPY [Var tmp;Var src;Lit 32w] [];
       mk_inst (i+3) MSTORE [Var dst;Lit 32w] [];
       mk_inst (i+4) MLOAD [Var dst] [out]] s = OK t` by
    (simp[Abbr `t`] >> irule collision_encode_run >>
     gvs[ALL_DISTINCT, Abbr `copied`, Abbr `added`, Abbr `addressed`, Abbr `allocated`] >> decide_tac) >>
  `venomExecSemantics$exec_alloca (mk_inst i ALLOCA [Lit 64w] [dst]) s
      (64w:bytes32) = OK addressed` by
    (gvs[Abbr `addressed`, Abbr `allocated`,
         venomExecSemanticsTheory.exec_alloca_def, venomInstTheory.mk_inst_def]) >>
  `stmt_state_rel ctx func ce cx es addressed /\
   FLOOKUP addressed.vs_allocas i = SOME (b,64)` by
    (drule loweringSliceTheory.stmt_state_rel_exec_alloca >>
     disch_then (qspecl_then [`mk_inst i ALLOCA [Lit 64w] [dst]`, `dst`, `64w`, `addressed`] mp_tac) >>
     simp[venomInstTheory.mk_inst_def] >>
     strip_tac >>
     gvs[Abbr `addressed`, Abbr `allocated`, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE, wordsTheory.w2n_n2w] >> decide_tac) >>
  `stmt_state_rel ctx func ce cx es added` by
    (simp[Abbr `added`] >> irule stmt_state_rel_update_var >> simp[]) >>
  `stmt_state_rel ctx func ce cx es copied` by
    (simp[Abbr `copied`] >> irule collision_mcopy_state_rel >> simp[] >>
     qexistsl_tac [`b`, `mk_inst i ALLOCA [Lit 64w] [dst]`, `dst`, `64`] >>
     gvs[Abbr `added`, update_var_def, venomInstTheory.mk_inst_def]) >>
  `stmt_state_rel ctx func ce cx es (mstore b 32w copied)` by
    (irule collision_mstore_state_rel >> simp[] >>
     qexistsl_tac [`b`, `mk_inst i ALLOCA [Lit 64w] [dst]`, `dst`, `64`] >>
     gvs[Abbr `copied`, Abbr `added`, update_var_def, venomInstTheory.mk_inst_def,
         venomExecSemanticsTheory.mcopy_def, write_memory_with_expansion_def]) >>
  `stmt_state_rel ctx func ce cx es t` by
    (simp[Abbr `t`] >> irule stmt_state_rel_update_var >> gvs[]) >>
  `t.vs_allocas = addressed.vs_allocas` by
    (simp_tac (pure_ss ++ boolSimps.BOOL_ss ++
       rewrites [venom_state_accfupds, combinTheory.K_THM, LET_THM])
       [Abbr `t`, Abbr `copied`, Abbr `added`, update_var_def, mstore_def,
        venomExecSemanticsTheory.mcopy_def, write_memory_with_expansion_def]) >>
  qexistsl_tac [`t`, `b`] >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- gvs[Abbr `t`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
  >- gvs[]
  >- first_assum ACCEPT_TAC
  >- metis_tac[]
  >- (rpt strip_tac >>
      simp_tac (pure_ss ++ boolSimps.BOOL_ss ++
        rewrites [venom_state_accfupds, combinTheory.K_THM, LET_THM])
        [Abbr `t`, Abbr `copied`, Abbr `added`, Abbr `addressed`,
         mstore_def, venomExecSemanticsTheory.mcopy_def,
         write_memory_with_expansion_def, lookup_var_def, update_var_def] >>
      simp[FLOOKUP_UPDATE] >>
      Cases_on `FLOOKUP s.vs_allocas i = NONE` >>
      simp[Abbr `allocated`, lookup_var_def])
  >- (rpt strip_tac >> simp[] >>
      simp[Abbr `addressed`, update_var_def] >>
      Cases_on `FLOOKUP s.vs_allocas i = NONE` >>
      gvs[Abbr `allocated`, FLOOKUP_UPDATE] >> Cases_on `aid = i` >> gvs[]) >>
  rpt strip_tac >> simp[Abbr `t`, update_var_def] >>
  dep_rewrite.DEP_REWRITE_TAC[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >>
  `a+n <= b \/ b+64 <= a` by gvs[compileEnvTheory.regions_disjoint_def] >>
  simp[] >>
  simp[Abbr `copied`] >>
  dep_rewrite.DEP_REWRITE_TAC[valueCopyTheory.mem_bytes_at_mcopy_disjoint] >>
  simp[] >>
  simp[Abbr `added`, Abbr `addressed`, Abbr `allocated`, update_var_def])
QED

Theorem collision_local_region_transport[local]:
  !ce scopes s t q r name a n.
    not_local_ptr ce scopes q /\ not_local_ptr ce scopes r /\
    (!x. x <> q /\ x <> r ==> lookup_var x t = lookup_var x s) /\
    local_region ce scopes s name a n ==>
    local_region ce scopes t name a n
Proof
  simp[local_region_def, not_local_ptr_def] >> rpt strip_tac >>
  `p <> q /\ p <> r` by metis_tac[] >>
  metis_tac[]
QED

Theorem collision_two_memory_frames[local]:
  !s0 s1 s2 b1 n1 b2 n2 a n.
    (!x k. regions_disjoint x k b1 n1 ==>
       mem_bytes_at x k s1.vs_memory = mem_bytes_at x k s0.vs_memory) /\
    (!x k. regions_disjoint x k b2 n2 ==>
       mem_bytes_at x k s2.vs_memory = mem_bytes_at x k s1.vs_memory) /\
    regions_disjoint a n b1 n1 /\ regions_disjoint a n b2 n2 ==>
    mem_bytes_at a n s2.vs_memory = mem_bytes_at a n s0.vs_memory
Proof
  metis_tac[]
QED

Theorem collision_expr_post_inst_idx[local]:
  !ctx func ce cx e es sa sb s0 es1 v op s k.
    expr_post ctx func ce cx e es sa sb s0 es1 v op s ==>
    expr_post ctx func ce cx e es sa sb s0 es1 v op
      (s with vs_inst_idx := k)
Proof
  simp[expr_post_def, stmt_state_rel_inst_idx, expr_val_rel_def,
       expr_val_at_def, eval_operand_def, lookup_var_def, local_region_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_collision_expr_contract_probe[local]:
  !ctx func ce cx es.
    ce.ce_struct_fields = FEMPTY /\ ~ce.ce_is_ctor ==>
    expr_sim ctx func ce cx (BaseT (BytesT (Fixed 32)))
      (TypeBuiltin (BaseT (BytesT (Fixed 32))) (AbiEncode T NONE)
         (TupleT [BaseT (UintT 256)])
         [Literal (BaseT (UintT 256)) (IntL 32)]) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_sim_def, abi_collision_source_probe] >>
  rpt gen_tac >> strip_tac >>
  drule_all abi_collision_trace_structure >> strip_tac >>
  drule_all collision_allocation_sites >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!es'. MEM _ _ /\ _` (qspec_then `es` strip_assume_tac) >>
  `!k. not_local_ptr ce es.scopes ("%" ++ toString (sa.cs_next_var+k))` by
    (gen_tac >> simp[] >> irule local_ptrs_reserved_fresh >>
     goal_assum (drule_at Any) >> simp[]) >>
  `ALL_DISTINCT (MAP (\k. "%" ++ toString (sa.cs_next_var+k)) [0;1;2;3;4])` by
    simp[ASCIInumbersTheory.toString_inj] >>
  `?s1 b1. run_inst_seq
      [mk_inst sa.cs_next_id ALLOCA [Lit 32w] ["%" ++ toString sa.cs_next_var];
       mk_inst (sa.cs_next_id+1) ADD [Var ("%" ++ toString sa.cs_next_var);Lit 0w]
         ["%" ++ toString (sa.cs_next_var+1)];
       mk_inst (sa.cs_next_id+2) MSTORE [Var ("%" ++ toString (sa.cs_next_var+1));Lit 32w] []] s0 = OK s1 /\
      stmt_state_rel ctx func ce cx es s1 /\
      lookup_var ("%" ++ toString sa.cs_next_var) s1 = SOME (n2w b1) /\
      FLOOKUP s1.vs_allocas sa.cs_next_id = SOME (b1,32) /\ b1+32 < dimword (:256) /\
      (FLOOKUP s0.vs_allocas sa.cs_next_id = SOME (b1,32) \/
       (FLOOKUP s0.vs_allocas sa.cs_next_id = NONE /\ b1 = s0.vs_alloca_next)) /\
      (!x. x <> "%" ++ toString sa.cs_next_var /\ x <> "%" ++ toString (sa.cs_next_var+1) ==>
         lookup_var x s1 = lookup_var x s0) /\
      (!aid z. FLOOKUP s0.vs_allocas aid = SOME z ==> FLOOKUP s1.vs_allocas aid = SOME z) /\
      (!a n. regions_disjoint a n b1 32 ==>
         mem_bytes_at a n s1.vs_memory = mem_bytes_at a n s0.vs_memory)` by
    (irule collision_stage_framed_run >> simp[] >> gvs[]) >>
  (qpat_assum `lookup_var _ s1 = SOME _`
    (mp_then (Pos (el 4)) mp_tac collision_encode_framed_run) >>
   disch_then (qspecl_then [`ctx`, `func`, `ce`, `cx`, `es`,
     `sa.cs_next_id+3`, `"%" ++ toString (sa.cs_next_var+2)`,
     `"%" ++ toString (sa.cs_next_var+3)`,
     `"%" ++ toString (sa.cs_next_var+4)`] mp_tac) >>
   (impl_tac >- (simp[ASCIInumbersTheory.toString_inj] >> metis_tac[])) >>
   disch_then (qx_choose_then `s2` (qx_choose_then `b2` assume_tac)) >>
   fs[] >>
   `!name a n. local_region ce es.scopes s0 name a n ==>
       local_region ce es.scopes s1 name a n` by
     (rpt strip_tac >> irule collision_local_region_transport >>
      goal_assum (drule_at Any) >>
      qexistsl_tac [`"%" ++ toString sa.cs_next_var`,
                    `"%" ++ toString (sa.cs_next_var+1)`] >>
      simp[] >> irule local_ptrs_reserved_fresh >>
      goal_assum (drule_at Any) >> simp[]) >>
   `!name a n. local_region ce es.scopes s0 name a n ==>
       regions_disjoint a n b1 32 /\ regions_disjoint a n b2 64` by
     (rpt gen_tac >> strip_tac >>
      `local_region ce es.scopes s1 name a n` by metis_tac[] >>
      conj_tac
      >- ((qsuff_tac `regions_disjoint b1 32 a n` >-
             gvs[compileEnvTheory.regions_disjoint_def]) >>
          qpat_x_assum `local_region _ _ s1 _ _ _` kall_tac >>
          irule collision_alloca_local_frame >> goal_assum (drule_at Any) >>
          qexistsl_tac [`ctx`, `cx`, `func`,
            `mk_inst sa.cs_next_id ALLOCA [Lit 32w] ["%" ++ toString sa.cs_next_var]`,
            `"%" ++ toString sa.cs_next_var`] >>
          gvs[venomInstTheory.mk_inst_def]) >>
      (qsuff_tac `regions_disjoint b2 64 a n` >-
         gvs[compileEnvTheory.regions_disjoint_def]) >>
      irule collision_alloca_local_frame >> goal_assum (drule_at Any) >>
      qexistsl_tac [`ctx`, `cx`, `func`,
        `mk_inst (sa.cs_next_id+3) ALLOCA [Lit 64w] ["%" ++ toString (sa.cs_next_var+2)]`,
        `"%" ++ toString (sa.cs_next_var+2)`] >>
      gvs[venomInstTheory.mk_inst_def]) >>
   `alloca_inv s0 /\ alloca_inv s1` by gvs[stmt_state_rel_def] >>
   `!aid a n. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa.cs_next_id ==>
       regions_disjoint a n b1 32 /\ regions_disjoint a n b2 64` by
     (rpt gen_tac >> strip_tac >>
      `FLOOKUP s1.vs_allocas aid = SOME (a,n)` by
        (qpat_assum `!aid z. FLOOKUP s0.vs_allocas _ = _ ==> _` drule >> simp[]) >>
      conj_tac
      >- (irule collision_prior_alloca_frame >> goal_assum (drule_at Any) >>
          qexistsl_tac [`sa.cs_next_id`, `sa.cs_next_id`] >> simp[]) >>
      qpat_x_assum `FLOOKUP s0.vs_allocas aid = _` kall_tac >>
      irule collision_prior_alloca_frame >> goal_assum (drule_at Any) >>
      qexistsl_tac [`sa.cs_next_id`, `sa.cs_next_id+3`] >> simp[]) >>
   `locals_kept ce es s0 s2 /\
    (!aid a n. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa.cs_next_id ==>
       mem_bytes_at a n s2.vs_memory = mem_bytes_at a n s0.vs_memory)` by
     (irule collision_memory_frame >>
      qexistsl_tac [`b1`, `b2`] >>
      conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!name a n. local_region _ _ s0 _ _ _ ==> _ /\ _` drule >> simp[]) >>
      conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!aid a n. FLOOKUP s0.vs_allocas _ = _ /\ _ ==> _ /\ _` drule_all >> simp[]) >>
      rpt strip_tac >> irule collision_two_memory_frames >>
      qexistsl_tac [`b1`, `b2`, `32`, `64`, `s1`] >> simp[]) >>
   `!x. not_fresh_at sa x ==> lookup_var x s2 = lookup_var x s0` by
     (rpt strip_tac >>
      `!k. x <> "%" ++ toString (sa.cs_next_var+k)` by
        (gen_tac >> qpat_assum `not_fresh_at _ _`
           (mp_tac o REWRITE_RULE [not_fresh_at_def]) >>
         disch_then (qspec_then `sa.cs_next_var+k` mp_tac) >> simp[]) >>
      `lookup_var x s2 = lookup_var x s1` by
        (qpat_assum `!x. _ /\ _ /\ _ ==> lookup_var x s2 = _` irule >>
         qpat_assum `!k. x <> _` (fn th =>
           simp[SRULE [] (Q.SPEC `2` th), SRULE [] (Q.SPEC `3` th),
                SRULE [] (Q.SPEC `4` th)])) >>
      simp[] >> qpat_assum `!x. _ /\ _ ==> lookup_var x s1 = _` irule >>
      qpat_assum `!k. x <> _` (fn th =>
        simp[SRULE [] (Q.SPEC `0` th), SRULE [] (Q.SPEC `1` th)])) >>
   drule_all abi_collision_trace_probe >> simp[] >> strip_tac >>
   (qexists_tac `s2` >> conj_tac
   >- (qpat_assum `run_inst_seq [_;_;_] s0 = OK s1`
         (mp_then Any mp_tac run_inst_seq_append) >>
       disch_then (qspec_then
         `[mk_inst (sa.cs_next_id+3) ALLOCA [Lit 64w] ["%" ++ toString (sa.cs_next_var+2)];
           mk_inst (sa.cs_next_id+4) ADD [Var ("%" ++ toString (sa.cs_next_var+2));Lit 32w]
             ["%" ++ toString (sa.cs_next_var+3)];
           mk_inst (sa.cs_next_id+5) MCOPY [Var ("%" ++ toString (sa.cs_next_var+3));
             Var ("%" ++ toString sa.cs_next_var);Lit 32w] [];
           mk_inst (sa.cs_next_id+6) MSTORE [Var ("%" ++ toString (sa.cs_next_var+2));Lit 32w] [];
           mk_inst (sa.cs_next_id+7) MLOAD [Var ("%" ++ toString (sa.cs_next_var+2))]
             ["%" ++ toString (sa.cs_next_var+4)]]` mp_tac) >> simp[]) >>
   irule collision_expr_post_inst_idx >>
   irule collision_expr_post_bridge >>
   simp[eval_operand_def] >>
   rpt strip_tac >>
   qpat_assum `!aid a n. FLOOKUP s0.vs_allocas _ = _ /\ _ ==> mem_bytes_at _ _ _ = _`
     drule_all >> simp[]))
QED

Theorem abi_collision_invariant_witness[local]:
  !ce. ce.ce_struct_fields = FEMPTY ==>
    ?env. expr_sim_inv ce empty_evaluation_context env
      ((initial_state initial_machine_state [FEMPTY]) with outcomes := SOME [])
Proof
  rpt strip_tac >>
  qexists_tac `<| current_src := NONE; var_types := FEMPTY;
    var_assignable := FEMPTY; bare_globals := FEMPTY;
    bare_global_assignable := FEMPTY; toplevel_vtypes := FEMPTY;
    type_defs := FEMPTY; fn_sigs := FEMPTY; flag_members := FEMPTY |>` >>
  simp[expr_sim_inv_def, initial_state_def, initial_machine_state_def,
       empty_evaluation_context_def, empty_call_txn_def, get_tenv_def,
       get_module_code_def, current_module_def, functions_well_typed_def,
       context_well_typed_def, env_consistent_def, env_context_consistent_def,
       toplevel_vtypes_complete_def, bare_globals_complete_def,
       bare_global_assignable_complete_def, flag_members_complete_def,
       env_scopes_consistent_def, env_immutables_consistent_def,
       fn_sigs_consistent_def, fn_sigs_declared_complete_def,
       fn_sigs_live_def, state_well_typed_def,
       scope_well_typed_def, vyperStateTheory.lookup_scopes_def,
       accounts_well_typed_def, account_well_typed_def, machine_well_typed_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.empty_accounts_def,
       vfmStateTheory.empty_account_state_def,
       outcomes_accounts_typed_def, sfields_tenv_consistent_def,
       popped_keys_indexed_def, place_map_tables_agree_on_defined_def,
       contract_storage_well_formed_def, storage_layout_safe_def,
       oracle_storage_ok_def, well_formed_storage_def, well_formed_layout_def,
       storage_var_in_range_def, storage_var_info_def, declared_storage_region_def,
       nonreentrant_slot_separated_def, get_module_code_def]
QED

Theorem abi_collision_declaration_contract[local]:
  !ctx func ce cx es id dty st0 c st1.
    ce.ce_struct_fields = FEMPTY /\ ~ce.ce_is_ctor /\
    declare_local ce id dty st0 = (c,st1) ==>
    expr_sim ctx func c cx (BaseT (BytesT (Fixed 32)))
      (TypeBuiltin (BaseT (BytesT (Fixed 32))) (AbiEncode T NONE)
        (TupleT [BaseT (UintT 256)])
        [Literal (BaseT (UintT 256)) (IntL 32)]) es /\
    !sa sb op.
      lower_value compile_expr c (BaseT (BytesT (Fixed 32)))
        (TypeBuiltin (BaseT (BytesT (Fixed 32))) (AbiEncode T NONE)
          (TupleT [BaseT (UintT 256)])
          [Literal (BaseT (UintT 256)) (IntL 32)]) sa = (op,sb) ==>
      cs_extends sa sb
Proof
  rpt gen_tac >> strip_tac >>
  `c.ce_struct_fields = FEMPTY /\ ~c.ce_is_ctor` by
    (Cases_on `ce.ce_alloca_locals` >>
     gvs[declare_local_def, comp_bind_def, comp_return_def, fresh_var_def,
         AllCaseEqs()]) >>
  conj_tac >- (irule abi_collision_expr_contract_probe >> simp[]) >>
  rpt strip_tac >> drule_all abi_collision_trace_structure >> simp[]
QED

Theorem abi_collision_initial_state_rel[local]:
  !ce func.
    ce.ce_vars = FEMPTY /\ ce.ce_module_vars = FEMPTY ==>
    state_rel func ce empty_evaluation_context
      ((initial_state initial_machine_state [FEMPTY]) with outcomes := SOME [])
      (init_venom_state "entry")
Proof
  rpt strip_tac >>
  simp[state_rel_def, local_ptrs_rel_def, local_region_def,
       storage_rel_def, transient_rel_def, storage_vars_rel_def,
       transient_vars_rel_def, accounts_rel_def, immutables_rel_def,
       logs_rel_def, call_ctx_rel_def, initial_state_def, initial_machine_state_def,
       empty_evaluation_context_def, empty_call_txn_def, get_module_code_def,
       init_venom_state_def, empty_call_context_def, empty_tx_context_def,
       empty_block_context_def, contract_storage_def, contract_transient_def]
QED

Theorem collision_single_block_code[local]:
  !sa sb tail.
    sb.cs_blocks = [] /\ sb.cs_current_bb = "entry" ==>
    fn_has_code sa sb (mk_raw_function "collision"
      [<|bb_label := "entry"; bb_instructions := sb.cs_current_insts ++ tail|>])
Proof
  rpt strip_tac >> simp[fn_has_code_def, emitted_blocks_def, mk_raw_function_def] >>
  qexists_tac `<|bb_label := "entry"; bb_instructions := sb.cs_current_insts ++ tail|>` >>
  simp[lookup_block_def, IS_PREFIX_APPEND, listTheory.FIND_def, listTheory.INDEX_FIND_def]
QED

Theorem abi_collision_stmt_entry_code[local]:
  !base lc rt.
    let ce = base with <|ce_vars := FEMPTY; ce_struct_fields := FEMPTY;
      ce_is_ctor := F; ce_alloca_locals := T; ce_return_pc := NONE|> in
    let sa = <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
      cs_current_bb := "entry"; cs_current_insts := [];
      cs_blocks := []; cs_data_sections := [] |> in
    let out = stmt_env ce lc rt
      (AnnAssign "x" (BaseT (BytesT (Dynamic 32)))
        (TypeBuiltin (BaseT (BytesT (Fixed 32))) (AbiEncode T NONE)
          (TupleT [BaseT (UintT 256)]) [Literal (BaseT (UintT 256)) (IntL 32)])) sa in
    let sb = SND out in
    let fn = mk_raw_function "collision"
      [<|bb_label := "entry"; bb_instructions :=
        sb.cs_current_insts ++ [mk_inst sb.cs_next_id STOP [] []] |>] in
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved ce sa /\ ret_pc_ok ce sa (init_venom_state "entry") /\
    ~block_is_terminated sa /\ stmt_res_ok lc (INL ()) /\
    ~(init_venom_state "entry").vs_halted /\
    (init_venom_state "entry").vs_current_bb = sa.cs_current_bb /\
    (init_venom_state "entry").vs_inst_idx = LENGTH sa.cs_current_insts
Proof
  rpt gen_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `fn_has_code sa sb fn` >>
  `sb.cs_blocks = [] /\ sb.cs_current_bb = "entry"` by
    (unabbrev_all_tac >> EVAL_TAC) >>
  conj_tac
  >- (simp[Abbr `fn`] >> irule collision_single_block_code >> simp[]) >>
  rpt conj_tac >> unabbrev_all_tac >> EVAL_TAC >> simp[]
QED

Theorem collision_no_call_room[local]:
  !ctx fn ss.
    lookup_function fn.fn_name ctx.ctx_functions = SOME fn /\
    (!g. ~fn_directly_calls ctx fn.fn_name g) /\
    ss.vs_alloca_next + pending_alloca_size fn ss < dimword (:256) ==>
    alloca_room ctx fn ss
Proof
  rpt strip_tac >>
  `!g. ~TC (fn_directly_calls ctx) fn.fn_name g` by
    (gen_tac >> simp[Once relationTheory.TC_CASES1]) >>
  gvs[alloca_room_def, GSYM pred_setTheory.EMPTY_DEF]
QED

Theorem abi_collision_initial_stmt_state_rel[local]:
  !base lc rt ctx.
    let ce = base with <|ce_vars := FEMPTY; ce_module_vars := FEMPTY;
      ce_struct_fields := FEMPTY; ce_is_ctor := F; ce_alloca_locals := T;
      ce_return_pc := NONE|> in
    let sa = <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
      cs_current_bb := "entry"; cs_current_insts := [];
      cs_blocks := []; cs_data_sections := [] |> in
    let sb = SND (stmt_env ce lc rt
      (AnnAssign "x" (BaseT (BytesT (Dynamic 32)))
        (TypeBuiltin (BaseT (BytesT (Fixed 32))) (AbiEncode T NONE)
          (TupleT [BaseT (UintT 256)]) [Literal (BaseT (UintT 256)) (IntL 32)])) sa) in
    let fn = mk_raw_function "collision"
      [<|bb_label := "entry"; bb_instructions :=
        sb.cs_current_insts ++ [mk_inst sb.cs_next_id STOP [] []]|>] in
    stmt_state_rel (ctx with ctx_functions := [fn]) fn ce empty_evaluation_context
      ((initial_state initial_machine_state [FEMPTY]) with outcomes := SOME [])
      (init_venom_state "entry")
Proof
  rpt gen_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel ct fn ce cx es ss` >>
  simp[stmt_state_rel_def] >> conj_tac
  >- (simp[Abbr `cx`, Abbr `es`, Abbr `ss`] >>
      irule abi_collision_initial_state_rel >> simp[Abbr `ce`]) >>
  conj_tac
  >- (unabbrev_all_tac >> EVAL_TAC >> simp[]) >>
  conj_tac
  >- (irule collision_no_call_room >> conj_tac
      >- (simp[fcgDefsTheory.fn_directly_calls_def, Abbr `ct`, Abbr `fn`,
               venomInstTheory.lookup_function_def, mk_raw_function_def,
               listTheory.FIND_def, listTheory.INDEX_FIND_def] >>
          unabbrev_all_tac >> EVAL_TAC >> simp[] >>
          rpt gen_tac >> rpt disch_tac >> rpt conj_tac >> strip_tac >> gvs[]) >>
      conj_tac
      >- (unabbrev_all_tac >> EVAL_TAC) >>
      simp[Abbr `ct`, Abbr `fn`, venomInstTheory.lookup_function_def,
           mk_raw_function_def, listTheory.FIND_def, listTheory.INDEX_FIND_def]) >>
  conj_tac
  >- simp[immutable_alloca_sep_def, Abbr `ce`] >>
  simp[Abbr `ss`, init_venom_state_def]
QED

Theorem abi_collision_all_fuel_observation[local]:
  !base lc rt ctx fuel.
    let ce = base with <|ce_vars := FEMPTY; ce_module_vars := FEMPTY;
      ce_struct_fields := FEMPTY; ce_is_ctor := F; ce_alloca_locals := T;
      ce_return_pc := NONE|> in
    let sa = <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
      cs_current_bb := "entry"; cs_current_insts := [];
      cs_blocks := []; cs_data_sections := [] |> in
    let sb = SND (stmt_env ce lc rt
      (AnnAssign "x" (BaseT (BytesT (Dynamic 32)))
        (TypeBuiltin (BaseT (BytesT (Fixed 32))) (AbiEncode T NONE)
          (TupleT [BaseT (UintT 256)]) [Literal (BaseT (UintT 256)) (IntL 32)])) sa) in
    let fn = mk_raw_function "collision"
      [<|bb_label := "entry"; bb_instructions :=
        sb.cs_current_insts ++ [mk_inst sb.cs_next_id STOP [] []]|>] in
    case run_from fuel (ctx with ctx_functions := [fn]) fn (init_venom_state "entry") of
      Halt s => lookup_var "%0" s = SOME 0w /\ mload 0 s = 0w
    | _ => F
Proof
  rpt gen_tac >> EVAL_TAC
QED

Theorem collision_local_observation[local]:
  !fn ce scopes t name entry p sz w.
    local_ptrs_rel fn ce scopes t /\
    lookup_scopes name scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p t = SOME w ==>
    val_in_memory entry.type entry.value (w2n w) t.vs_memory
Proof
  rpt strip_tac >> fs[local_ptrs_rel_def] >>
  first_x_assum drule_all >> simp[]
QED

Theorem collision_normal_stop_observation[local]:
  !ctx fn cx lc R ce m es es' sa sb s0 ce'.
    stmt_frag ctx fn cx lc R ce m es (INL ()) es' /\
    m sa = (ce',sb) /\ fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved ce sa /\ ret_pc_ok ce sa s0 /\
    ~block_is_terminated sa /\ stmt_res_ok lc (INL ()) /\
    stmt_state_rel ctx fn ce cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!t. t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
         run_from 0 ctx fn t = Halt (stop_view t)) ==>
    ?t fuel. stmt_state_rel ctx fn ce' cx es' t /\
      run_from fuel ctx fn s0 = Halt (stop_view t)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_frag_def] >> disch_then drule_all >>
  simp[stmt_exit_loop_ctl] >> strip_tac >> gvs[] >>
  `run_from 0 ctx fn s = Halt (stop_view s)` by
    (first_x_assum irule >> gvs[stmt_lands_def]) >>
  qexists_tac `s` >> simp[] >>
  qpat_x_assum `!fuel. _` (qspec_then `0` mp_tac) >>
  simp[]
QED

Theorem collision_single_block_stop[local]:
  !sb ctx t.
    sb.cs_current_bb = "entry" /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    run_from 0 ctx (mk_raw_function "collision"
      [<|bb_label := "entry"; bb_instructions := sb.cs_current_insts ++
        [mk_inst sb.cs_next_id STOP [] []]|>]) t = Halt (stop_view t)
Proof
  rpt strip_tac >> irule run_from_stop_view >>
  qexists_tac `<|bb_label := "entry"; bb_instructions := sb.cs_current_insts ++
    [mk_inst sb.cs_next_id STOP [] []]|>` >>
  simp[mk_raw_function_def, lookup_block_def, listTheory.FIND_def,
       listTheory.INDEX_FIND_def, get_instruction_def, EL_APPEND_EQN] >>
  qexists_tac `sb.cs_next_id` >> simp[]
QED

Theorem abi_collision_fragment_negation[local]:
  !base lc rt ctx R.
    let ce = base with <|ce_vars := FEMPTY; ce_module_vars := FEMPTY;
      ce_struct_fields := FEMPTY; ce_is_ctor := F; ce_alloca_locals := T;
      ce_return_pc := NONE|> in
    let sa = <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
      cs_current_bb := "entry"; cs_current_insts := [];
      cs_blocks := []; cs_data_sections := [] |> in
    let stmt = AnnAssign "x" (BaseT (BytesT (Dynamic 32)))
        (TypeBuiltin (BaseT (BytesT (Fixed 32))) (AbiEncode T NONE)
          (TupleT [BaseT (UintT 256)]) [Literal (BaseT (UintT 256)) (IntL 32)]) in
    let sb = SND (stmt_env ce lc rt stmt sa) in
    let fn = mk_raw_function "collision"
      [<|bb_label := "entry"; bb_instructions :=
        sb.cs_current_insts ++ [mk_inst sb.cs_next_id STOP [] []]|>] in
    let es = (initial_state initial_machine_state [FEMPTY]) with outcomes := SOME [] in
    let es' = SND (eval_stmt empty_evaluation_context stmt es) in
    ~stmt_frag (ctx with ctx_functions := [fn]) fn empty_evaluation_context lc R ce
      (stmt_env ce lc rt stmt) es (INL ()) es'
Proof
  rpt gen_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `~stmt_frag ct fn cx lc R ce m es _ es'` >>
  qabbrev_tac `sa = <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
      cs_current_bb := "entry"; cs_current_insts := [];
      cs_blocks := []; cs_data_sections := [] |>` >>
  qabbrev_tac `out = m sa` >>
  qabbrev_tac `sb = SND out` >>
  qabbrev_tac `c = FST out` >>
  `m sa = (c,sb)` by simp[Abbr `c`, Abbr `sb`, Abbr `out`] >>
  `fn = mk_raw_function "collision"
      [<|bb_label := "entry"; bb_instructions :=
        sb.cs_current_insts ++ [mk_inst sb.cs_next_id STOP [] []]|>]` by
    simp[Abbr `fn`, Abbr `sb`, Abbr `out`, Abbr `m`, Abbr `sa`] >>
  strip_tac >>
  `fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
   local_ptrs_reserved ce sa /\ ret_pc_ok ce sa (init_venom_state "entry") /\
   ~block_is_terminated sa /\ stmt_res_ok lc (INL ()) /\
   ~(init_venom_state "entry").vs_halted /\
   (init_venom_state "entry").vs_current_bb = sa.cs_current_bb /\
   (init_venom_state "entry").vs_inst_idx = LENGTH sa.cs_current_insts` by
    (qspecl_then [`base' with ce_module_vars := FEMPTY`, `lc`, `rt`] mp_tac
       abi_collision_stmt_entry_code >>
     simp[Abbr `ce`, Abbr `fn`, Abbr `sb`, Abbr `out`, Abbr `m`, Abbr `sa`]) >>
  `stmt_state_rel ct fn ce cx es (init_venom_state "entry")` by
    (qspecl_then [`base'`, `lc`, `rt`, `ctx`] mp_tac
       abi_collision_initial_stmt_state_rel >>
     simp[Abbr `ct`, Abbr `fn`, Abbr `sb`, Abbr `out`, Abbr `m`,
          Abbr `ce`, Abbr `cx`, Abbr `es`, Abbr `sa`]) >>
  `sb.cs_current_bb = "entry"` by (unabbrev_all_tac >> EVAL_TAC) >>
  `!t. t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
       run_from 0 ct fn t = Halt (stop_view t)` by
    (rpt strip_tac >> simp[Abbr `fn`] >>
     irule collision_single_block_stop >> simp[]) >>
  drule_all collision_normal_stop_observation >> strip_tac >>
  `lookup_var "%0" (stop_view t) = SOME 0w /\ mload 0 (stop_view t) = 0w` by
    (qspecl_then [`base'`, `lc`, `rt`, `ctx`] mp_tac abi_collision_all_fuel_observation >>
     disch_then (qspec_then `fuel` mp_tac) >>
     qpat_x_assum `run_from fuel _ _ _ = _` mp_tac >>
     simp[Abbr `ct`, Abbr `fn`, Abbr `sb`, Abbr `out`, Abbr `m`, Abbr `ce`, Abbr `sa`]) >>
  `lookup_var "%0" t = SOME 0w /\ mload 0 t = 0w` by
    (qpat_x_assum `lookup_var _ (stop_view _) = _` mp_tac >>
     qpat_x_assum `mload _ (stop_view _) = _` mp_tac >>
     simp[stop_view_def, halt_state_def, lookup_var_def, mload_def]) >>
  `FLOOKUP c.ce_vars "x" = SOME (PtrVar (Var "%0") 64)` by
    (unabbrev_all_tac >> EVAL_TAC) >>
  `lookup_scopes "x" es'.scopes = SOME
      <|assignable := T; type := BaseTV (BytesT (Dynamic 32));
        value := BytesV (REPLICATE 31 0w ++ [32w]); popped := []|>` by
    (unabbrev_all_tac >> EVAL_TAC) >>
  `local_ptrs_rel fn c es'.scopes t` by
    (qpat_x_assum `stmt_state_rel ct fn c cx es' t` mp_tac >>
     simp_tac bool_ss [stmt_state_rel_def, state_rel_def]) >>
  drule_all collision_local_observation >>
  simp[val_in_memory_def, valueEncodingPropsTheory.mem_word_at_eq_mload]
QED

Theorem abi_collision_annassign_antecedent[local]:
  !ce ctx func.
    ce.ce_struct_fields = FEMPTY /\ ~ce.ce_is_ctor /\
    ce.ce_vars = FEMPTY /\ ce.ce_alloca_locals ==>
    let cx = empty_evaluation_context in
    let es = (initial_state initial_machine_state [FEMPTY]) with outcomes := SOME [] in
    let e = TypeBuiltin (BaseT (BytesT (Fixed 32))) (AbiEncode T NONE)
      (TupleT [BaseT (UintT 256)]) [Literal (BaseT (UintT 256)) (IntL 32)] in
    let dty = BaseT (BytesT (Dynamic 32)) in
    let tv = BaseTV (BytesT (Dynamic 32)) in
    ?env es'.
      eval_stmt cx (AnnAssign "x" dty e) es = (INL (),es') /\
      expr_sim_inv ce cx env es /\ ce.ce_alloca_locals /\
      acyclic_struct_metadata ce.ce_struct_fields /\
      ~is_word_type dty /\ ~(has_length_word dty /\ is_empty_value_expr e) /\
      lookup_scopes "x" es.scopes = NONE /\
      (!l. FLOOKUP ce.ce_vars "x" = SOME l ==> ?q z. l = PtrVar q z) /\
      type_widens_to (get_tenv cx) (lowered_value_type ce e) dty /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      evaluate_type (get_tenv cx) dty = SOME tv /\
      type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
      type_memory_bytes ce dty = type_memory_size tv /\
      0 < type_memory_size tv /\ type_memory_size tv < dimword (:256) /\
      0 < type_memory_size tv /\ type_memory_size tv + 64 < dimword (:256) /\
      (!v es1. (do raw <- eval_expr cx e; read_result cx raw od) es = (INL v,es1) ==>
         value_has_type tv v /\ value_has_type tv v) /\
      (!st0 c st1. declare_local ce "x" dty st0 = (c,st1) ==>
        expr_sim ctx func c cx (expr_type e) e es /\
        !sa sb op. lower_value compile_expr c (expr_type e) e sa = (op,sb) ==>
          cs_extends sa sb)
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  drule abi_collision_invariant_witness >> strip_tac >>
  qexists_tac `env` >>
  simp[abi_collision_source_probe, vyperASTTheory.expr_type_def] >>
  qmatch_goalsub_abbrev_tac `eval_stmt _ stmt es` >>
  `?out. eval_stmt empty_evaluation_context stmt es = (INL (),out)` by
    (qexists_tac `SND (eval_stmt empty_evaluation_context stmt es)` >>
     unabbrev_all_tac >> EVAL_TAC) >>
  qexists_tac `out` >> simp[] >>
  reverse (rpt conj_tac)
  >- (rpt gen_tac >> disch_tac >>
      drule_all abi_collision_declaration_contract >> simp[]) >>
  unabbrev_all_tac >> EVAL_TAC
QED

Theorem lowered_word_located_unwrap_probe[local]:
  !cenv ty ptr.
    is_word_type ty ==>
    unwrap_value cenv (LocatedValue ty (mk_ptr ptr LocMemory)) =
      compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory ptr
Proof
  simp[unwrap_value_def, contextTheory.mk_ptr_def]
QED

Theorem lower_abi_word_result_probe[local]:
  !cenv ty ensure mid target args sa sc ptr.
    is_word_type ty /\
    compile_expr cenv ty (TypeBuiltin ty (AbiEncode ensure mid) target args) sa =
      (LocatedValue ty (mk_ptr ptr LocMemory),sc) ==>
    lower_value compile_expr cenv ty
      (TypeBuiltin ty (AbiEncode ensure mid) target args) sa =
      compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory ptr sc
Proof
  rpt strip_tac >>
  simp[lower_value_def, comp_bind_def, lowered_word_located_unwrap_probe]
QED

Theorem lower_bytes_literal_actual_probe[local]:
  !cenv n bs sa buf sb.
    compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) ==>
    lower_value compile_expr cenv (BaseT (BytesT (Dynamic n)))
      (Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) sa =
      (buf.buf_operand,sb)
Proof
  rpt strip_tac >>
  simp[lower_value_def, Once compile_expr_def, vyperASTTheory.expr_type_def,
       compile_literal_vv_def,
       comp_bind_def, comp_return_def, unwrap_value_def, is_word_type_def,
       contextTheory.base_ptr_def, contextTheory.mk_ptr_def]
QED

Theorem lowered_value_type_exception_partition[local]:
  !cenv e.
    lowered_value_type cenv e = expr_type e \/
    (?n s. e = Literal (BaseT (StringT n)) (StringL s)) \/
    (?n bs. e = Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) \/
    (?ty ensure method_id tys args.
      e = TypeBuiltin ty (AbiEncode ensure method_id) tys args)
Proof
  ho_match_mp_tac lowered_value_type_ind >>
  simp[lowered_value_type_def, vyperASTTheory.expr_type_def]
QED

Theorem lowered_value_type_equal_evaluates[local]:
  !cenv e tenv stv.
    lowered_value_type cenv e = expr_type e /\
    evaluate_type tenv (lowered_value_type cenv e) = SOME stv ==>
    evaluate_type tenv (expr_type e) = SOME stv
Proof
  rpt strip_tac >> gvs[]
QED

(* Interface probe: a literal's declared bound need not evaluate even when
   its lowered (actual-length) type does. *)
Theorem lowered_bytes_literal_annotation_probe[local]:
  !cenv cx es.
    lowered_value_type cenv
      (Literal (BaseT (BytesT (Dynamic (dimword (:256))))) (BytesL [])) =
      BaseT (BytesT (Dynamic 0)) /\
    is_bytestring_type (lowered_value_type cenv
      (Literal (BaseT (BytesT (Dynamic (dimword (:256))))) (BytesL []))) /\
    evaluate_type (get_tenv cx)
      (BaseT (BytesT (Dynamic (dimword (:256))))) = NONE /\
    (do raw <- eval_expr cx
          (Literal (BaseT (BytesT (Dynamic (dimword (:256))))) (BytesL []));
        read_result cx raw od) es = (INL (BytesV []), es)
Proof
  simp[lowered_value_type_def, is_bytestring_type_def,
       vyperValueTheory.evaluate_type_def, Once evaluate_def,
       bind_def, read_result_def, return_def,
       vyperValueOperationTheory.evaluate_literal_def]
QED

Theorem compile_assign_memory_typed_extends[local]:
  !cenv dst src loc dty sty info sz sa sb.
    compile_assign_value cenv dst LocMemory src F loc dty sty info sz sa = ((),sb) ==>
    cs_extends sa sb
Proof
  rpt gen_tac >> strip_tac >>
  `exprLoweringProps$ci_mono sa
     (SND (compile_assign_value cenv dst LocMemory src F loc dty sty info sz sa))` suffices_by
    gvs[exprLoweringPropsTheory.ci_mono_def] >>
  pop_assum kall_tac >>
  simp[compile_assign_value_def] >>
  Cases_on `loc = SOME LocMemory` >> simp[] >>
  rpt (FIRST [ho_match_mp_tac exprLoweringPropsTheory.ci_mono_bind,
              ho_match_mp_tac exprLoweringPropsTheory.ci_mono_ignore_bind,
              conj_tac, gen_tac]) >>
  simp[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,
       exprLoweringPropsTheory.ci_mono_comp_return,
       exprLoweringPropsTheory.ci_mono_compile_copy_memory,
       exprLoweringPropsTheory.ci_mono_compile_store_memory]
QED

Theorem assign_local_memory_typed_code_parts:
  !cenv lctx ty id e sa sf c func p sz vtyp.
    stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e) sa = (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vtyp /\ ~is_word_type vtyp /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    fn_has_code sa sf func ==>
    c = cenv /\
    ?vv sV sB op.
      compile_expr cenv (expr_type e) e sa = (vv, sV) /\
      unwrap_value cenv vv sV = (op, sB) /\
      lower_value compile_expr cenv (expr_type e) e sa = (op, sB) /\
      compile_assign_value cenv (Var p) LocMemory op F (vv_location vv)
        vtyp (lowered_value_type cenv e)
        (case vtyp of ArrayT elem_ty (Dynamic _) =>
           SOME ((type_memory_bytes cenv elem_ty + 31) DIV 32,
                 type_memory_bytes cenv elem_ty) | _ => NONE)
        (type_memory_bytes cenv vtyp) sB = ((), sf) /\
      cs_extends sa sB /\ cs_extends sB sf /\
      fn_has_code sa sB func /\ fn_has_code sB sf func
Proof
  rpt gen_tac >> strip_tac >>
  drule stmt_env_assign >> strip_tac >>
  qpat_x_assum `c = cenv` SUBST_ALL_TAC >>
  drule compile_get_target_ptr_local >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss())
    [Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, LET_THM] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv, sV)` >>
  Cases_on `unwrap_value cenv vv sV` >>
  rename1 `unwrap_value _ _ _ = (op, sB)` >>
  simp[] >> strip_tac >>
  `lower_value compile_expr cenv (expr_type e) e sa = (op, sB)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa sB` by
    metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows] >>
  `cs_extends sB sf` by metis_tac[compile_assign_memory_typed_extends] >>
  `fn_has_code sa sB func /\ fn_has_code sB sf func` by
    metis_tac[fn_has_code_split] >> gvs[]
QED

Theorem declare_local_typed_memory_metadata:
  !cenv id vtyp sa c st.
    declare_local cenv id vtyp sa = (c, st) /\ cenv.ce_alloca_locals ==>
    c.ce_struct_fields = cenv.ce_struct_fields /\
    (!ty. type_memory_bytes c ty = type_memory_bytes cenv ty) /\
    (!e. lowered_value_type c e = lowered_value_type cenv e)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  `c.ce_struct_fields = cenv.ce_struct_fields` by
    (qpat_x_assum `c with <| ce_vars := _; ce_var_type := _;
                            ce_dynarray_capacity := _ |> = cenv` mp_tac >>
     simp[compile_env_component_equality]) >>
  simp[] >> conj_tac
  >- (`!env ty. env.ce_struct_fields = cenv.ce_struct_fields ==>
          type_memory_bytes env ty = type_memory_bytes cenv ty` suffices_by
        metis_tac[] >>
      ho_match_mp_tac type_memory_bytes_ind >>
      rw[type_memory_bytes_def] >>
      AP_TERM_TAC >> irule MAP_CONG >> simp[]) >>
  gen_tac >> simp[oneline lowered_value_type_def]
QED

Theorem annassign_memory_typed_lower_parts[local]:
  !cenv lctx ty id vtyp e st sf p sz.
    compile_stmt cenv lctx ty (AnnAssign id vtyp e) st = ((), sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    ~is_word_type vtyp /\ ~(has_length_word vtyp /\ is_empty_value_expr e) ==>
    ?sA sV sB vv op.
      emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((), sA) /\
      compile_expr cenv (expr_type e) e sA = (vv, sV) /\
      unwrap_value cenv vv sV = (op, sB) /\
      lower_value compile_expr cenv (expr_type e) e sA = (op, sB) /\
      compile_assign_value cenv (Var p) LocMemory op F (vv_location vv)
        vtyp (lowered_value_type cenv e)
        (case vtyp of ArrayT elem_ty (Dynamic _) =>
           SOME ((type_memory_bytes cenv elem_ty + 31) DIV 32,
                 type_memory_bytes cenv elem_ty) | _ => NONE)
        (type_memory_bytes cenv vtyp) sB = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, emit_local_alloca_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  imp_res_tac loweringSliceTheory.emit_inst_unit >>
  gvs[lower_value_def, comp_bind_def] >> metis_tac[]
QED

Theorem annassign_memory_typed_code_parts:
  !cenv lctx ty id vtyp e sa sf c func.
    stmt_env cenv lctx ty (AnnAssign id vtyp e) sa = (c, sf) /\
    cenv.ce_alloca_locals /\ ~is_word_type vtyp /\
    ~(has_length_word vtyp /\ is_empty_value_expr e) /\
    fn_has_code sa sf func /\ local_ptrs_reserved cenv sa /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       !a b op. lower_value compile_expr c (expr_type e) e a = (op, b) ==>
                cs_extends a b) ==>
    ?st sA sV sB vv op p.
      declare_local cenv id vtyp sa = (c, st) /\
      FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv vtyp)) /\
      emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv vtyp))] [p] st = ((), sA) /\
      compile_expr c (expr_type e) e sA = (vv, sV) /\
      unwrap_value c vv sV = (op, sB) /\
      lower_value compile_expr c (expr_type e) e sA = (op, sB) /\
      compile_assign_value c (Var p) LocMemory op F (vv_location vv) vtyp
        (lowered_value_type cenv e)
        (case vtyp of ArrayT elem_ty (Dynamic _) =>
           SOME ((type_memory_bytes c elem_ty + 31) DIV 32,
                 type_memory_bytes c elem_ty) | _ => NONE)
        (type_memory_bytes c vtyp) sB = ((), sf) /\
      local_ptrs_reserved c st /\ local_ptrs_reserved c sA /\ not_fresh_at sA p /\
      cs_extends st sA /\ cs_extends sA sB /\ cs_extends sB sf /\
      fn_has_code st sA func /\ fn_has_code sA sB func /\ fn_has_code sB sf func /\
      MEM (mk_inst st.cs_next_id ALLOCA
             [Lit (n2w (type_memory_bytes cenv vtyp))] [p]) (fn_insts func)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule stmt_env_annassign >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  drule_all declare_local_typed_memory_metadata >> strip_tac >>
  `lowered_value_type c e = lowered_value_type cenv e` by metis_tac[] >>
  drule_all annassign_memory_typed_lower_parts >>
  disch_then (qx_choosel_then [`sA`, `sV`, `sB`, `vv`, `op`] strip_assume_tac) >>
  `fn_has_code st sf func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  `cs_extends sA sB /\ cs_extends sB sf` by
    metis_tac[compile_assign_memory_typed_extends] >>
  `cs_extends sA sf` by metis_tac[cs_extends_trans] >>
  drule_all annassign_alloca_code >> strip_tac >>
  `fn_has_code sA sB func /\ fn_has_code sB sf func` by
    metis_tac[fn_has_code_split] >>
  qexistsl [`st`, `sA`, `sV`, `sB`, `vv`, `op`,
            `STRING #"%" (toString sa.cs_next_var)`] >>
  simp[] >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[]
QED

Theorem lowered_nonbytestring_type_eq[local]:
  !cenv e. ~is_bytestring_type (lowered_value_type cenv e) ==>
    lowered_value_type cenv e = expr_type e
Proof
  ho_match_mp_tac lowered_value_type_ind >>
  simp[lowered_value_type_def, is_bytestring_type_def, LET_THM]
QED

Theorem compile_intcall_stack_operand_zero[local]:
  !cfn cenv ret_ty ty fid args default_ret sa vt op sb.
    compile_call cfn cenv ret_ty ty (IntCall fid) args default_ret sa =
      (StackValue vt op, sb) ==>
    op = Lit 0w
Proof
  rpt gen_tac >>
  simp[compile_call_def] >>
  pairarg_tac >> simp[] >>
  Cases_on `compile_multi_vvs cfn cenv args sa` >> simp[] >>
  rename1 `compile_multi_vvs _ _ _ _ = (avs,s1)` >>
  Cases_on `returns_count > 0`
  >- (simp[] >> Cases_on `compile_alloc_buffer (32 * returns_count) s1` >>
      simp[] >> rpt (pairarg_tac >> gvs[])) >>
  Cases_on `return_buf_size > 0`
  >- (simp[] >> Cases_on `compile_alloc_buffer return_buf_size s1` >>
      simp[] >> rpt (pairarg_tac >> gvs[])) >>
  simp[] >> rpt (pairarg_tac >> gvs[])

QED

Theorem typed_bytestring_expr_source[local]:
  !ctx func cenv cx e es sa sb s0 es1 v op s env dty dtv.
    expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
    well_typed_expr env e /\ expr_sim_inv cenv cx env es /\
    is_bytestring_type (lowered_value_type cenv e) /\
    is_bytestring_type dty /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type dtv v ==>
    ?sw. eval_operand op s = SOME sw /\
         val_in_memory dtv v (w2n sw) s.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  `is_bytestring_type (expr_type e)` by
    metis_tac[lowered_value_type_shape] >>
  `~is_word_type (expr_type e)` by
    metis_tac[is_bytestring_word_type] >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by
    (`env.type_defs = get_tenv cx` by
       gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
     `!id t. FLOOKUP env.var_types id = SOME t ==>
             well_formed_type env.type_defs t` by
       (gvs[expr_sim_inv_def, well_formed_type_def] >>
        metis_tac[env_consistent_var_type_evaluates]) >>
     drule_all exprSafeOperandTheory.well_typed_expr_type_well_formed >>
     simp[well_formed_type_def, IS_SOME_EXISTS]) >>
  gvs[expr_post_def, expr_val_rel_def] >>
  metis_tac[bytestring_val_in_memory_transfer]
QED

Theorem typed_memory_expr_source:
  !ctx func cenv cx e es sa sb s0 es1 v op s stv.
    expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
    ~is_bytestring_type (lowered_value_type cenv e) /\
    ~is_word_type (lowered_value_type cenv e) /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv ==>
    val_wf stv v /\
    expr_val_at cenv cx (lowered_value_type cenv e) sa sb es1 v op s /\
    ?w. eval_operand op s = SOME w /\
        val_in_memory stv v (w2n w) s.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  drule lowered_nonbytestring_type_eq >> strip_tac >>
  gvs[expr_post_def, expr_val_rel_def] >>
  metis_tac[expr_val_at_def]
QED

Theorem nonbytestring_full_footprint[local]:
  !tenv t tv v.
    evaluate_type tenv t = SOME tv /\ ~is_bytestring_type t ==>
    val_footprint tv v = type_memory_size tv
Proof
  rpt gen_tac >> Cases_on `t` >>
  simp[is_bytestring_type_def, vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> Cases_on `v` >>
  gvs[val_footprint_def, is_bytestring_type_def]
QED

(* Separation keeps both allocation and borrowed-local source ownership. *)
Theorem typed_source_decl_alloca_separate[local]:
  !cenv cx t sa sb es v op s tv func inst q dst dsz sw.
    expr_val_at cenv cx t sa sb es v op s /\
    evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
    val_footprint tv v = type_memory_size tv /\
    0 < type_memory_size tv /\ 0 < dsz /\
    eval_operand op s = SOME sw /\
    alloca_inv s /\ fn_inst_ids_distinct func /\
    local_ptrs_rel func cenv es.scopes s /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
    not_local_ptr cenv es.scopes q /\
    inst.inst_id < sa.cs_next_id /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (dst,dsz) ==>
    w2n sw + type_memory_size tv <= dst \/
    dst + dsz <= w2n sw
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[]
  >- (gvs[venomMemDefsTheory.alloca_inv_def,
           venomMemDefsTheory.allocas_non_overlapping_def] >>
      `aid <> inst.inst_id` by decide_tac >>
      first_x_assum drule_all >> decide_tac) >>
  `regions_disjoint dst dsz b sz` by
    (irule localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     metis_tac[]) >>
  gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem typed_decl_post_separate[local]:
  !ctx func cenv cx e es sa sb s0 es1 v op s stv inst p dw dsz.
    expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
    ~is_bytestring_type (lowered_value_type cenv e) /\
    ~is_word_type (lowered_value_type cenv e) /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    0 < type_memory_size stv /\ 0 < dsz /\
    not_fresh_at sa p /\ lookup_var p s0 = SOME dw /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n dw,dsz) /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [p] /\
    inst.inst_id < sa.cs_next_id /\
    not_local_ptr cenv es1.scopes p /\ fn_inst_ids_distinct func ==>
    lookup_var p s = SOME dw /\
    ?sw. eval_operand op s = SOME sw /\
         (w2n sw + type_memory_size stv <= w2n dw \/
          w2n dw + dsz <= w2n sw)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_memory_expr_source >> strip_tac >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[nonbytestring_full_footprint] >>
  gvs[expr_post_def] >>
  `lookup_var p s = SOME dw /\
   FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,dsz)` by metis_tac[] >>
  `alloca_inv s /\ local_ptrs_rel func cenv es1.scopes s` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `expr_val_at _ _ (expr_type e) _ _ _ _ _ _` kall_tac >>
  drule_all typed_source_decl_alloca_separate >> simp[]
QED

Theorem typed_expr_source_end_lt[local]:
  !ctx func cenv cx es s t sa sb v op tv w.
    stmt_state_rel ctx func cenv cx es s /\
    expr_val_at cenv cx t sa sb es v op s /\
    evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
    ~is_bytestring_type t /\ 0 < type_memory_size tv /\
    eval_operand op s = SOME w ==>
    w2n w + type_memory_size tv < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  `val_footprint tv v = type_memory_size tv` by
    metis_tac[nonbytestring_full_footprint] >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[exprLoweringPropsTheory.stmt_state_rel_def,
              exprLoweringPropsTheory.alloca_room_next_lt] >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >>
  gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def,
      venomMemDefsTheory.alloca_inv_def,
      venomMemDefsTheory.alloca_next_valid_def]
  >- (first_x_assum drule >> decide_tac) >>
  gvs[local_region_def, local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >> decide_tac
QED

Theorem typed_alloca_end_lt[local]:
  !ctx func cenv cx es s aid b sz n.
    stmt_state_rel ctx func cenv cx es s /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ n <= sz ==>
    b + n < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[exprLoweringPropsTheory.stmt_state_rel_def,
              exprLoweringPropsTheory.alloca_room_next_lt] >>
  gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def,
      venomMemDefsTheory.alloca_inv_def,
      venomMemDefsTheory.alloca_next_valid_def] >>
  first_x_assum drule >> decide_tac
QED

Theorem typed_decl_post_copy_run[local]:
  !ctx func cenv cx env e es sa sb sf s0 es1 v op s stv dtv
   inst p dw dsz dty.
    expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
    expr_sim_inv cenv cx env es /\
    ~is_bytestring_type (lowered_value_type cenv e) /\
    ~is_word_type (lowered_value_type cenv e) /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    0 < type_memory_size stv /\
    not_fresh_at sa p /\ lookup_var p s0 = SOME dw /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n dw,dsz) /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [p] /\
    inst.inst_id < sa.cs_next_id /\
    not_local_ptr cenv es1.scopes p /\ fn_inst_ids_distinct func /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    0 < type_memory_size dtv /\ type_memory_size dtv <= dsz /\
    compile_store_memory_typed cenv (Var p) dty op
      (lowered_value_type cenv e) sb = ((),sf) /\
    fn_has_code sb sf func /\
    (!x. op = Var x ==> not_fresh_at sb x) /\ not_fresh_at sb p /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt gen_tac >> strip_tac >>
  `0 < dsz` by decide_tac >>
  drule_all typed_decl_post_separate >> strip_tac >>
  drule_all typed_memory_expr_source >> strip_tac >>
  gvs[] >>
  `stmt_state_rel ctx func cenv cx es1 s /\
   FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,dsz)` by
    (gvs[expr_post_def] >> metis_tac[]) >>
  `w2n dw + type_memory_size dtv < dimword (:256)` by
    (drule_all typed_alloca_end_lt >> simp[]) >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (drule_all typed_expr_source_end_lt >> simp[]) >>
  `val_wf stv v /\ val_wf dtv v` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  drule compile_store_memory_typed_run >>
  disch_then (qspec_then `get_tenv cx` mp_tac) >>
  simp[venomStateTheory.eval_operand_def] >>
  disch_then irule >>
  gvs[expr_sim_inv_def] >> rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, decide_tac, metis_tac[]]
QED

Theorem typed_decl_staged_code_parts[local]:
  !cenv dst src dty sty info bytes sa sb func.
    compile_assign_value cenv dst LocMemory src F (SOME LocMemory)
      dty sty info bytes sa = ((),sb) /\
    0 < type_memory_bytes cenv sty /\ fn_has_code sa sb func ==>
    ?sx sm sn tmp.
      sx = sa with cs_next_var := sa.cs_next_var + 1 /\
      ~not_fresh_at sa tmp /\ not_fresh_at sn tmp /\
      sa.cs_next_var <= sn.cs_next_var /\
      emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv sty))] [tmp]
        sx = ((),sm) /\
      emit_void MCOPY [Var tmp; src; Lit (n2w (type_memory_bytes cenv sty))]
        sm = ((),sn) /\
      compile_store_memory cenv (Var tmp) dst dty sty sn = ((),sb) /\
      cs_extends sa sx /\ cs_extends sx sm /\ cs_extends sm sn /\ cs_extends sn sb /\
      fn_has_code sx sm func /\ fn_has_code sm sn func /\
      fn_has_code sn sb func
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_assign_value_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule loweringHaltTheory.compile_alloc_buffer_emission >>
  disch_then (qx_choosel_then [`sx`, `tmp`] strip_assume_tac) >>
  rename1 `compile_copy_memory _ _ _ sm = ((),sn)` >>
  `emit_void MCOPY [Var tmp; src; Lit (n2w (type_memory_bytes cenv sty))]
      sm = ((),sn)` by
    (Cases_on `type_memory_bytes cenv sty` >> gvs[contextTheory.compile_copy_memory_def]) >>
  `cs_extends sm sn` by
    metis_tac[cs_appends_def, cs_appends_emit_helpers] >>
  `cs_extends sn sb` by
    (`exprLoweringProps$ci_mono sn
       (SND (compile_store_memory cenv (Var tmp) dst dty sty sn))` suffices_by
       gvs[exprLoweringPropsTheory.ci_mono_def] >>
     simp[exprLoweringPropsTheory.ci_mono_compile_store_memory]) >>
  `cs_extends sx sn /\ cs_extends sa sn` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sn func /\ fn_has_code sn sb func` by metis_tac[fn_has_code_split] >>
  `fn_has_code sa sx func /\ fn_has_code sx sn func` by metis_tac[fn_has_code_split] >>
  `fn_has_code sx sm func /\ fn_has_code sm sn func` by metis_tac[fn_has_code_split] >>
  `sm.cs_next_var = sn.cs_next_var` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_void_def, emit_def, fresh_id_def, comp_bind_def, comp_return_def] >>
     strip_tac >> gvs[]) >>
  `sm.cs_next_var = sx.cs_next_var` by
    (qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_inst_def, emit_def, fresh_id_def, comp_bind_def, comp_return_def] >>
     strip_tac >> gvs[]) >>
  qexistsl [`sm`, `sn`, `tmp`] >> gvs[] >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists `sm` >> simp[]
QED

Theorem typed_decl_stage_owned_run[local]:
  !ctx func cenv cx es sb sf s op dty sty info bytes stv v sw p dw aid dsz.
    compile_assign_value cenv (Var p) LocMemory op F (SOME LocMemory)
      dty sty info bytes sb = ((),sf) /\
    type_memory_bytes cenv sty = type_memory_size stv /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sb /\
    (!x. op = Var x ==> not_fresh_at sb x) /\ not_fresh_at sb p /\
    eval_operand op s = SOME sw /\ lookup_var p s = SOME dw /\
    FLOOKUP s.vs_allocas aid = SOME (w2n dw,dsz) /\
    val_in_memory stv v (w2n sw) s.vs_memory /\ val_wf stv v /\
    val_footprint stv v <= type_memory_size stv /\
    fn_has_code sb sf func /\ ~s.vs_halted /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?sn tmp u uw taid.
      taid = sb.cs_next_id /\
      compile_store_memory cenv (Var tmp) (Var p) dty sty sn = ((),sf) /\
      cs_extends sb sn /\ sb.cs_next_var <= sn.cs_next_var /\
      fn_has_code sn sf func /\ not_fresh_at sn tmp /\
      stmt_state_rel ctx func cenv cx es u /\
      lookup_var tmp u = SOME uw /\ lookup_var p u = SOME dw /\
      FLOOKUP u.vs_allocas taid = SOME (w2n uw,type_memory_size stv) /\
      FLOOKUP u.vs_allocas aid = SOME (w2n dw,dsz) /\
      val_in_memory stv v (w2n uw) u.vs_memory /\
      (!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x s) /\
      (!a entry. FLOOKUP s.vs_allocas a = SOME entry ==>
                 FLOOKUP u.vs_allocas a = SOME entry) /\
      ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
      u.vs_inst_idx = LENGTH sn.cs_current_insts /\
      (!fuel r. run_from fuel ctx func u = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt gen_tac >> strip_tac >>
  `0 < type_memory_bytes cenv sty` by simp[] >>
  drule_all typed_decl_staged_code_parts >>
  disch_then (qx_choosel_then [`sx`, `sm`, `sn`, `tmp`] strip_assume_tac) >>
  `MEM (mk_inst sx.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv sty))] [tmp]) (fn_insts func)` by
    (irule loweringHaltTheory.emit_inst_fn_member >> qexists `sm` >> simp[]) >>
  `not_local_ptr cenv es.scopes tmp` by
    (gvs[compileEnvTheory.local_ptrs_reserved_def,
         compileEnvTheory.not_local_ptr_def] >> metis_tac[]) >>
  `op <> Var tmp /\ p <> tmp` by metis_tac[] >>
  `s.vs_current_bb = sx.cs_current_bb /\
   s.vs_inst_idx = LENGTH sx.cs_current_insts` by simp[] >>
  `type_memory_bytes cenv sty < dimword (:256) /\
   val_footprint stv v <= type_memory_bytes cenv sty` by metis_tac[] >>
  drule_all alloc_copy_memory_owned_run >>
  disch_then (qx_choosel_then [`u`, `uw`] strip_assume_tac) >>
  `!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> `x <> tmp` by (strip_tac >> gvs[]) >> simp[]) >>
  qexistsl [`sn`, `tmp`, `u`, `uw`, `sx.cs_next_id`] >>
  simp[] >> conj_tac
  >- metis_tac[cs_extends_trans] >>
  metis_tac[]
QED

Theorem typed_owned_allocas_copy_run[local]:
  !ctx func cenv cx env es0 es s sa sf src p sw dw aid bid stv dtv v sty dty dsz.
    stmt_state_rel ctx func cenv cx es s /\ expr_sim_inv cenv cx env es0 /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    FLOOKUP s.vs_allocas aid = SOME (w2n sw,type_memory_size stv) /\
    FLOOKUP s.vs_allocas bid = SOME (w2n dw,dsz) /\ aid <> bid /\
    0 < type_memory_size stv /\ 0 < type_memory_size dtv /\
    type_memory_size dtv <= dsz /\
    compile_store_memory_typed cenv (Var p) dty src sty sa = ((),sf) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    eval_operand src s = SOME sw /\ lookup_var p s = SOME dw /\
    (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
    fn_has_code sa sf func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt gen_tac >> strip_tac >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (irule typed_alloca_end_lt >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `w2n dw + type_memory_size dtv < dimword (:256)` by
    (irule typed_alloca_end_lt >> metis_tac[]) >>
  `w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw` by
    (gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def,
         venomMemDefsTheory.alloca_inv_def,
         venomMemDefsTheory.allocas_non_overlapping_def] >>
     first_x_assum drule_all >> decide_tac) >>
  `val_wf stv v /\ val_wf dtv v` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  drule compile_store_memory_typed_run >>
  disch_then (qspec_then `get_tenv cx` mp_tac) >>
  simp[venomStateTheory.eval_operand_def] >>
  disch_then irule >> gvs[expr_sim_inv_def] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, metis_tac[]]
QED

Theorem typed_same_layout_store_run[local]:
  !ctx func cenv tenv s sa sf src dst sw dw tv ty v.
    compile_store_memory cenv src dst ty ty sa = ((),sf) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    ~is_word_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
    val_in_memory tv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    type_memory_size tv + 64 < dimword (:256) /\
    fn_has_code sa sf func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. val_in_memory tv v (w2n dw) t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt gen_tac >> strip_tac >>
  `val_wf tv v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  drule valueCopyTheory.compile_store_memory_run_size_bound_with_capacity >>
  disch_then (qspecl_then [`s`, `tenv`, `tv`, `v`, `sw`, `dw`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `frag_exec ctx sa sf (\u. u = s)
    (\u. val_in_memory tv v (w2n dw) u.vs_memory /\
      (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
        mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH u.vs_memory) (\r. F)` by
    (irule frag_exec_run_inst_seq >>
     gvs[exprLoweringPropsTheory.same_blocks_def, venomStateTheory.lookup_var_def] >>
     conj_tac
     >- (qpat_x_assum `t with <|vs_memory := _; vs_vars := _|> = s` mp_tac >>
         simp[venomStateTheory.venom_state_component_equality]) >>
     first_assum ACCEPT_TAC) >>
  drule stmtSimDeclTheory.frag_exec_no_exit_run >>
  disch_then (qspecl_then [`func`, `s`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  qexists `u` >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem typed_decl_staged_convert_run[local]:
  !ctx func cenv cx env es0 es sb sf s op dty sty info bytes stv dtv v sw p dw aid dsz.
    compile_assign_value cenv (Var p) LocMemory op F (SOME LocMemory)
      dty sty info bytes sb = ((),sf) /\
    type_memory_bytes cenv sty = type_memory_size stv /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    0 < type_memory_size dtv /\ type_memory_size dtv <= dsz /\
    stmt_state_rel ctx func cenv cx es s /\ expr_sim_inv cenv cx env es0 /\
    acyclic_struct_metadata cenv.ce_struct_fields /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sb /\
    (!x. op = Var x ==> not_fresh_at sb x) /\ not_fresh_at sb p /\
    eval_operand op s = SOME sw /\ lookup_var p s = SOME dw /\
    FLOOKUP s.vs_allocas aid = SOME (w2n dw,dsz) /\ aid < sb.cs_next_id /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    val_footprint stv v <= type_memory_size stv /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    ~is_word_type dty /\ ~is_bytestring_type dty /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    type_memory_size dtv + 64 < dimword (:256) /\
    fn_has_code sb sf func /\ ~s.vs_halted /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?sn u t.
      cs_extends sb sn /\ sb.cs_next_var <= sn.cs_next_var /\
      stmt_state_rel ctx func cenv cx es u /\
      lookup_var p u = SOME dw /\
      (!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x s) /\
      (!a entry. FLOOKUP s.vs_allocas a = SOME entry ==>
                 FLOOKUP u.vs_allocas a = SOME entry) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
                vs_prev_bb := u.vs_prev_bb; vs_current_bb := u.vs_current_bb;
                vs_inst_idx := u.vs_inst_idx|>) = u /\
      (!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x u) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
      LENGTH u.vs_memory <= LENGTH t.vs_memory /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt gen_tac >> strip_tac >>
  `val_wf stv v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  drule_all typed_decl_stage_owned_run >>
  disch_then (qx_choosel_then [`sn`, `tmp`, `u`, `uw`, `taid`] strip_assume_tac) >>
  `not_fresh_at sn p` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `sb` >> simp[]) >>
  `eval_operand (Var tmp) u = SOME uw` by simp[venomStateTheory.eval_operand_def] >>
  `taid <> aid` by decide_tac >>
  `!x. Var tmp = Var x ==> not_fresh_at sn x` by simp[] >>
  `!x. Var p = Var x ==> not_fresh_at sn x` by simp[] >>
  `?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
                vs_prev_bb := u.vs_prev_bb; vs_current_bb := u.vs_current_bb;
                vs_inst_idx := u.vs_inst_idx|>) = u /\
      (!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x u) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
      LENGTH u.vs_memory <= LENGTH t.vs_memory /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func u = r)` by
    (Cases_on `dty = sty`
     >- (qpat_x_assum `dty = sty` SUBST_ALL_TAC >>
         `stv = dtv` by
           (qpat_x_assum `evaluate_type _ _ = SOME stv` mp_tac >>
            qpat_x_assum `evaluate_type _ _ = SOME dtv` mp_tac >> simp[]) >>
         qpat_x_assum `stv = dtv` SUBST_ALL_TAC >>
         `eval_operand (Var p) u = SOME dw` by simp[venomStateTheory.eval_operand_def] >>
         drule_all typed_same_layout_store_run >> simp[]) >>
     `compile_store_memory_typed cenv (Var p) dty (Var tmp) sty sn = ((),sf)` by
       gvs[contextTheory.compile_store_memory_def] >>
     drule_all typed_owned_allocas_copy_run >> simp[]) >>
  qexistsl [`sn`, `u`, `t`] >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  rpt strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx func t = r /\ _ ==> _`
    (qspec_then `fuel` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx func u = r /\ _ ==> _` drule >>
  simp[]
QED
Theorem typed_decl_post_assign_run[local]:
  !ctx func cenv cx env e es sa sb sf s0 es1 v op s stv dtv
   inst p dw dsz dty loc info bytes.
    expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
    expr_sim_inv cenv cx env es /\
    ~is_bytestring_type (lowered_value_type cenv e) /\
    ~is_word_type (lowered_value_type cenv e) /\
    ~is_word_type dty /\ ~is_bytestring_type dty /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    type_memory_size dtv + 64 < dimword (:256) /\
    not_fresh_at sa p /\ lookup_var p s0 = SOME dw /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n dw,dsz) /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [p] /\
    inst.inst_id < sa.cs_next_id /\ inst.inst_id < sb.cs_next_id /\
    not_local_ptr cenv es1.scopes p /\ fn_inst_ids_distinct func /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    0 < type_memory_size dtv /\ type_memory_size dtv <= dsz /\
    compile_assign_value cenv (Var p) LocMemory op F loc dty
      (lowered_value_type cenv e) info bytes sb = ((),sf) /\
    fn_has_code sb sf func /\ local_ptrs_reserved cenv sb /\
    (!x. op = Var x ==> not_fresh_at sb x) /\ not_fresh_at sb p /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?sn u t.
      cs_extends sb sn /\ sb.cs_next_var <= sn.cs_next_var /\
      stmt_state_rel ctx func cenv cx es1 u /\ lookup_var p u = SOME dw /\
      (!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x s) /\
      (!a entry. FLOOKUP s.vs_allocas a = SOME entry ==>
                 FLOOKUP u.vs_allocas a = SOME entry) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
                vs_prev_bb := u.vs_prev_bb; vs_current_bb := u.vs_current_bb;
                vs_inst_idx := u.vs_inst_idx|>) = u /\
      (!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x u) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
      LENGTH u.vs_memory <= LENGTH t.vs_memory /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_memory_expr_source >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es1 s /\
   lookup_var p s = SOME dw /\
   FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,dsz)` by
    (gvs[expr_post_def] >> metis_tac[]) >>
  `val_footprint stv v <= type_memory_size stv` by
    metis_tac[nonbytestring_full_footprint, arithmeticTheory.LESS_EQ_REFL] >>
  Cases_on `loc = SOME LocMemory`
  >- (qpat_x_assum `loc = SOME LocMemory` SUBST_ALL_TAC >>
      drule_all typed_decl_staged_convert_run >> simp[]) >>
  `compile_store_memory cenv op (Var p) dty (lowered_value_type cenv e) sb = ((),sf)` by
    gvs[compile_assign_value_def] >>
  qexistsl [`sb`, `s`] >> simp[compileEnvTheory.cs_extends_refl] >>
  Cases_on `dty = lowered_value_type cenv e`
  >- suspend "same" >>
  suspend "different"
QED

Resume typed_decl_post_assign_run[same]:
  qpat_x_assum `dty = lowered_value_type cenv e` SUBST_ALL_TAC >>
  `stv = dtv` by
    (qpat_x_assum `evaluate_type _ _ = SOME stv` mp_tac >>
     qpat_x_assum `evaluate_type _ _ = SOME dtv` mp_tac >> simp[]) >>
  qpat_x_assum `stv = dtv` SUBST_ALL_TAC >>
  `!x. Var p = Var x ==> not_fresh_at sb x` by simp[] >>
  `eval_operand (Var p) s = SOME dw` by simp[venomStateTheory.eval_operand_def] >>
  drule_all typed_same_layout_store_run >> simp[]
QED

Resume typed_decl_post_assign_run[different]:
  `compile_store_memory_typed cenv (Var p) dty op
     (lowered_value_type cenv e) sb = ((),sf)` by
    gvs[contextTheory.compile_store_memory_def] >>
  drule_all typed_decl_post_copy_run >> simp[]
QED

Finalise typed_decl_post_assign_run

Theorem typed_decl_store_frame[local]:
  !func cenv cx es s t sa id p sz w inst v tyv sc rest a ctx.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!b n. b + n <= w2n w \/ w2n w + type_memory_size tyv <= b ==>
           mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    type_memory_size tyv <= sz /\ val_wf tyv v /\
    val_in_memory tyv v (w2n w) t.vs_memory ==>
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
        (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t
Proof
  rpt gen_tac >> strip_tac >>
  `!q. q = p \/ ~not_local_ptr cenv es.scopes q ==>
       lookup_var q t = lookup_var q s` by
    (rpt strip_tac >- simp[] >>
     `not_fresh_at sa q` by
       (gvs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >> simp[]) >>
  `!n b sz'. n <> id /\ local_region cenv es.scopes s n b sz' ==>
       mem_bytes_at b sz' s.vs_memory = mem_bytes_at b sz' t.vs_memory` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) sz b sz'` by
       (irule local_ptrs_rel_alloca_disjoint >>
        qexistsl [`cenv`, `func`, `inst`, `n`, `p`, `es.scopes`, `s`] >>
        fs[stmt_state_rel_def, state_rel_def]) >>
     `b + sz' <= w2n w \/ w2n w + type_memory_size tyv <= b` by
       (fs[regions_disjoint_def] >> decide_tac) >> metis_tac[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (`t.vs_data_section = s.vs_data_section` by
       (qpat_x_assum `t with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
                              vs_current_bb := _; vs_inst_idx := _|> = s` mp_tac >>
        simp[venom_state_component_equality]) >>
     irule loweringSliceTheory.immutables_rel_mem_agree >> qexists `s` >>
     fs[stmt_state_rel_def, state_rel_def] >>
     fs[immutable_alloca_sep_def] >> rpt strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     `regions_disjoint off (type_memory_size tv) (w2n w) sz` by metis_tac[] >>
     `off + type_memory_size tv <= w2n w \/
      w2n w + type_memory_size tyv <= off` by
       (fs[regions_disjoint_def] >> decide_tac) >>
     qpat_x_assum `!b n. _ ==> mem_bytes_at b n t.vs_memory = _`
       (qspecl_then [`off`, `type_memory_size tv`] mp_tac) >> simp[]) >>
  irule stmt_state_rel_declare_memory >> simp[] >>
  qexistsl [`inst`, `s`, `w`] >> gs[] >>
  qpat_x_assum `t with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
                         vs_current_bb := _; vs_inst_idx := _|> = s` mp_tac >>
  simp[venom_state_component_equality] >> strip_tac >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem typed_decl_store_post_run[local]:
  !ctx func cenv cx env e es sa sb sf s0 es1 v op s stv dtv
   inst p dw dsz dty loc info bytes sc rest id a.
    expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
    expr_sim_inv cenv cx env es /\
    ~is_bytestring_type (lowered_value_type cenv e) /\
    ~is_word_type (lowered_value_type cenv e) /\
    ~is_word_type dty /\ ~is_bytestring_type dty /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    type_memory_size dtv + 64 < dimword (:256) /\
    not_fresh_at sa p /\ lookup_var p s0 = SOME dw /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n dw,dsz) /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [p] /\
    inst.inst_opcode = ALLOCA /\
    inst.inst_id < sa.cs_next_id /\ inst.inst_id < sb.cs_next_id /\
    not_local_ptr cenv es1.scopes p /\ fn_inst_ids_distinct func /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    0 < type_memory_size dtv /\ type_memory_size dtv <= dsz /\
    compile_assign_value cenv (Var p) LocMemory op F loc dty
      (lowered_value_type cenv e) info bytes sb = ((),sf) /\
    fn_has_code sb sf func /\ local_ptrs_reserved cenv sb /\
    (!x. op = Var x ==> not_fresh_at sb x) /\ not_fresh_at sb p /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    es1.scopes = sc :: rest /\ lookup_scopes id es1.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) dsz) ==>
    ?t. stmt_state_rel ctx func cenv cx
          (es1 with scopes :=
            (sc |+ (id, <|assignable := a; type := dtv; value := v; popped := []|>)) :: rest) t /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                   FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_decl_post_assign_run >>
  disch_then (qx_choosel_then [`sn`, `u`, `t`] strip_assume_tac) >>
  `FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n dw,dsz)` by
    (gvs[expr_post_def] >> metis_tac[]) >>
  `local_ptrs_reserved cenv sn` by
    (irule local_ptrs_reserved_next_var >> qexists `sb` >> simp[]) >>
  `not_fresh_at sn p` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `sb` >> simp[]) >>
  `val_wf dtv v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `stmt_state_rel ctx func cenv cx
      (es1 with scopes :=
        (sc |+ (id, <|assignable := a; type := dtv; value := v; popped := []|>)) :: rest) t` by
    (drule_all typed_decl_store_frame >> simp[]) >>
  `t.vs_allocas = u.vs_allocas` by
    (qpat_x_assum `_ = u` mp_tac >> simp[venom_state_component_equality]) >>
  qexists `t` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sn x` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists `sb` >> simp[]) >>
      simp[]) >>
  rpt strip_tac >> simp[] >>
  qpat_x_assum `!fuel r. _` irule >> simp[] >>
  qexists `fuel` >> simp[]
QED

Theorem annassign_memory_typed_read_success_run[local]:
  !ctx func cenv cx env id dty e es es' stv dtv sa sb sf op p sz s0 dw inst loc info bytes.
    eval_stmt cx (AnnAssign id dty e) es = (INL (),es') /\
    expr_sim_inv cenv cx env es /\ acyclic_struct_metadata cenv.ce_struct_fields /\
    ~is_word_type dty /\ ~is_bytestring_type dty /\
    ~is_word_type (lowered_value_type cenv e) /\
    ~is_bytestring_type (lowered_value_type cenv e) /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    0 < type_memory_size dtv /\ type_memory_size dtv <= sz /\
    type_memory_size dtv + 64 < dimword (:256) /\
    (!v es1. (do raw <- eval_expr cx e; read_result cx raw od) es = (INL v,es1) ==>
       value_has_type stv v /\ value_has_type dtv v) /\
    expr_sim ctx func cenv cx (expr_type e) e es /\
    lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\ cs_extends sa sb /\
    compile_assign_value cenv (Var p) LocMemory op F loc dty
      (lowered_value_type cenv e) info bytes sb = ((),sf) /\
    fn_has_code sa sb func /\ fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    lookup_var p s0 = SOME dw /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n dw,sz) /\
    inst.inst_id < sa.cs_next_id ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
        t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==> lookup_var x t = SOME u) /\
        (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                     FLOOKUP t.vs_allocas aid = SOME entry) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s0 = r
Proof
  rpt gen_tac >> strip_tac >>
  drule loweringSliceTheory.eval_stmt_annassign_read_value >> strip_tac >>
  rename1 `(do raw <- eval_expr cx e; read_result cx raw od) es = (INL v,es1)` >>
  `value_has_type stv v /\ value_has_type dtv v` by metis_tac[] >>
  `not_local_ptr cenv es1.scopes p` by metis_tac[local_ptrs_reserved_not_live] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `op`, `INL v`, `es1`, `s0`] mp_tac) >>
  (impl_tac >- simp[expr_res_ok_def]) >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  `tyv = dtv` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `tyv = dtv` SUBST_ALL_TAC >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    metis_tac[exprLoweringPropsTheory.compile_expr_grows] >>
  `not_fresh_at sb p` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `inst.inst_id < sb.cs_next_id` by decide_tac >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  drule_all typed_decl_store_post_run >>
  disch_then (qspec_then `T` mp_tac) >> strip_tac >>
  qexists `t` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sb x` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
      qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[expr_post_def] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[expr_post_def] >> metis_tac[]) >>
  qpat_x_assum `!fuel. _ ==> ?fuel'. run_from fuel' ctx func s0 = _` mp_tac >>
  qpat_x_assum `!fuel r. _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED


Theorem unstaged_overlap_value_types[local]:
  let u = BaseT (UintT 256);
      sty = TupleT [TupleT [BaseT (BytesT (Dynamic 1));u];u];
      dty = TupleT [TupleT [BaseT (BytesT (Dynamic 33));u];u];
      v = ArrayV (TupleV [ArrayV (TupleV [BytesV [];IntV 7]);IntV 9])
  in type_widens_to FEMPTY sty dty /\
     value_has_type
       (TupleTV [TupleTV [BaseTV (BytesT (Dynamic 1));BaseTV (UintT 256)];
                 BaseTV (UintT 256)]) v /\
     value_has_type
       (TupleTV [TupleTV [BaseTV (BytesT (Dynamic 33));BaseTV (UintT 256)];
                 BaseTV (UintT 256)]) v
Proof
  EVAL_TAC
QED

Theorem unstaged_overlap_input_memory[local]:
  !s0.
  let s = mstore 96 9w (mstore 64 7w (s0 with vs_memory := []));
      tv = TupleTV [TupleTV [BaseTV (BytesT (Dynamic 1));BaseTV (UintT 256)];
                    BaseTV (UintT 256)];
      v = ArrayV (TupleV [ArrayV (TupleV [BytesV [];IntV 7]);IntV 9])
  in val_in_memory tv v 0 s.vs_memory /\ mload 96 s = 9w
Proof
  gen_tac >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``val_in_memory``, ``mload``]) >>
  EVAL_TAC
QED

(* A probe of an adapter, not a counterexample to expression simulation. *)
Theorem unstaged_overlap_probe[local]:
  let u = BaseT (UintT 256);
      sty = TupleT [TupleT [BaseT (BytesT (Dynamic 1));u];u];
      dty = TupleT [TupleT [BaseT (BytesT (Dynamic 33));u];u];
      ce = (ARB:compile_env) with ce_struct_fields := FEMPTY;
      st = initial_compile_state "entry";
      out = SND (compile_assign_value ce (Lit 0w) LocMemory (Lit 0w)
                    F NONE dty sty NONE 160 st);
      bb = <|bb_label := "entry";
             bb_instructions := out.cs_current_insts ++
               [mk_inst 999 STOP [] []]|>;
      s = mstore 96 9w (mstore 64 7w
            ((ARB:venom_state) with <|vs_vars := FEMPTY; vs_memory := [];
              vs_inst_idx := 0; vs_halted := F|>))
  in case run_block 100 ARB bb s of
       Halt s' => mload 128 s' = 7w
     | _ => F
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_block``, ``mload``]) >>
  rewrite_tac[venomExecSemanticsTheory.run_block_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``mload``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  EVAL_TAC
QED

Theorem expr_sim_inv_declare_memory[local]:
  !cenv cx env es id dty sa c st.
    expr_sim_inv cenv cx env es /\ lookup_scopes id es.scopes = NONE /\
    declare_local cenv id dty sa = (c,st) /\ cenv.ce_alloca_locals ==>
    expr_sim_inv c cx env es
Proof
  rpt gen_tac >> strip_tac >>
  `FLOOKUP env.var_types id = NONE` by
    (gvs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
         vyperTypeInvariantsTheory.env_scopes_consistent_def] >>
     Cases_on `FLOOKUP env.var_types id` >> gvs[] >>
     qpat_x_assum `!id ty. _ ==> IS_SOME (lookup_scopes _ _)` drule >> simp[]) >>
  qpat_x_assum `declare_local _ _ _ _ = _` mp_tac >>
  simp[declare_local_def, fresh_var_def, comp_bind_def, comp_return_def, LET_THM] >>
  strip_tac >> gvs[expr_sim_inv_def, FLOOKUP_UPDATE,
                   placeTypingPropsTheory.place_map_tables_agree_on_defined_def] >>
  rpt strip_tac >> simp[] >>
  FIRST [(first_assum drule >> simp[] >> NO_TAC),
         (`id <> id'` by (strip_tac >> gvs[]) >> simp[] >>
          first_x_assum drule >> simp[combinTheory.APPLY_UPDATE_THM])]
QED

Theorem typed_widen_memory_categories[local]:
  !tenv t u. type_widens_to tenv t u /\ ~is_word_type u ==>
    ~is_word_type t /\ (is_bytestring_type t <=> is_bytestring_type u)
Proof
  rpt gen_tac >> simp[type_widens_to_def] >> strip_tac
  >- simp[] >>
  Cases_on `t` >> Cases_on `u` >>
  gvs[arg_type_fits_def, is_word_type_def, is_bytestring_type_def] >>
  rename1 `arg_type_fits (BaseT b1) (BaseT b2)` >>
  Cases_on `b1` >> Cases_on `b2` >>
  gvs[arg_type_fits_def, is_word_type_def, is_bytestring_type_def] >>
  rename1 `arg_type_fits (BaseT (BytesT d1)) (BaseT (BytesT d2))` >>
  Cases_on `d1` >> Cases_on `d2` >>
  gvs[arg_type_fits_def, is_word_type_def, is_bytestring_type_def]
QED

Theorem compile_annassign_memory_typed_stmt_frag:
  !ctx func cx lctx RetQ cenv env ret id dty e es res es' stv dtv.
    eval_stmt cx (AnnAssign id dty e) es = (res,es') /\
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\ cenv.ce_alloca_locals /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    ~is_word_type dty /\ ~(has_length_word dty /\ is_empty_value_expr e) /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    0 < type_memory_size dtv /\ type_memory_size dtv + 64 < dimword (:256) /\
    (!v es1.
       (do raw <- eval_expr cx e; read_result cx raw od) es = (INL v,es1) ==>
       value_has_type stv v /\ value_has_type dtv v) /\
    (!st0 c st1. declare_local cenv id dty st0 = (c,st1) ==>
       expr_sim ctx func c cx (expr_type e) e es /\
       !sa sb op. lower_value compile_expr c (expr_type e) e sa = (op,sb) ==>
                  cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret (AnnAssign id dty e)) es res es'
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
  `!st0 c st1. declare_local cenv id dty st0 = (c,st1) ==>
     !a b op. lower_value compile_expr c (expr_type e) e a = (op,b) ==>
              cs_extends a b` by metis_tac[] >>
  drule_all annassign_memory_typed_code_parts >>
  disch_then (qx_choosel_then [`st`, `sA`, `sV`, `sB`, `vv`, `op`, `p`] strip_assume_tac) >>
  rename1 `declare_local cenv id dty sa = (c,st)` >>
  qpat_x_assum `!st0 c st1. _ ==> _ /\ _` drule >> strip_tac >>
  `stmt_state_rel ctx func c cx es s0` by
    (irule stmt_state_rel_declare_local_entry >> metis_tac[]) >>
  `expr_sim_inv c cx env es` by (drule_all expr_sim_inv_declare_memory >> simp[]) >>
  drule_all declare_local_typed_memory_metadata >> strip_tac >>
  `not_local_ptr c es.scopes p` by metis_tac[local_ptrs_reserved_not_live] >>
  `s0.vs_current_bb = st.cs_current_bb /\
   s0.vs_inst_idx = LENGTH st.cs_current_insts` by
    (drule_all declare_local_ptr >> simp[] >> strip_tac >> gvs[]) >>
  `type_memory_bytes cenv dty < dimword (:256)` by (fs[] >> decide_tac) >>
  drule_all annassign_alloca_framed_run >>
  disch_then (qx_choosel_then [`salloc`, `w`] strip_assume_tac) >>
  Cases_on `res`
  >- suspend "success" >>
  rename1 `eval_stmt cx (AnnAssign id dty e) es = (INR ex, es')` >>
  `(do raw <- eval_expr cx e; read_result cx raw od) es = (INR ex,es') /\
   expr_res_ok (INR ex : value + exception)` by
    (drule eval_annassign_word_error >> simp[] >>
     disch_then (qspec_then `lctx` mp_tac) >> simp[] >> metis_tac[]) >>
  drule_all expr_sim_error_run >> strip_tac >>
  drule exit_result_not_error >> strip_tac >>
  disj2_tac >> simp[stmt_exit_def] >> metis_tac[]
QED

Resume compile_annassign_memory_typed_stmt_frag[success]:
  rename1 `eval_stmt cx (AnnAssign id dty e) es = (INL unit, es')` >>
  Cases_on `unit` >>
  qmatch_asmsub_abbrev_tac `MEM ai (fn_insts func)` >>
  `ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [p] /\
   FLOOKUP salloc.vs_allocas ai.inst_id =
     SOME (w2n w,type_memory_bytes cenv dty)` by
    simp[Abbr `ai`, venomInstTheory.mk_inst_def] >>
  qpat_x_assum `expr_sim_inv cenv _ _ _` kall_tac >>
  qpat_x_assum `stmt_state_rel _ _ cenv _ _ _` kall_tac >>
  qpat_x_assum `stmt_state_rel _ _ c _ _ s0` kall_tac >>
  qpat_x_assum `!st0 c st1. _` kall_tac >>
  qpat_x_assum `!l. FLOOKUP cenv.ce_vars id = SOME l ==> _` kall_tac >>
  `ai.inst_id < sA.cs_next_id` by
    (qpat_x_assum `emit_inst ALLOCA _ _ st = _` mp_tac >>
     simp[Abbr `ai`, emitHelperTheory.emit_inst_def, fresh_id_def, emit_def,
          comp_bind_def, comp_return_def, venomInstTheory.mk_inst_def] >>
     strip_tac >> gvs[]) >>
  drule_all typed_widen_memory_categories >> strip_tac >>
  Cases_on `is_bytestring_type dty`
  >- suspend "bytestring" >>
  qpat_x_assum `compile_expr _ _ _ _ = _` kall_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` kall_tac >>
  `~is_word_type (lowered_value_type c e) /\
   ~is_bytestring_type (lowered_value_type c e)` by simp[] >>
  `type_memory_size dtv <= type_memory_bytes cenv dty /\
   type_memory_bytes c dty = type_memory_size dtv /\
   type_memory_bytes c (lowered_value_type c e) = type_memory_size stv /\
   evaluate_type (get_tenv cx) (lowered_value_type c e) = SOME stv /\
   type_widens_to (get_tenv cx) (lowered_value_type c e) dty /\
   acyclic_struct_metadata c.ce_struct_fields` by simp[] >>
  `compile_assign_value c (Var p) LocMemory op F (vv_location vv) dty
     (lowered_value_type c e)
     (case dty of ArrayT et (Dynamic _) =>
        SOME ((type_memory_bytes c et + 31) DIV 32,type_memory_bytes c et)
      | _ => NONE) (type_memory_bytes c dty) sB = ((),sb)` by
    (qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >> simp[]) >>
  drule_all annassign_memory_typed_read_success_run >> strip_tac >>
  suspend "finish"
QED

Resume compile_annassign_memory_typed_stmt_frag[bytestring]:
  FAIL_TAC "bytestring branch"
QED

Resume compile_annassign_memory_typed_stmt_frag[finish]:
  FAIL_TAC "final composition"
QED

Finalise compile_annassign_memory_typed_stmt_frag

Theorem compile_assign_local_memory_typed_stmt_frag:
  !ctx func cx lctx RetQ cenv env ret id dty e es res es' p sz stv dtv.
    eval_stmt cx (Assign (BaseTarget (NameTarget id)) e) es = (res,es') /\
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME dty /\
    ~is_word_type dty /\ ~(has_length_word dty /\ is_empty_value_expr e) /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    0 < type_memory_size dtv /\ type_memory_size dtv + 64 < dimword (:256) /\
    (!v es1 entry.
       (do raw <- eval_expr cx e; read_result cx raw od) es = (INL v,es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       entry.type = dtv /\ value_has_type stv v /\ value_has_type dtv v) /\
    (~is_bytestring_type (expr_type e) ==>
       !sa vv sb. compile_expr cenv (expr_type e) e sa = (vv,sb) ==>
         (?ptr. vv = LocatedValue (expr_type e) ptr /\
                ptr.ptr_location <> LocCalldata) \/
         (?op. vv = StackValue (expr_type e) op /\
               emit_inst INVALID [] [] sa = ((),sb))) /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    expr_sim ctx func cenv cx (expr_type e) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret (Assign (BaseTarget (NameTarget id)) e)) es res es'
Proof
  cheat
QED

