Theory exprSimAbiEncodeArgsMaterializePath
Ancestors
  abiEncodeMaterialize exprSimAbiGasBridge exprSimHash vyperCompiler context
  loweringPosts compileEnv finite_map exprSimAbiEncodeSeparation

Definition materialize_owned_post_def:
  materialize_owned_post ctx func ce cx e es sa sm sb s0 es' v dst tv s <=>
    stmt_state_rel ctx func ce cx es' s /\
    wb_frame ce es es' sa s0 s /\
    expr_val_rel cx (lowered_value_type ce e) v dst s /\
    expr_val_at ce cx (lowered_value_type ce e) sa sb es' v dst s /\
    sm.cs_next_id < sb.cs_next_id /\
    ?w. eval_operand dst s = SOME w /\
        FLOOKUP s.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
        val_in_memory tv v (w2n w) s.vs_memory /\
        (!name b len. local_region ce es'.scopes s name b len ==>
           w2n w + type_memory_size tv <= b \/ b + len <= w2n w)
End

Theorem materialize_owned_post_returndata:
  materialize_owned_post ctx func ce cx e es sa sm sb s0 es' v dst tv
    (s with vs_returndata := rd) <=>
  materialize_owned_post ctx func ce cx e es sa sm sb s0 es' v dst tv s
Proof
  Cases_on `dst` >>
  simp[materialize_owned_post_def, hash_returndata_state_rel,
       wb_frame_def, expr_val_rel_def, expr_val_at_def,
       locals_kept_def, popped_kept_def, local_region_def, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def]
QED

Theorem compile_materialize_vv_owned_path:
  compile_materialize_vv ce (lowered_value_type ce e) vv sm = (dst,sb) /\
  expr_body_pre ce cx env e es_pre /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  read_result cx tvv es' = (INL v,es') /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
         ~is_word_type (post_value_type ce e) ==>
         type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
         type_memory_size tvt < 2 ** 64) /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 /\
  type_memory_size tv + 64 < dimword (:256) /\
  cs_extends sm sb /\ frag_gas_free sm sb /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_marked_path F ctx func r 0 (OK t) /\
      materialize_owned_post ctx func ce cx e es sa sm sb s0 es' v dst tv t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all compile_materialize_vv_owned_sim >>
  disch_then (qspec_then `\r. F` mp_tac) >>
  rewrite_tac[GSYM materialize_owned_post_def] >> strip_tac >>
  drule frag_exec_gas_path >>
  disch_then (qspecl_then [`func`, `r`] mp_tac) >>
  simp[materialize_owned_post_returndata]
QED

Theorem materialize_extends:
  compile_materialize_vv ce ty vv sa = (dst,sb) ==> cs_extends sa sb
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`ce`, `ty`, `vv`, `sa`]
    exprLoweringPropsTheory.ci_mono_compile_materialize_vv) >>
  simp[exprLoweringPropsTheory.ci_mono_def]
QED

Theorem materialize_stack_gas_free:
  compile_materialize_vv ce ty (StackValue vty op) sa = (dst,sb) /\
  (!l. op <> Label l) ==> frag_gas_free sa sb
Proof
  Cases_on `is_word_type ty` >> Cases_on `is_bytestring_type ty` >>
  Cases_on `type_memory_bytes ce ty` >>
  simp[exprLoweringTheory.compile_materialize_vv_def, exprLoweringTheory.unwrap_value_def,
       contextTheory.compile_store_memory_def,
       contextTheory.compile_alloc_buffer_def,
       contextTheory.compile_store_bytestring_def,
       contextTheory.compile_bytestring_copy_len_def,
       contextTheory.compile_copy_memory_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
       compileEnvTheory.emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> strip_tac >> gvs[] >>
  simp[frag_gas_free_def, frag_code_def, fragExecTheory.emitted_blocks_def,
       exprLoweringPropsTheory.emitted_insts_def, rich_listTheory.DROP_APPEND, arithmeticTheory.SUB_PLUS,
       arithmeticTheory.SUB_EQ_0, venomInstTheory.mk_inst_def]
QED

Theorem materialize_memory_gas_free:
  compile_materialize_vv ce ty (LocatedValue vty p) sa = (dst,sb) /\
  ~is_word_type vty /\ p.ptr_location = LocMemory /\
  (!l. p.ptr_operand <> Label l) ==> frag_gas_free sa sb
Proof
  strip_tac >> irule materialize_stack_gas_free >>
  qexistsl_tac [`ce`, `dst`, `p.ptr_operand`, `ty`, `vty`] >> simp[] >>
  gvs[exprLoweringTheory.compile_materialize_vv_def,
      exprLoweringTheory.unwrap_value_def, comp_bind_def]
QED

Theorem materialize_zero_store:
  ~is_word_type ty /\ type_memory_bytes ce ty = 0 ==>
  compile_store_memory ce src dst ty ty = comp_return ()
Proof
  strip_tac >>
  `~is_bytestring_type ty` by
    (spose_not_then assume_tac >>
     drule valueCopyBytesTheory.bytestring_memory_bytes_positive >>
     disch_then (qspec_then `ce` mp_tac) >> simp[]) >>
  simp[contextTheory.compile_store_memory_def,
       contextTheory.compile_copy_memory_def]
QED

Theorem materialize_zero_code_shape:
  ~is_word_type ty /\ type_memory_bytes ce ty = 0 /\
  ~is_word_type vty /\ type_memory_bytes ce vty = 0 /\
  p.ptr_location = LocCode ==>
  compile_materialize_vv ce ty (LocatedValue vty p) =
    comp_bind (compile_alloc_buffer 0)
      (\tmp. comp_bind (compile_alloc_buffer 0)
        (\src. comp_return tmp.buf_operand))
Proof
  strip_tac >>
  simp[exprLoweringTheory.compile_materialize_vv_def,
       exprLoweringTheory.unwrap_value_def,
       contextTheory.compile_ensure_in_memory_def,
       contextTheory.compile_imm_copy_to_memory_def,
       materialize_zero_store, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, FUN_EQ_THM] >>
  gen_tac >> pairarg_tac >> simp[] >>
  Cases_on `compile_alloc_buffer 0 cs'` >> simp[]
QED

Theorem materialize_zero_code_gas_free:
  compile_materialize_vv ce ty (LocatedValue vty p) sa = (dst,sb) /\
  ~is_word_type ty /\ type_memory_bytes ce ty = 0 /\
  ~is_word_type vty /\ type_memory_bytes ce vty = 0 /\
  p.ptr_location = LocCode ==> frag_gas_free sa sb
Proof
  strip_tac >>
  gvs[materialize_zero_code_shape, contextTheory.compile_alloc_buffer_def,
      emitHelperTheory.emit_op_def, compileEnvTheory.fresh_var_def,
      compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[frag_gas_free_def, frag_code_def, fragExecTheory.emitted_blocks_def,
       exprLoweringPropsTheory.emitted_insts_def, rich_listTheory.DROP_APPEND,
       arithmeticTheory.SUB_PLUS, arithmeticTheory.SUB_EQ_0,
       venomInstTheory.mk_inst_def]
QED

Theorem materialize_zero_slot_shape:
  ~is_word_type ty /\ type_memory_bytes ce ty = 0 /\
  ~is_word_type vty /\ type_memory_bytes ce vty = 0 /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
  compile_materialize_vv ce ty (LocatedValue vty p) =
    comp_bind (compile_alloc_buffer 0)
      (\tmp. comp_bind (compile_alloc_buffer 0)
        (\src. comp_bind
          (compile_word_copy_loop p.ptr_operand src.buf_operand 0
            p.ptr_location LocMemory F)
          (\u. comp_return tmp.buf_operand)))
Proof
  strip_tac >>
  simp[exprLoweringTheory.compile_materialize_vv_def,
       exprLoweringTheory.unwrap_value_def,
       contextTheory.compile_ensure_in_memory_def,
       contextTheory.compile_storage_to_memory_def,
       contextTheory.compile_transient_to_memory_def,
       materialize_zero_store, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, FUN_EQ_THM] >>
  gen_tac >> Cases_on `compile_alloc_buffer 0 x` >> simp[] >>
  rename1 `compile_alloc_buffer 0 x = (buf,sm)` >>
  Cases_on `compile_alloc_buffer 0 sm` >> simp[] >>
  rename1 `compile_alloc_buffer 0 sm = (src,sn)` >>
  Cases_on `compile_word_copy_loop p.ptr_operand src.buf_operand 0
    p.ptr_location LocMemory F sn` >> gvs[]
QED

Theorem materialize_zero_loop_test_edge:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\ lookup_var ctr s = SOME 0w /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := s.vs_current_bb;
      bb_instructions := [mk_inst id EQ [Var ctr; Lit 0w] [done];
        mk_inst (id+1) JNZ [Var done; Label exit; Label body_lbl] []]|> ==>
  fragGasPath$gas_path_edge ctx fn s 0
    (OK ((update_var done 1w s) with vs_inst_idx := 1))
Proof
  strip_tac >>
  simp[fragGasPathTheory.gas_path_edge_def] >> qexists_tac `0` >>
  simp[venomInstTheory.get_instruction_def] >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
       gasCountTheory.gas_count_step_def] >>
  disj1_tac >> qexists_tac `update_var done 1w s` >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def,
       venomStateTheory.eval_operand_def, venomExecSemanticsTheory.bool_to_word_def,
       venomStateTheory.update_var_def]
QED

Theorem materialize_zero_loop_exit_edge:
  ~s.vs_halted /\ s.vs_inst_idx = 1 /\ lookup_var done s = SOME 1w /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := s.vs_current_bb;
      bb_instructions := [mk_inst id EQ [Var ctr; Lit 0w] [done];
        mk_inst (id+1) JNZ [Var done; Label exit; Label body_lbl] []]|> ==>
  fragGasPath$gas_path_edge ctx fn s 0 (OK (jump_to exit s))
Proof
  strip_tac >> simp[fragGasPathTheory.gas_path_edge_def] >>
  qexists_tac `0` >>
  simp[venomInstTheory.get_instruction_def] >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
       gasCountTheory.gas_count_step_def] >>
  disj2_tac >> disj1_tac >> qexists_tac `exit` >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_def,
       venomStateTheory.eval_operand_def]
QED

Theorem materialize_zero_loop_test_path:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\ lookup_var ctr s = SOME 0w /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := s.vs_current_bb;
      bb_instructions := [mk_inst id EQ [Var ctr; Lit 0w] [done];
        mk_inst (id+1) JNZ [Var done; Label exit; Label body_lbl] []]|> ==>
  gas_marked_path F ctx fn s 0 (OK (jump_to exit (update_var done 1w s)))
Proof
  strip_tac >>
  `fragGasPath$gas_path_edge ctx fn s 0
    (OK ((update_var done 1w s) with vs_inst_idx := 1))` by
    (irule materialize_zero_loop_test_edge >> metis_tac[]) >>
  `fragGasPath$gas_path_edge ctx fn
    ((update_var done 1w s) with vs_inst_idx := 1) 0
    (OK (jump_to exit ((update_var done 1w s) with vs_inst_idx := 1)))` by
    (irule materialize_zero_loop_exit_edge >>
     simp[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  `~(jump_to exit (update_var done 1w s)).vs_halted` by
    simp[venomStateTheory.jump_to_def, venomStateTheory.update_var_def] >>
  gvs[venomStateTheory.jump_to_def] >>
  simp[fragGasModeTheory.gas_marked_path_def] >>
  irule (cj 2 fragGasPathTheory.gas_path_rules |> SPEC_ALL |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SIMP_RULE (srw_ss()) []) >>
  qexists_tac `(update_var done 1w s) with vs_inst_idx := 1` >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule (cj 2 fragGasPathTheory.gas_path_rules |> SPEC_ALL |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SIMP_RULE (srw_ss()) []) >>
  goal_assum (drule_at Any) >>
  irule (cj 1 fragGasPathTheory.gas_path_rules) >> simp[]
QED

Theorem materialize_zero_loop_layout:
  compile_word_copy_loop src dst 0 loc LocMemory F sa = (u,sb) /\
  (loc = LocStorage \/ loc = LocTransient) /\ fn_has_code sa sb fn ==>
  lookup_block (fresh_label_output "wcopy_cond" sa.cs_next_label) fn.fn_blocks =
    SOME <|bb_label := fresh_label_output "wcopy_cond" sa.cs_next_label;
      bb_instructions :=
        [mk_inst (sa.cs_next_id+2) EQ
          [Var ("%" ++ toString sa.cs_next_var); Lit 0w]
          ["%" ++ toString (sa.cs_next_var+1)];
         mk_inst (sa.cs_next_id+3) JNZ
          [Var ("%" ++ toString (sa.cs_next_var+1));
           Label (fresh_label_output "wcopy_exit" (sa.cs_next_label+2));
           Label (fresh_label_output "wcopy_body" (sa.cs_next_label+1))] []]|> /\
  lookup_block sa.cs_current_bb fn.fn_blocks =
    SOME <|bb_label := sa.cs_current_bb;
      bb_instructions := sa.cs_current_insts ++
        [mk_inst sa.cs_next_id ASSIGN [Lit 0w] ["%" ++ toString sa.cs_next_var];
         mk_inst (sa.cs_next_id+1) JMP
           [Label (fresh_label_output "wcopy_cond" sa.cs_next_label)] []]|> /\
  sb.cs_current_bb = fresh_label_output "wcopy_exit" (sa.cs_next_label+2) /\
  sb.cs_current_insts = []
Proof
  strip_tac >> gvs[] >>
  gvs[contextTheory.compile_word_copy_loop_def, word_scale_def,
       contextTheory.compile_ptr_load_def, contextTheory.compile_ptr_store_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_inst_def,
       emitHelperTheory.emit_void_def, fresh_var_def, fresh_id_def,
       fresh_label_def, emit_def, new_block_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  gvs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def,
      DISJ_IMP_THM, FORALL_AND_THM, listTheory.APPEND_ASSOC]
QED

Theorem materialize_zero_assign_edge:
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [Lit 0w] [ctr]) ==>
  fragGasPath$gas_path_edge ctx fn s 0
    (OK ((update_var ctr 0w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> simp[fragGasPathTheory.gas_path_edge_def] >>
  qexists_tac `0` >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
       gasCountTheory.gas_count_step_def] >>
  disj1_tac >> qexists_tac `update_var ctr 0w s` >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_def,
       venomStateTheory.eval_operand_def, venomStateTheory.update_var_def]
QED

Theorem materialize_zero_jump_edge:
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label dest] []) ==>
  fragGasPath$gas_path_edge ctx fn s 0 (OK (jump_to dest s))
Proof
  strip_tac >> simp[fragGasPathTheory.gas_path_edge_def] >>
  qexists_tac `0` >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
       gasCountTheory.gas_count_step_def] >>
  disj2_tac >> disj1_tac >> qexists_tac `dest` >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_def]
QED

Theorem materialize_zero_loop_path:
  compile_word_copy_loop src dst 0 loc LocMemory F sa = (u,sb) /\
  (loc = LocStorage \/ loc = LocTransient) /\ fn_has_code sa sb fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_marked_path F ctx fn s 0
    (OK (jump_to sb.cs_current_bb
      (update_var ("%" ++ toString (sa.cs_next_var+1)) 1w
        (jump_to (fresh_label_output "wcopy_cond" sa.cs_next_label)
          (update_var ("%" ++ toString sa.cs_next_var) 0w s)))))
Proof
  strip_tac >> drule materialize_zero_loop_layout >>
  disch_then (qspec_then `fn` mp_tac) >> simp[] >> strip_tac >>
  qabbrev_tac `ctr = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `done = "%" ++ toString (sa.cs_next_var+1)` >>
  qabbrev_tac `hdr = fresh_label_output "wcopy_cond" sa.cs_next_label` >>
  `fragGasPath$gas_path_edge ctx fn s 0
    (OK ((update_var ctr 0w s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule materialize_zero_assign_edge >>
     simp[venomInstTheory.get_instruction_def, listTheory.EL_APPEND_EQN,
          Abbr `ctr`] >> metis_tac[]) >>
  `fragGasPath$gas_path_edge ctx fn
    ((update_var ctr 0w s) with vs_inst_idx := SUC s.vs_inst_idx) 0
    (OK (jump_to hdr ((update_var ctr 0w s) with
       vs_inst_idx := SUC s.vs_inst_idx)))` by
    (irule materialize_zero_jump_edge >>
     simp[venomStateTheory.update_var_def, venomStateTheory.jump_to_def,
          venomInstTheory.get_instruction_def, listTheory.EL_APPEND_EQN,
          Abbr `ctr`, Abbr `hdr`] >> metis_tac[]) >>
  `gas_marked_path F ctx fn (jump_to hdr (update_var ctr 0w s)) 0
    (OK (jump_to sb.cs_current_bb
      (update_var done 1w (jump_to hdr (update_var ctr 0w s)))))` by
    (irule materialize_zero_loop_test_path >>
     simp[venomStateTheory.jump_to_def, venomStateTheory.update_var_def,
          venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
          venomInstTheory.mk_inst_def,
          Abbr `ctr`, Abbr `done`, Abbr `hdr`]) >>
  gvs[fragGasModeTheory.gas_marked_path_def, venomStateTheory.jump_to_def] >>
  qpat_x_assum `compile_word_copy_loop _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `fn_has_code _ _ _` kall_tac >>
  qpat_x_assum `lookup_block hdr _ = _` kall_tac >>
  qpat_x_assum `lookup_block sa.cs_current_bb _ = _` kall_tac >>
  fs[] >> metis_tac[fragGasPathTheory.gas_path_rules, arithmeticTheory.ADD]
QED

(* The explicit fresh zero allocation leaves the frontier unchanged. *)
Definition materialize_zero_alloc_def:
  materialize_zero_alloc id out s =
    (update_var out (n2w s.vs_alloca_next)
      (s with vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,0))))
      with vs_inst_idx := SUC s.vs_inst_idx
End

Theorem materialize_zero_alloc_edge:
  ~s.vs_halted /\ FLOOKUP s.vs_allocas id = NONE /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ALLOCA [Lit 0w] [out]) ==>
  fragGasPath$gas_path_edge ctx fn s 0
    (OK (materialize_zero_alloc id out s))
Proof
  strip_tac >> simp[fragGasPathTheory.gas_path_edge_def] >>
  qexists_tac `0` >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
       gasCountTheory.gas_count_step_def] >>
  disj1_tac >>
  qexists_tac `update_var out (n2w s.vs_alloca_next)
    (s with vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,0)))` >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_alloca_def,
       venomStateTheory.eval_operand_def, materialize_zero_alloc_def,
       venomStateTheory.update_var_def]
QED

Theorem materialize_zero_alloc_fields:
  (materialize_zero_alloc id out s).vs_memory = s.vs_memory /\
  (materialize_zero_alloc id out s).vs_alloca_next = s.vs_alloca_next /\
  (materialize_zero_alloc id out s).vs_allocas =
    s.vs_allocas |+ (id,(s.vs_alloca_next,0)) /\
  (materialize_zero_alloc id out s).vs_vars =
    s.vs_vars |+ (out,n2w s.vs_alloca_next) /\
  (materialize_zero_alloc id out s).vs_halted = s.vs_halted /\
  (materialize_zero_alloc id out s).vs_current_bb = s.vs_current_bb /\
  (materialize_zero_alloc id out s).vs_inst_idx = SUC s.vs_inst_idx
Proof
  simp[materialize_zero_alloc_def, venomStateTheory.update_var_def]
QED
Theorem materialize_zero_alloc_buffer_path:
  compile_alloc_buffer 0 sa = (buf,sb) /\ fn_has_code sa sb fn /\
  FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_marked_path F ctx fn s 0
    (OK (materialize_zero_alloc sa.cs_next_id
      ("%" ++ toString sa.cs_next_var) s)) /\
  ~ (materialize_zero_alloc sa.cs_next_id
      ("%" ++ toString sa.cs_next_var) s).vs_halted /\
  (materialize_zero_alloc sa.cs_next_id
      ("%" ++ toString sa.cs_next_var) s).vs_current_bb = sb.cs_current_bb /\
  (materialize_zero_alloc sa.cs_next_id
      ("%" ++ toString sa.cs_next_var) s).vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id ALLOCA [Lit 0w]
        ["%" ++ toString sa.cs_next_var])` by
    (gvs[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
         fresh_id_def, fresh_var_def, emit_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def,
         fragExecTheory.fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
     simp[venomInstTheory.get_instruction_def, listTheory.EL_APPEND_EQN] >>
     metis_tac[]) >>
  `fragGasPath$gas_path_edge ctx fn s 0
    (OK (materialize_zero_alloc sa.cs_next_id
      ("%" ++ toString sa.cs_next_var) s))` by
    (irule materialize_zero_alloc_edge >> metis_tac[]) >>
  `~ (materialize_zero_alloc sa.cs_next_id
      ("%" ++ toString sa.cs_next_var) s).vs_halted /\
   (materialize_zero_alloc sa.cs_next_id
      ("%" ++ toString sa.cs_next_var) s).vs_current_bb = sb.cs_current_bb /\
   (materialize_zero_alloc sa.cs_next_id
      ("%" ++ toString sa.cs_next_var) s).vs_inst_idx = LENGTH sb.cs_current_insts` by
    (gvs[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
         fresh_id_def, fresh_var_def, emit_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def,
         materialize_zero_alloc_fields]) >>
  fs[fragGasModeTheory.gas_marked_path_def] >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` kall_tac >>
  qpat_x_assum `fn_has_code _ _ _` kall_tac >>
  metis_tac[fragGasPathTheory.gas_path_rules, arithmeticTheory.ADD]
QED


(* A zero-sized destination can leave the unwrap loop's exit empty. *)
Theorem materialize_zero_destination_alias_probe:
  let sa = initial_compile_state "@wcopy_exit_2";
      vv = LocatedValue (BaseT (BytesT (Dynamic 32)))
             (mk_ptr (Lit 0w) LocStorage);
      result = compile_materialize_vv ce (TupleT []) vv sa;
      sb = SND result;
      fn = venomInst$mk_raw_function "materialize-probe" sb.cs_blocks
  in
    (!l. vv_operand vv <> Label l) /\
    fragExec$fn_has_code sa sb fn /\ venomWf$fn_inst_ids_distinct fn /\
    ~frag_gas_free sa sb
Proof
  EVAL_TAC >> rpt conj_tac >> rpt strip_tac >> gvs[] >> EVAL_TAC >>
  qmatch_goalsub_abbrev_tac `$= b` >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM boolTheory.ETA_THM))) >>
  qexists_tac `b` >> simp[]
QED

Theorem materialize_located_physical_classify:
  expr_body_pre ce cx env e es_pre /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv (LocatedValue vty p) r /\
  p.ptr_location <> LocMemory /\ ~is_word_type (expr_type e) ==>
  vty = lowered_value_type ce e \/
  (is_bytestring_type vty /\ is_bytestring_type (lowered_value_type ce e))
Proof
  strip_tac >>
  `vty = post_value_type ce e` by gvs[vv_post_def, vv_holds_def] >>
  metis_tac[materialize_post_lowered_classify,
            exprSimHypsTheory.expr_body_pre_lowered_fits]
QED

Theorem materialize_equal_zero_alias_probe:
  let sa = initial_compile_state "@wcopy_exit_2";
      vv = LocatedValue (TupleT []) (mk_ptr (Lit 0w) LocStorage);
      result = compile_materialize_vv ce (TupleT []) vv sa;
      sb = SND result;
      fn = venomInst$mk_raw_function "materialize-probe" sb.cs_blocks
  in
    type_memory_bytes ce (TupleT []) = 0 /\
    (!l. vv_operand vv <> Label l) /\
    fragExec$fn_has_code sa sb fn /\ venomWf$fn_inst_ids_distinct fn /\
    ~frag_gas_free sa sb
Proof
  EVAL_TAC >> rpt conj_tac >> rpt strip_tac >> gvs[] >> EVAL_TAC >>
  qmatch_goalsub_abbrev_tac `$= b` >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM boolTheory.ETA_THM))) >>
  qexists_tac `b` >> simp[]
QED

Theorem materialize_equal_zero_lookup_probe:
  let sa = initial_compile_state "@wcopy_exit_2";
      vv = LocatedValue (TupleT []) (mk_ptr (Lit 0w) LocStorage);
      sb = SND (compile_materialize_vv ce (TupleT []) vv sa);
      fn = venomInst$mk_raw_function "materialize-probe" sb.cs_blocks
  in
    sb.cs_current_bb = sa.cs_current_bb /\ sb.cs_current_insts = [] /\
    (MAP (\i. i.inst_opcode)
      (THE (lookup_block sb.cs_current_bb fn.fn_blocks)).bb_instructions =
      [ALLOCA; ALLOCA; ASSIGN; JMP]) /\
    (MAP (\i. i.inst_opcode)
      (THE (lookup_block "@wcopy_cond_0" fn.fn_blocks)).bb_instructions =
      [EQ; JNZ])
Proof
  EVAL_TAC
QED

Definition materialize_zero_probe_fn_def:
  materialize_zero_probe_fn ce =
    let sa = initial_compile_state "@wcopy_exit_2";
        vv = LocatedValue (TupleT []) (mk_ptr (Lit 0w) LocStorage);
        sb = SND (compile_materialize_vv ce (TupleT []) vv sa)
    in venomInst$mk_raw_function "materialize-probe" sb.cs_blocks
End

Definition materialize_zero_probe_next_def:
  materialize_zero_probe_next fn s =
    let bb = THE (lookup_block s.vs_current_bb fn.fn_blocks);
        inst = THE (get_instruction bb s.vs_inst_idx)
    in case venomExecSemantics$step_inst_base inst s of
         OK t => if is_terminator inst.inst_opcode then t
                 else t with vs_inst_idx := SUC s.vs_inst_idx
       | _ => s
End

Definition materialize_zero_probe_trace_def:
  materialize_zero_probe_trace ce 0 = init_venom_state "@wcopy_exit_2" /\
  materialize_zero_probe_trace ce (SUC n) =
    materialize_zero_probe_next (materialize_zero_probe_fn ce)
      (materialize_zero_probe_trace ce n)
End

Theorem materialize_zero_probe_edges:
  !n. n < 6 ==>
    fragGasPath$gas_path_edge ctx (materialize_zero_probe_fn ce)
      (materialize_zero_probe_trace ce n) 0
      (OK (materialize_zero_probe_trace ce (SUC n)))
Proof
  rpt strip_tac >>
  `n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5` by decide_tac >>
  gvs[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``fragGasPath$gas_path_edge``]) >>
  simp[fragGasPathTheory.gas_path_edge_def] >>
  qexists_tac `0` >>
  CONV_TAC (BINDER_CONV (BINDER_CONV (LAND_CONV (RAND_CONV EVAL)))) >>
  simp[venomInstTheory.get_instruction_def] >> EVAL_TAC >> simp[] >>
  disj2_tac >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM boolTheory.ETA_THM))) >>
  qexists_tac `"@wcopy_cond_0"` >> simp[]
QED

Theorem materialize_zero_probe_path:
  !n. n <= 6 ==>
    fragGasPath$gas_path ctx (materialize_zero_probe_fn ce)
      (materialize_zero_probe_trace ce 0) 0
      (OK (materialize_zero_probe_trace ce n))
Proof
  Induct >> rpt strip_tac
  >- (irule (cj 1 fragGasPathTheory.gas_path_rules) >> EVAL_TAC) >>
  `fragGasPath$gas_path ctx (materialize_zero_probe_fn ce)
      (materialize_zero_probe_trace ce 0) 0
      (OK (materialize_zero_probe_trace ce n))` by
    (first_x_assum irule >> decide_tac) >>
  `fragGasPath$gas_path_edge ctx (materialize_zero_probe_fn ce)
      (materialize_zero_probe_trace ce n) 0
      (OK (materialize_zero_probe_trace ce (SUC n)))` by
    (irule materialize_zero_probe_edges >> decide_tac) >>
  metis_tac[fragGasPathTheory.gas_path_rules,
            fragGasPathTheory.gas_path_edge_normal,
            fragGasPathTheory.gas_path_then, arithmeticTheory.ADD]
QED

Theorem materialize_zero_probe_endpoint:
  let t = materialize_zero_probe_trace ce 6 in
    ~t.vs_halted /\ t.vs_current_bb = "@wcopy_exit_2" /\
    t.vs_inst_idx = 0 /\
    FLOOKUP t.vs_allocas 0 = SOME (0,0) /\
    FLOOKUP t.vs_allocas 1 = SOME (0,0) /\
    lookup_var "%3" t = SOME 1w
Proof
  EVAL_TAC >> simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem materialize_equal_zero_counted_probe:
  let t = materialize_zero_probe_trace ce 6 in
    gas_marked_path F ctx (materialize_zero_probe_fn ce)
      (init_venom_state "@wcopy_exit_2") 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = "@wcopy_exit_2" /\
    t.vs_inst_idx = 0 /\ FLOOKUP t.vs_allocas 0 = SOME (0,0)
Proof
  simp[fragGasModeTheory.gas_marked_path_def] >>
  mp_tac (Q.SPEC `6` materialize_zero_probe_path) >>
  mp_tac materialize_zero_probe_endpoint >>
  simp[materialize_zero_probe_trace_def]
QED
