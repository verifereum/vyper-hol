Theory exprSimAbiEncodeArgsMaterializePath
Libs exprSimAbiEncodeArgsProbeLib
Ancestors
  abiEncodeMaterialize exprSimAbiGasBridge exprSimHash vyperCompiler context
  loweringPosts compileEnv finite_map exprSimAbiEncodeSeparation
  entrySinkExtraction fragGasSeq stmtReasonLitFragMemory emitHelperProps
  abiDecodeStaticProps fragGasMode list exprSimHyps
  exprSimAggregateLayout storageCopyGasPath

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

Theorem materialize_expr_post_returndata[local]:
  expr_post ctx func ce cx e es sa sb s0 es' v op
    (s with vs_returndata := rd) <=>
  expr_post ctx func ce cx e es sa sb s0 es' v op s
Proof
  Cases_on `op` >>
  simp[expr_post_def, hash_returndata_state_rel,
       expr_val_rel_def, expr_val_at_def, expr_val_own_def,
       locals_kept_def, popped_kept_def, local_region_def,
       venomStateTheory.lookup_var_def, venomStateTheory.eval_operand_def]
QED

Theorem materialize_unwrap_owned_straight_path[local]:
  unwrap_value ce vv sm = (op,su) /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= sm.cs_next_id /\
  read_result cx tvv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
         ~is_word_type (post_value_type ce e) ==>
         type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
         type_memory_size tvt < 2 ** 64) /\
  not_fresh_at sm p /\ lookup_var p r = SOME w /\
  FLOOKUP r.vs_allocas aid = SOME (w2n w,sz) /\
  cs_extends sm su /\ frag_gas_free sm su /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func r 0 (OK u) /\
      expr_post ctx func ce cx e es'
        (sa with cs_next_var := sm.cs_next_var) su r es' v op u /\
      lookup_var p u = SOME w /\
      FLOOKUP u.vs_allocas aid = SOME (w2n w,sz) /\
      ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
      u.vs_inst_idx = LENGTH su.cs_current_insts
Proof
  strip_tac >> drule_all materialize_unwrap_owned_sim >>
  disch_then (qspec_then `\r. F` mp_tac) >> strip_tac >>
  drule frag_exec_gas_path >>
  disch_then (qspecl_then [`func`, `r`] mp_tac) >>
  simp[materialize_expr_post_returndata, venomStateTheory.lookup_var_def] >>
  metis_tac[]
QED

Theorem materialize_unwrap_identity_path[local]:
  unwrap_value ce vv sm = (op,su) /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= sm.cs_next_id /\
  read_result cx tvv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
         ~is_word_type (post_value_type ce e) ==>
         type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
         type_memory_size tvt < 2 ** 64) /\
  not_fresh_at sm p /\ lookup_var p r = SOME w /\
  FLOOKUP r.vs_allocas aid = SOME (w2n w,sz) /\
  ((?ty src. vv = StackValue ty src) \/
   (?ty ptr. vv = LocatedValue ty ptr /\ ~is_word_type ty /\
             ptr.ptr_location = LocMemory)) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func r 0 (OK u) /\
      expr_post ctx func ce cx e es'
        (sa with cs_next_var := sm.cs_next_var) su r es' v op u /\
      lookup_var p u = SOME w /\
      FLOOKUP u.vs_allocas aid = SOME (w2n w,sz) /\
      ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
      u.vs_inst_idx = LENGTH su.cs_current_insts
Proof
  strip_tac >>
  `cs_extends sm su /\ frag_gas_free sm su` by
    (gvs[exprLoweringTheory.unwrap_value_def, comp_return_def] >>
     simp[cs_extends_refl, frag_gas_free_def, frag_code_def,
          fragExecTheory.emitted_blocks_def, exprLoweringPropsTheory.emitted_insts_def]) >>
  drule_all materialize_unwrap_owned_straight_path >> simp[]
QED

Theorem materialize_unwrap_word_region[local]:
  unwrap_value ce (LocatedValue ty psrc) sm = (op,su) /\
  is_word_type ty /\ psrc.ptr_location <> LocCode /\
  (!l. psrc.ptr_operand <> Label l) ==>
  cs_extends sm su /\ frag_gas_free sm su
Proof
  Cases_on `psrc.ptr_location` >>
  simp[exprLoweringTheory.unwrap_value_def, contextTheory.compile_ptr_load_def,
       emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_return_def] >> rpt strip_tac >>
  gvs[emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[cs_extends_def, frag_gas_free_def, frag_code_def,
       fragExecTheory.emitted_blocks_def, exprLoweringPropsTheory.emitted_insts_def,
       rich_listTheory.DROP_APPEND, arithmeticTheory.SUB_EQ_0,
       venomInstTheory.mk_inst_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem materialize_straight_zero_path[local]:
  frag_exec ctx sm su P Q (\r. F) /\
  dec_straight sm su /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sm su) /\
  fn_has_code sm su func /\ P r /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func r 0 (OK u) /\ Q u /\
      ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
      u.vs_inst_idx = LENGTH su.cs_current_insts
Proof
  strip_tac >> drule_all frag_exec_straight_run >> strip_tac >>
  `su.cs_current_bb = sm.cs_current_bb /\
   su.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm su /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm su)` by
    gvs[dec_straight_def, inst_extends_def] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm su)) = 0` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[EVERY_MEM]) >>
  drule_all hash_run_path >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `u with vs_inst_idx := LENGTH su.cs_current_insts` >> simp[]
QED

Theorem materialize_unwrap_word_straight[local]:
  unwrap_value ce (LocatedValue ty src) sm = (op,su) /\
  is_word_type ty /\ src.ptr_location <> LocCode ==>
  dec_straight sm su /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sm su)
Proof
  Cases_on `src.ptr_location` >>
  simp[exprLoweringTheory.unwrap_value_def, contextTheory.compile_ptr_load_def,
       emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_return_def] >> rpt strip_tac >>
  gvs[emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[dec_straight_def, inst_extends_def, exprLoweringPropsTheory.emitted_insts_def,
       rich_listTheory.DROP_APPEND, arithmeticTheory.SUB_EQ_0,
       venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]
QED

Theorem materialize_captured_post_copy_ok:
  expr_body_pre ce cx env e es /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 ==>
  !tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
        ~is_word_type (post_value_type ce e) ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
    type_memory_size tvt < 2 ** 64
Proof
  strip_tac >>
  `post_value_type ce e = expr_type e \/
   post_value_type ce e = lowered_value_type ce e` by
    (Cases_on `e` >> simp[post_value_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
     simp[post_value_type_def, vyperASTTheory.expr_type_def] >>
     IF_CASES_TAC >> simp[]) >>
  rpt strip_tac >> gvs[] >> drule_all expr_body_pre_copy_ok >> simp[]
QED

Theorem materialize_physical_copy_capacity:
  type_memory_bytes ce ty = type_memory_size tv /\
  b + type_memory_bytes ce ty < dimword (:256) ==>
  32 * ((type_memory_bytes ce ty + 31) DIV 32) = type_memory_bytes ce ty /\
  (type_memory_bytes ce ty + 31) DIV 32 < 2 ** 256 /\
  b + 32 * ((type_memory_bytes ce ty + 31) DIV 32) < 2 ** 256
Proof
  strip_tac >>
  `type_memory_bytes ce ty MOD 32 = 0` by
    metis_tac[type_memory_size_aligned] >>
  `32 * ((type_memory_bytes ce ty + 31) DIV 32) = type_memory_bytes ce ty` by
    intLib.COOPER_TAC >>
  gvs[wordsTheory.dimword_def] >> intLib.COOPER_TAC
QED

Theorem materialize_physical_storage_copy_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src dst ((type_memory_bytes ce ty + 31) DIV 32)
    loc LocMemory F sa = (u,sb) /\
  type_memory_bytes ce ty = type_memory_size tv /\
  b + type_memory_bytes ce ty < dimword (:256) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      copy_prefix loc a b ((type_memory_bytes ce ty + 31) DIV 32)
        s ((type_memory_bytes ce ty + 31) DIV 32) t /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all materialize_physical_copy_capacity >> strip_tac >>
  irule (PairRules.PSPEC_ALL compile_storage_copy_content_capacity_path) >>
  simp[] >> metis_tac[]
QED

Theorem materialize_captured_located_nonword:
  expr_body_pre ce cx env e es_pre /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv (LocatedValue vty src) r /\
  ~is_word_type (expr_type e) ==>
  ~is_word_type vty /\ src.ptr_location <> LocCalldata
Proof
  strip_tac >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `~is_word_type (lowered_value_type ce e)` by
    metis_tac[exprSimLayoutTransportTheory.compatible_word_type] >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[materialize_post_lowered_classify,
              valueCopyBytesTheory.is_bytestring_word_type] >>
  `~is_word_type vty` by
    (gvs[vv_post_def, vv_holds_def] >>
     metis_tac[valueCopyBytesTheory.is_bytestring_word_type]) >>
  simp[] >> Cases_on `src.ptr_location` >>
  gvs[vv_post_def, vv_holds_def]
QED

Theorem materialize_unwrap_owned_path:
  unwrap_value ce vv sm = (op,su) /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= sm.cs_next_id /\
  read_result cx tvv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
         ~is_word_type (post_value_type ce e) ==>
         type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
         type_memory_size tvt < 2 ** 64) /\
  not_fresh_at sm p /\ lookup_var p r = SOME w /\
  FLOOKUP r.vs_allocas aid = SOME (w2n w,sz) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func r 0 (OK u) /\
      expr_post ctx func ce cx e es'
        (sa with cs_next_var := sm.cs_next_var) su r es' v op u /\
      lookup_var p u = SOME w /\
      FLOOKUP u.vs_allocas aid = SOME (w2n w,sz) /\
      ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
      u.vs_inst_idx = LENGTH su.cs_current_insts
Proof
  strip_tac >> Cases_on `vv`
  >- (irule materialize_unwrap_identity_path >> simp[] >> metis_tac[]) >>
  rename1 `LocatedValue vty src` >>
  Cases_on `is_word_type vty`
  >- (Cases_on `src.ptr_location = LocCode`
      >- cheat >>
      drule_all materialize_unwrap_word_straight >> strip_tac >>
      drule_all materialize_unwrap_owned_sim >>
      disch_then (qspec_then `\r. F` mp_tac) >> strip_tac >>
      drule materialize_straight_zero_path >>
      disch_then (qspec_then `r` mp_tac) >> simp[] >> metis_tac[]) >>
  Cases_on `src.ptr_location`
  >- (irule materialize_unwrap_identity_path >> simp[] >> metis_tac[])
  >- cheat
  >- cheat
  >- cheat >>
  gvs[vv_post_def, vv_holds_def]
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


(* Lift the actual ALLOCA result, including allocation-map reentry. *)
Theorem materialize_alloc_run_path:
  compile_alloc_buffer sz sa = (buf,sb) /\ fn_has_code sa sb fn /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_marked_path F ctx fn s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
     ["%" ++ toString sa.cs_next_var]) s = OK t /\
   ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
     get_instruction bb (LENGTH sa.cs_current_insts) =
       SOME (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
         ["%" ++ toString sa.cs_next_var])` by
    (gvs[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
         fresh_id_def, fresh_var_def, emit_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, exprLoweringPropsTheory.emitted_insts_def,
         rich_listTheory.DROP_APPEND, arithmeticTheory.SUB_EQ_0,
         exprLoweringPropsTheory.run_inst_seq_def, AllCaseEqs(), fragExecTheory.fn_has_code_def,
         rich_listTheory.IS_PREFIX_APPEND] >>
     simp[venomInstTheory.get_instruction_def, listTheory.EL_APPEND_EQN] >>
     metis_tac[]) >>
  `~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[venomExecSemanticsTheory.step_inst_base_def,
          venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_alloca_def,
          venomStateTheory.eval_operand_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
     >- (simp[venomStateTheory.update_var_def] >> strip_tac >> gvs[]) >>
     rename1 `SOME entry` >> PairCases_on `entry` >>
     simp[venomStateTheory.update_var_def] >> strip_tac >> gvs[]) >>
  `fragGasPath$gas_path_edge ctx fn s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (simp[fragGasPathTheory.gas_path_edge_def] >> qexists_tac `0` >>
     simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
          gasCountTheory.gas_count_step_def] >>
     disj1_tac >> qexists_tac `t` >>
     gvs[venomExecSemanticsTheory.step_inst_non_invoke,
          GSYM venomInstTheory.mk_inst_def]) >>
  fs[fragGasModeTheory.gas_marked_path_def] >>
  qpat_x_assum `gas_path_edge _ _ _ _ _` mp_tac >>
  simp[] >> strip_tac >>
  drule (cj 2 fragGasPathTheory.gas_path_rules) >>
  disch_then (qspecl_then [`0`, `OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`] mp_tac) >>
  simp[fragGasPathTheory.gas_path_rules]
QED

Theorem materialize_alloc_semantic_path:
  compile_alloc_buffer sz sa = (buf,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn ce cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved ce sa /\
  sz < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t w. gas_marked_path F ctx fn s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx fn ce cx es t /\
    eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\
    t.vs_memory = s.vs_memory /\ sa.cs_next_id < sb.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region ce es.scopes t name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sb p)
Proof
  strip_tac >> drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all exprSimAllocTheory.literal_alloc_buffer_run >> strip_tac >>
  drule_all materialize_alloc_run_path >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `w`] >>
  simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       local_region_def] >>
  gvs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
      local_region_def] >> metis_tac[]
QED

Theorem materialize_zero_slot_prefixes:
  compile_materialize_vv ce ty (LocatedValue vty p) sa = (dst,sb) /\
  ~is_word_type ty /\ type_memory_bytes ce ty = 0 /\
  ~is_word_type vty /\ type_memory_bytes ce vty = 0 /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  fn_has_code sa sb fn /\ local_ptrs_reserved ce sa ==>
  ?tmp src mid su u.
    compile_alloc_buffer 0 sa = (tmp,mid) /\
    compile_alloc_buffer 0 mid = (src,su) /\
    compile_word_copy_loop p.ptr_operand src.buf_operand 0
      p.ptr_location LocMemory F su = (u,sb) /\
    dst = tmp.buf_operand /\
    fn_has_code sa mid fn /\ fn_has_code mid su fn /\ fn_has_code su sb fn /\
    local_ptrs_reserved ce mid /\ sa.cs_next_var <= mid.cs_next_var /\
    mid.cs_next_var <= su.cs_next_var
Proof
  strip_tac >>
  `?tmp mid src su u.
    compile_alloc_buffer 0 sa = (tmp,mid) /\
    compile_alloc_buffer 0 mid = (src,su) /\
    compile_word_copy_loop p.ptr_operand src.buf_operand 0
      p.ptr_location LocMemory F su = (u,sb) /\ dst = tmp.buf_operand` by
    (gvs[materialize_zero_slot_shape, comp_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
     pairarg_tac >> gvs[] >> metis_tac[]) >>
  `cs_extends sa mid /\ cs_extends mid su /\ cs_extends su sb` by
    (imp_res_tac loweringHaltTheory.compile_alloc_buffer_extends >>
     mp_tac (Q.SPECL [`p.ptr_operand`, `src.buf_operand`, `0`,
       `p.ptr_location`, `LocMemory`, `F`, `su`]
       exprLoweringPropsTheory.ci_mono_compile_word_copy_loop) >>
     gvs[exprLoweringPropsTheory.ci_mono_def]) >>
  `fn_has_code sa mid fn /\ fn_has_code mid su fn /\ fn_has_code su sb fn` by
    (metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans]) >>
  `sa.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= su.cs_next_var` by
    (imp_res_tac loweringHaltTheory.compile_alloc_buffer_emission >> simp[]) >>
  `local_ptrs_reserved ce mid` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  metis_tac[]
QED

Theorem materialize_zero_slot_execution:
  compile_materialize_vv ce ty (LocatedValue vty p) sa = (dst,sb) /\
  ~is_word_type ty /\ type_memory_bytes ce ty = 0 /\
  ~is_word_type vty /\ type_memory_bytes ce vty = 0 /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  fn_has_code sa sb fn /\ local_ptrs_reserved ce sa /\
  stmt_state_rel ctx fn ce cx es s /\ fn_inst_ids_distinct fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t mid su z w.
    gas_marked_path F ctx fn s 0 (OK t) /\
    t = jump_to sb.cs_current_bb
      (update_var ("%" ++ toString (su.cs_next_var+1)) 1w
        (jump_to (fresh_label_output "wcopy_cond" su.cs_next_label)
          (update_var ("%" ++ toString su.cs_next_var) 0w z))) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand dst z = SOME w /\
    FLOOKUP z.vs_allocas sa.cs_next_id = SOME (w2n w,0) /\
    z.vs_memory = s.vs_memory /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP z.vs_allocas aid = SOME entry) /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    sa.cs_next_id < mid.cs_next_id /\
    sa.cs_next_var < mid.cs_next_var /\ mid.cs_next_var < su.cs_next_var /\
    eval_operand dst t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,0) /\
    t.vs_memory = s.vs_memory /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> (drule materialize_zero_slot_prefixes >>
  disch_then (qspec_then `fn` mp_tac) >> simp[] >> strip_tac >>
  `0 < dimword (:256)` by simp[] >>
  drule_all materialize_alloc_semantic_path >>
  disch_then (qx_choose_then `a` (qx_choose_then `w` strip_assume_tac)) >>
  drule_all materialize_alloc_semantic_path >>
  disch_then (qx_choose_then `z` (qx_choose_then `w2` strip_assume_tac)) >>
  drule materialize_zero_loop_path >>
  disch_then (qspecl_then [`z`, `fn`, `ctx`] mp_tac) >>
  simp[] >> strip_tac >>
  `sb.cs_current_insts = []` by
    (drule materialize_zero_loop_layout >>
     disch_then (qspec_then `fn` mp_tac) >> simp[]) >>
  `sa.cs_next_var < mid.cs_next_var /\ mid.cs_next_var < su.cs_next_var` by
    (imp_res_tac loweringHaltTheory.compile_alloc_buffer_emission >> simp[]) >>
  `gas_marked_path F ctx fn s 0 (OK z)` by
    (irule (fragGasModeTheory.gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SIMP_RULE (srw_ss()) []) >>
     qexists_tac `a` >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at mid x` by
       (irule freshWritesTheory.not_fresh_at_mono >>
        qexists_tac `sa` >> simp[]) >> simp[]) >>
  `eval_operand dst z = SOME w` by
    (gvs[venomStateTheory.eval_operand_def] >> simp[]) >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP z.vs_allocas aid = SOME entry` by metis_tac[] >>
  qexistsl_tac [`mid`, `su`, `z`, `w`] >>
  conj_tac
  >- (irule (fragGasModeTheory.gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SIMP_RULE (srw_ss()) []) >>
      qexists_tac `z` >> simp[]) >>
  `!x. not_fresh_at mid x ==>
     x <> "%" ++ toString su.cs_next_var /\
     x <> "%" ++ toString (su.cs_next_var+1)` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ, arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
  gvs[venomStateTheory.jump_to_def, venomStateTheory.update_var_def,
      venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  `not_fresh_at mid x` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  fs[not_fresh_at_def] >> metis_tac[] )
QED

Theorem materialize_zero_code_execution:
  compile_materialize_vv ce ty (LocatedValue vty p) sa = (dst,sb) /\
  ~is_word_type ty /\ type_memory_bytes ce ty = 0 /\
  ~is_word_type vty /\ type_memory_bytes ce vty = 0 /\
  p.ptr_location = LocCode /\
  fn_has_code sa sb fn /\ local_ptrs_reserved ce sa /\
  stmt_state_rel ctx fn ce cx es s /\ fn_inst_ids_distinct fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t w. gas_marked_path F ctx fn s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx fn ce cx es t /\
    eval_operand dst t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,0) /\
    t.vs_memory = s.vs_memory /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `?tmp mid src. compile_alloc_buffer 0 sa = (tmp,mid) /\
     compile_alloc_buffer 0 mid = (src,sb) /\ dst = tmp.buf_operand` by
    (gvs[materialize_zero_code_shape, comp_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> metis_tac[]) >>
  `cs_extends sa mid /\ cs_extends mid sb` by
    metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `fn_has_code sa mid fn /\ fn_has_code mid sb fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `sa.cs_next_var <= mid.cs_next_var` by
    (imp_res_tac loweringHaltTheory.compile_alloc_buffer_emission >> simp[]) >>
  `local_ptrs_reserved ce mid` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `0 < dimword (:256)` by simp[] >>
  drule_all materialize_alloc_semantic_path >>
  disch_then (qx_choose_then `a` (qx_choose_then `w` strip_assume_tac)) >>
  drule_all materialize_alloc_semantic_path >>
  disch_then (qx_choose_then `z` (qx_choose_then `w2` strip_assume_tac)) >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at mid x` by
       (irule freshWritesTheory.not_fresh_at_mono >>
        qexists_tac `sa` >> simp[]) >> simp[]) >>
  qexistsl_tac [`z`, `w`] >> conj_tac
  >- (irule (fragGasModeTheory.gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SIMP_RULE (srw_ss()) []) >>
      qexists_tac `a` >> simp[]) >>
  gvs[venomStateTheory.eval_operand_def] >> metis_tac[]
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
  simp[]
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

(* Test whether a nonempty final copy alone prevents an aliased cut. *)
Theorem materialize_positive_cut_alias_probe:
  let ty = TupleT [BaseT (UintT 256); BaseT (UintT 256)];
      vv = LocatedValue ty (mk_ptr (Lit 0w) LocStorage);
      base = initial_compile_state "@wcopy_exit_2";
      end0 = SND (compile_materialize_vv ce ty vv base);
      sa = base with cs_current_insts := end0.cs_current_insts;
      sb = SND (compile_materialize_vv ce ty vv sa);
      fn = venomInst$mk_raw_function "positive-cut-probe" sb.cs_blocks
  in
    0 < type_memory_bytes ce ty /\
    sb.cs_current_insts <> [] /\
    fragExec$fn_has_code sa sb fn /\ venomWf$fn_inst_ids_distinct fn /\
    ~frag_gas_free sa sb
Proof
  EVAL_TAC >> rpt conj_tac >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED


Definition materialize_positive_probe_fn_def:
  materialize_positive_probe_fn ce =
    let ty = TupleT [BaseT (UintT 256); BaseT (UintT 256)];
        vv = LocatedValue ty (mk_ptr (Lit 0w) LocStorage);
        base = initial_compile_state "@wcopy_exit_2";
        end0 = SND (compile_materialize_vv ce ty vv base);
        sa = base with cs_current_insts := end0.cs_current_insts;
        sb = SND (compile_materialize_vv ce ty vv sa)
    in venomInst$mk_raw_function "positive-cut-probe" sb.cs_blocks
End

Definition materialize_positive_probe_trace_def:
  materialize_positive_probe_trace ce 0 =
    (init_venom_state "@wcopy_exit_2" with vs_inst_idx := 1) /\
  materialize_positive_probe_trace ce (SUC n) =
    materialize_zero_probe_next (materialize_positive_probe_fn ce)
      (materialize_positive_probe_trace ce n)
End

Theorem materialize_positive_probe_endpoint:
  let t = materialize_positive_probe_trace ce 27 in
    ~t.vs_halted /\ t.vs_current_bb = "@wcopy_exit_2" /\
    t.vs_inst_idx = 1
Proof
  CONV_TAC (computeLib.CBV_CONV
    (wordsLib.add_words_compset true (computeLib.copy (computeLib.the_compset()))))
QED

Theorem materialize_positive_probe_edges:
  !n. n < 27 ==>
    fragGasPath$gas_path_edge ctx (materialize_positive_probe_fn ce)
      (materialize_positive_probe_trace ce n) 0
      (OK (materialize_positive_probe_trace ce (SUC n)))
Proof
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "last" >> suspend "earlier"
QED

Resume materialize_positive_probe_edges[last]:
  CONV_TAC (RAND_CONV (computeLib.CBV_CONV
      (wordsLib.add_words_compset true (computeLib.copy (computeLib.the_compset()))))) >>
  CONV_TAC (RATOR_CONV (computeLib.CBV_CONV
      (wordsLib.add_words_compset true (computeLib.copy (computeLib.the_compset()))))) >>
  simp[fragGasPathTheory.gas_path_edge_def] >>
  qexists_tac `0` >>
  CONV_TAC (BINDER_CONV (BINDER_CONV (LAND_CONV (RAND_CONV EVAL)))) >>
  simp[venomInstTheory.get_instruction_def] >> EVAL_TAC >> simp[] >>
  disj2_tac >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM boolTheory.ETA_THM))) >> simp[]
QED

Resume materialize_positive_probe_edges[earlier]:
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step25" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step24" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step23" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step22" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step21" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step20" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step19" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step18" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step17" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step16" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step15" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step14" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step13" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step12" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step11" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step10" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step9" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step8" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step7" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step6" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step5" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step4" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step3" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step2" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step1" >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- suspend "step0" >> simp[]
QED

Resume materialize_positive_probe_edges[step25]:
  CONV_TAC (RAND_CONV (computeLib.CBV_CONV
    (wordsLib.add_words_compset true (computeLib.copy (computeLib.the_compset()))))) >>
  CONV_TAC (RATOR_CONV (computeLib.CBV_CONV
    (wordsLib.add_words_compset true (computeLib.copy (computeLib.the_compset()))))) >>
  simp[fragGasPathTheory.gas_path_edge_def] >> qexists_tac `0` >>
  CONV_TAC (BINDER_CONV (BINDER_CONV (LAND_CONV (RAND_CONV EVAL)))) >>
  simp[venomInstTheory.get_instruction_def] >> EVAL_TAC >> simp[] >>
  disj2_tac >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM boolTheory.ETA_THM))) >> simp[]
QED

Resume materialize_positive_probe_edges[step24]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step23]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step22]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step21]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step20]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step19]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step18]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step17]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step16]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step15]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step14]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step13]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step12]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step11]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step10]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step9]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step8]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step7]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step6]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step5]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step4]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step3]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step2]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step1]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED
Resume materialize_positive_probe_edges[step0]:
  exprSimAbiEncodeArgsProbeLib.probe_eval_target >>
  exprSimAbiEncodeArgsProbeLib.probe_eval_source >>
  exprSimAbiEncodeArgsProbeLib.probe_fetch >>
  exprSimAbiEncodeArgsProbeLib.probe_step >>
  exprSimAbiEncodeArgsProbeLib.probe_jump
QED

Finalise materialize_positive_probe_edges

Theorem materialize_positive_probe_path:
  !n. n <= 27 ==>
    fragGasPath$gas_path ctx (materialize_positive_probe_fn ce)
      (materialize_positive_probe_trace ce 0) 0
      (OK (materialize_positive_probe_trace ce n))
Proof
  Induct >> rpt strip_tac
  >- (irule (cj 1 fragGasPathTheory.gas_path_rules) >> EVAL_TAC) >>
  `fragGasPath$gas_path ctx (materialize_positive_probe_fn ce)
      (materialize_positive_probe_trace ce 0) 0
      (OK (materialize_positive_probe_trace ce n))` by
    (first_x_assum irule >> decide_tac) >>
  `fragGasPath$gas_path_edge ctx (materialize_positive_probe_fn ce)
      (materialize_positive_probe_trace ce n) 0
      (OK (materialize_positive_probe_trace ce (SUC n)))` by
    (irule materialize_positive_probe_edges >> decide_tac) >>
  metis_tac[fragGasPathTheory.gas_path_rules,
            fragGasPathTheory.gas_path_edge_normal,
            fragGasPathTheory.gas_path_then, arithmeticTheory.ADD]
QED

Theorem materialize_positive_alias_counted_probe:
  let t = materialize_positive_probe_trace ce 27 in
    gas_marked_path F ctx (materialize_positive_probe_fn ce)
      (init_venom_state "@wcopy_exit_2" with vs_inst_idx := 1) 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = "@wcopy_exit_2" /\
    t.vs_inst_idx = 1
Proof
  simp[fragGasModeTheory.gas_marked_path_def] >>
  mp_tac (Q.SPEC `27` materialize_positive_probe_path) >>
  mp_tac materialize_positive_probe_endpoint >>
  simp[materialize_positive_probe_trace_def]
QED

(* A legacy fragment specifies continuation results, not the state reached
   by an arbitrary finite path to the same cursor. *)
Theorem materialize_same_cut_identity[local]:
  sa.cs_current_bb = sb.cs_current_bb /\
  LENGTH sa.cs_current_insts = LENGTH sb.cs_current_insts ==>
  frag_exec ctx sa sb (\s. s = initial) (\s. s = initial) (\r. F)
Proof
  rw[fragExecTheory.frag_exec_def] >> metis_tac[]
QED

Theorem materialize_zero_endpoint_transfer_probe:
  let sa = initial_compile_state "@wcopy_exit_2";
      vv = LocatedValue (TupleT []) (mk_ptr (Lit 0w) LocStorage);
      sb = SND (compile_materialize_vv ce (TupleT []) vv sa);
      initial = init_venom_state "@wcopy_exit_2";
      t = materialize_zero_probe_trace ce 6
  in
    frag_exec ctx sa sb (\s. s = initial) (\s. s = initial) (\r. F) /\
    gas_marked_path F ctx (materialize_zero_probe_fn ce) initial 0 (OK t) /\
    t <> initial
Proof
  simp_tac (srw_ss()) [LET_THM] >> conj_tac
  >- (irule materialize_same_cut_identity >> EVAL_TAC) >>
  conj_tac
  >- metis_tac[materialize_equal_zero_counted_probe] >>
  `FLOOKUP (materialize_zero_probe_trace ce 6).vs_allocas 0 = SOME (0,0)` by
    metis_tac[materialize_zero_probe_endpoint] >>
  strip_tac >> gvs[venomStateTheory.init_venom_state_def]
QED

Theorem materialize_positive_endpoint_transfer_probe:
  let ty = TupleT [BaseT (UintT 256); BaseT (UintT 256)];
      vv = LocatedValue ty (mk_ptr (Lit 0w) LocStorage);
      base = initial_compile_state "@wcopy_exit_2";
      end0 = SND (compile_materialize_vv ce ty vv base);
      sa = base with cs_current_insts := end0.cs_current_insts;
      sb = SND (compile_materialize_vv ce ty vv sa);
      initial = init_venom_state "@wcopy_exit_2" with vs_inst_idx := 1;
      t = materialize_positive_probe_trace ce 27
  in
    frag_exec ctx sa sb (\s. s = initial) (\s. s = initial) (\r. F) /\
    gas_marked_path F ctx (materialize_positive_probe_fn ce) initial 0 (OK t) /\
    t <> initial
Proof
  simp_tac (srw_ss()) [LET_THM] >> conj_tac
  >- (irule materialize_same_cut_identity >> EVAL_TAC) >>
  conj_tac
  >- metis_tac[materialize_positive_alias_counted_probe] >>
  `FLOOKUP (materialize_positive_probe_trace ce 27).vs_allocas 0 = SOME (0,64)` by
    (CONV_TAC (computeLib.CBV_CONV
      (wordsLib.add_words_compset true (computeLib.copy (computeLib.the_compset()))))) >>
  strip_tac >> gvs[venomStateTheory.init_venom_state_def]
QED

Theorem materialize_straight_free_trans[local]:
  dec_straight sa sm /\ dec_straight sm sb /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sm) /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sm sb) ==>
  dec_straight sa sb /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  strip_tac >> conj_tac >- metis_tac[dec_straight_trans] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule exprLoweringPropsTheory.emitted_insts_append >>
     gvs[dec_straight_def, inst_extends_def]) >> simp[]
QED

Theorem materialize_offset_straight_free[local]:
  compile_lit_byte_offset op off sa = (r,sb) ==>
  dec_straight sa sb /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Cases_on `off = 0` >> Cases_on `op` >>
  simp[contextTheory.compile_lit_byte_offset_def,
       emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_return_def] >> rpt strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  simp[dec_straight_def, inst_extends_def,
       exprLoweringPropsTheory.emitted_insts_def, rich_listTheory.DROP_APPEND,
       arithmeticTheory.SUB_EQ_0, arithmeticTheory.SUB_PLUS,
       venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]
QED

Theorem materialize_imm_load_straight_free[local]:
  compile_imm_load_word ctor imm src sa = (r,sb) ==>
  dec_straight sa sb /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Cases_on `ctor` >> Cases_on `imm` >>
  simp[contextTheory.compile_imm_load_word_def,
       emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_return_def] >> rpt strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  simp[dec_straight_def, inst_extends_def,
       exprLoweringPropsTheory.emitted_insts_def, rich_listTheory.DROP_APPEND,
       arithmeticTheory.SUB_EQ_0, arithmeticTheory.SUB_PLUS,
       venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]
QED

Theorem materialize_mstore_straight_free[local]:
  emit_void MSTORE ops sa = ((),sb) ==>
  dec_straight sa sb /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  strip_tac >> conj_tac
  >- (drule dec_straight_emit_void >>
      simp[venomInstTheory.is_terminator_def]) >>
  drule emitted_insts_emit_void >> simp[venomInstTheory.mk_inst_def]
QED

Theorem materialize_imm_copy_straight_free:
  !n off sa sb.
    compile_imm_copy_to_memory ctor imm src dst n off sa = ((),sb) ==>
    dec_straight sa sb /\
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Induct
  >- simp[contextTheory.compile_imm_copy_to_memory_def, comp_return_def,
          dec_straight_def, inst_extends_def,
          exprLoweringPropsTheory.emitted_insts_def] >>
  rpt gen_tac >>
  simp[Once contextTheory.compile_imm_copy_to_memory_def,
       comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule materialize_offset_straight_free >> strip_tac >>
  drule materialize_imm_load_straight_free >> strip_tac >>
  drule_all materialize_mstore_straight_free >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  metis_tac[materialize_offset_straight_free, materialize_straight_free_trans]
QED

Theorem materialize_alloc_straight_free[local]:
  compile_alloc_buffer sz sa = (buf,sb) ==>
  dec_straight sa sb /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  simp[contextTheory.compile_alloc_buffer_def,
       emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_return_def] >> rpt strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  simp[dec_straight_def, inst_extends_def,
       exprLoweringPropsTheory.emitted_insts_def, rich_listTheory.DROP_APPEND,
       arithmeticTheory.SUB_EQ_0, venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def]
QED

Theorem materialize_unwrap_code_straight_free:
  unwrap_value ce (LocatedValue ty src) sm = (op,su) /\
  ~is_word_type ty /\ src.ptr_location = LocCode ==>
  dec_straight sm su /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sm su)
Proof
  strip_tac >> qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[exprLoweringTheory.unwrap_value_def,
       contextTheory.compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule materialize_alloc_straight_free >> strip_tac >>
  drule materialize_imm_copy_straight_free >> strip_tac >>
  metis_tac[materialize_straight_free_trans]
QED

Theorem materialize_unwrap_code_owned_path:
  unwrap_value ce (LocatedValue ty src) sm = (op,su) /\
  ~is_word_type ty /\ src.ptr_location = LocCode /\
  local_ptrs_reserved ce sm /\ sa.cs_next_id <= sm.cs_next_id /\
  read_result cx tvv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv (LocatedValue ty src) r /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand (LocatedValue ty src) = Var x ==> not_fresh_at sm x) /\
  (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
         ~is_word_type (post_value_type ce e) ==>
         type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
         type_memory_size tvt < 2 ** 64) /\
  not_fresh_at sm p /\ lookup_var p r = SOME w /\
  FLOOKUP r.vs_allocas aid = SOME (w2n w,sz) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func r 0 (OK u) /\
      expr_post ctx func ce cx e es'
        (sa with cs_next_var := sm.cs_next_var) su r es' v op u /\
      lookup_var p u = SOME w /\
      FLOOKUP u.vs_allocas aid = SOME (w2n w,sz) /\
      ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
      u.vs_inst_idx = LENGTH su.cs_current_insts
Proof
  strip_tac >>
  drule_all materialize_unwrap_code_straight_free >> strip_tac >>
  drule_all materialize_unwrap_owned_sim >>
  disch_then (qspec_then `\r. F` mp_tac) >> strip_tac >>
  drule materialize_straight_zero_path >>
  disch_then (qspecl_then [`r`, `func`] mp_tac) >> simp[] >> metis_tac[]
QED
