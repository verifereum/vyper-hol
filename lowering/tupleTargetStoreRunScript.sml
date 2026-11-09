(* Compiler head boundaries for mixed tuple destinations. *)
Theory tupleTargetStoreRun
Ancestors
  loweringPosts stmtSimDefs stmtSimProps
  tupleAssignParts valueCopy context stmtSimAssignStore fragGasSeq fragGasMode vyperLookup exprSimProps
  loweringSlice
  tupleTargetStoreProps tupleLocalStoreRun stmtSimAssignStorage
  stmtSimAssignAttrStorage stmtLowering exprLowering exprLoweringProps
  storageStoreFrame stmtSimDeclPath stmtSimDecl stmtSimDeclMem venomExecSemantics venomState vyperState
  exprSimBuffer fragExec venomInst ASCIInumbers string rich_list
  emitHelper emitHelperProps compileEnv loweringStateRelDefs list finite_map
  tupleMemoryFrame tupleMemoryLayout valueEncoding valueEncodingDefs valueEncodingProps vyperTyping stmtLoweringMono
  vyperInterpreter freshWrites

Theorem tuple_store_word_step:
  !cenv ty tys bt gs op ops st sp sf dst loc vt.
    compile_tuple_store_all cenv (ty::tys) (BaseTarget bt::gs) (op::ops) st =
      ((), sf) /\
    compile_get_target_ptr compile_expr cenv bt st =
      ((dst, loc, SOME (ValPT vt)), sp) /\
    is_word_type ty /\ is_word_type vt ==>
    ?sm. compile_store_at_loc cenv.ce_imm_alloca dst op loc sp = ((), sm) /\
         compile_tuple_store_all cenv tys gs ops sm = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_tuple_store_all _ _ _ _ _ = _` mp_tac >>
  simp[compile_tuple_store_all_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  Cases_on `compile_store_at_loc cenv.ce_imm_alloca dst op loc sp` >>
  rename1 `compile_store_at_loc _ _ _ _ _ = (u, sm)` >> Cases_on `u` >> simp[]
QED

(* The storage part of either storage head, after its pointer is available. *)
Theorem tuple_storage_store_head_path:
  !ctx func cenv cx es es' s tr slot tv v op dst st st'.
    compile_store_at_loc cenv.ce_imm_alloca dst op
      (SOME (if tr then LocTransient else LocStorage)) st = ((), st') /\
    eval_operand dst s = SOME slot /\
    eval_operand op s = SOME (typed_val_to_w256 tv v) /\
    stmt_state_rel ctx func cenv cx es s /\
    (!u mem. storage_dead cx tr (update_storage slot u mem) =
             storage_dead cx tr mem) /\
    write_storage_slot cx tr slot tv v es = (INL (), es') /\
    encode_value tv v = SOME [(0, typed_val_to_w256 tv v)] /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\
        t.vs_memory = s.vs_memory /\
        ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. lookup_var x t = lookup_var x s) /\
        t.vs_allocas = s.vs_allocas /\
        gas_marked_path F ctx func s 0 (OK t)
Proof
  rpt strip_tac >>
  `~s.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all stmt_state_rel_write_storage_word >> strip_tac >>
  `gas_marked_path F ctx func s 0
    (OK ((if tr then tstore slot (typed_val_to_w256 tv v) s
          else sstore slot (typed_val_to_w256 tv v) s)
      with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule emit_inst_zero_marked_path >> simp[] >>
     qexistsl [`[dst; op]`, `if tr then TSTORE else SSTORE`, `[]`, `st`, `st'`] >>
     Cases_on `tr` >> gvs[compile_store_at_loc_def, emit_void_def,
       emit_inst_def, is_terminator_def] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     fs[mk_inst_def, exec_write2_def]) >>
  `st'.cs_current_bb = st.cs_current_bb /\
   LENGTH st'.cs_current_insts = SUC (LENGTH st.cs_current_insts)` by
    (Cases_on `tr` >> gvs[compile_store_at_loc_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def, emit_def]) >>
  qexists `(if tr then tstore slot (typed_val_to_w256 tv v) s
            else sstore slot (typed_val_to_w256 tv v) s)
      with vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[stmt_state_rel_inst_idx] >>
  Cases_on `tr` >> simp[tstore_def, sstore_def, lookup_var_def, LET_THM]
QED

(* Pointer ADDs preserve the unread tuple and all older loaded operands. *)
Theorem tuple_field_add_frame_path:
  !ctx func cenv cx es s st st' dst slot off.
    emit_op ADD [Lit slot; Lit (n2w off)] st = (dst, st') /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx es t /\
        eval_operand dst t = SOME (slot + n2w off) /\
        t.vs_labels = s.vs_labels /\ t.vs_memory = s.vs_memory /\
        ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
        t.vs_allocas = s.vs_allocas /\
        gas_marked_path F ctx func s 0 (OK t)
Proof
  rpt strip_tac >>
  `!out. step_inst_base (mk_inst st.cs_next_id ADD [Lit slot; Lit (n2w off)] [out]) s =
    OK (update_var out (slot + n2w off) s)` by
    (simp[mk_inst_def, step_inst_base_def, exec_pure2_def, eval_operand_def]) >>
  drule_all (emit_op_zero_path |> Q.INST [`opc` |-> `ADD`]
    |> SRULE [is_terminator_def]) >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString st.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists `st` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es
    (update_var (STRING #"%" (toString st.cs_next_var)) (slot + n2w off) s)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
      comp_ignore_bind_def, comp_return_def, emit_def] >>
  qexists `update_var (STRING #"%" (toString st.cs_next_var)) (slot + n2w off) s
    with vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[gas_marked_path_def, stmt_state_rel_inst_idx, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE, not_fresh_at_def] >>
  fs[update_var_def]
QED

Theorem tuple_field_storage_head_path:
  !ctx func cenv cx es es' s tr slot off tv v op dst st sp sf.
    emit_op ADD [Lit slot; Lit (n2w off)] st = (dst, sp) /\
    compile_store_at_loc cenv.ce_imm_alloca dst op
      (SOME (if tr then LocTransient else LocStorage)) sp = ((), sf) /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st /\
    eval_operand op s = SOME (typed_val_to_w256 tv v) /\
    (!x. op = Var x ==> not_fresh_at st x) /\
    (!u mem. storage_dead cx tr (update_storage (slot + n2w off) u mem) =
             storage_dead cx tr mem) /\
    write_storage_slot cx tr (slot + n2w off) tv v es = (INL (), es') /\
    encode_value tv v = SOME [(0, typed_val_to_w256 tv v)] /\
    fn_has_code st sf func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\
        t.vs_memory = s.vs_memory /\
        ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
        t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        gas_marked_path F ctx func s 0 (OK t)
Proof
  rpt strip_tac >>
  `cs_extends st sp /\ cs_extends sp sf` by
    (Cases_on `tr` >> gvs[compile_store_at_loc_def] >>
     metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND]) >>
  `fn_has_code st sp func /\ fn_has_code sp sf func` by
    metis_tac[fn_has_code_split] >>
  drule_all tuple_field_add_frame_path >> strip_tac >>
  rename1 `stmt_state_rel ctx func cenv cx es mid` >>
  `eval_operand op mid = SOME (typed_val_to_w256 tv v)` by
    (Cases_on `op` >> gvs[eval_operand_def]) >>
  drule_all tuple_storage_store_head_path >> strip_tac >>
  first_assum (irule_at Any) >> simp[] >>
  irule (gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
  first_assum (irule_at Any) >> simp[]
QED

Theorem tuple_store_base_cons:
  !cenv ty tys bt gs op ops st sf.
    compile_tuple_store_all cenv (ty::tys) (BaseTarget bt::gs) (op::ops) st =
      ((),sf) ==>
    ?sm. compile_tuple_store_all cenv [ty] [BaseTarget bt] [op] st = ((),sm) /\
         compile_tuple_store_all cenv tys gs ops sm = ((),sf)
Proof
  rpt gen_tac >>
  simp[compile_tuple_store_all_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem tuple_store_singleton_local_open[local]:
  !cenv id p sz ty op st sf.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME ty /\ 0 < type_memory_bytes cenv ty /\
    compile_tuple_store_all cenv [ty] [BaseTarget (NameTarget id)] [op] st =
      ((),sf) ==> ~block_is_terminated sf
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_tuple_store_all _ _ _ _ _ = _` mp_tac >>
  simp[compile_tuple_store_all_def, compile_get_target_ptr_def,
       compile_store_at_loc_def, compile_assign_value_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_at Any tuple_store_head_code_shape >> simp[]
QED

Theorem tuple_store_singleton_storage_open[local]:
  !cenv bt ty op st sf dst sp tr.
    compile_get_target_ptr compile_expr cenv bt st =
      ((dst, SOME (if tr then LocTransient else LocStorage), SOME (ValPT ty)),sp) /\
    is_word_type ty /\
    compile_tuple_store_all cenv [ty] [BaseTarget bt] [op] st = ((),sf) ==>
    ~block_is_terminated sf
Proof
  rpt strip_tac >> drule_all tuple_store_word_step >> strip_tac >>
  gvs[compile_tuple_store_all_def, comp_return_def] >>
  Cases_on `tr` >> gvs[compile_store_at_loc_def] >>
  drule emit_void_nonterminator_open >> simp[is_terminator_def]
QED

Theorem tuple_store_singleton_open:
  !cenv g ty op st sf.
    tuple_compiler_target cenv g ty /\
    compile_tuple_store_all cenv [ty] [g] [op] st = ((),sf) ==>
    ~block_is_terminated sf
Proof
  rpt gen_tac >> simp[tuple_compiler_target_def] >> strip_tac >> gvs[]
  >- (drule_all tuple_store_singleton_local_open >> simp[])
  >- (drule_all compile_get_target_ptr_toplevel >> strip_tac >>
      irule tuple_store_singleton_storage_open >>
      first_assum (irule_at Any) >> gvs[] >> metis_tac[]) >>
  Cases_on `emit_op ADD [Lit slot; Lit (n2w (struct_field_offset_slots
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))] st` >>
  rename1 `emit_op ADD _ st = (dst, sp)` >>
  drule_all tuple_target_field_pointer >> strip_tac >>
  irule tuple_store_singleton_storage_open >>
      first_assum (irule_at Any) >> gvs[] >> metis_tac[]
QED

Theorem tuple_stores_open:
  !gs cenv tys ops st sf.
    LIST_REL (tuple_compiler_target cenv) gs tys /\
    LENGTH ops = LENGTH tys /\
    compile_tuple_store_all cenv tys gs ops st = ((),sf) ==>
    (gs <> [] \/ ~block_is_terminated st ==> ~block_is_terminated sf)
Proof
  Induct
  >- (rpt gen_tac >> Cases_on `tys` >> simp[] >>
      Cases_on `ops` >>
      simp[compile_tuple_store_all_def, comp_return_def] >> metis_tac[]) >>
  rpt gen_tac >> Cases_on `tys` >> simp[] >> Cases_on `ops` >> simp[] >>
  strip_tac >> rename1 `tuple_compiler_target cenv g ty` >>
  drule tuple_compiler_target_base >> strip_tac >> gvs[] >>
  drule tuple_store_base_cons >> strip_tac >>
  `~block_is_terminated sm` by
    (drule_all tuple_store_singleton_open >> simp[]) >>
  first_x_assum irule >> simp[] >> first_assum (irule_at Any) >> simp[]
QED

Theorem tuple_store_local_singleton_code:
  !cenv id p sz ty op st sf.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME ty /\
    compile_tuple_store_all cenv [ty] [BaseTarget (NameTarget id)] [op] st =
      ((),sf) ==>
    (if is_word_type ty then emit_void MSTORE [Var p;op]
     else compile_store_memory cenv op (Var p) ty ty) st = ((),sf)
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_tuple_store_all _ _ _ _ _ = _` mp_tac >>
  simp[compile_tuple_store_all_def, compile_get_target_ptr_def,
       compile_store_at_loc_def, compile_assign_value_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> simp[]
QED

Theorem tuple_local_copy_exec:
  !ctx func cenv cx es s id p sz pre env entry rest v src ty sa sb sw.
    compile_store_memory cenv src (Var p) ty ty sa = ((), sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME entry.type /\
    value_has_type entry.type v /\ val_wf entry.type v /\
    val_in_memory entry.type v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size entry.type /\
    type_memory_size entry.type + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa ==>
    ?dw u.
      lookup_var p s = SOME dw /\
      run_inst_seq (emitted_insts sa sb) s = OK u /\
      stmt_state_rel ctx func cenv cx
        (es with scopes :=
          pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) u /\
      (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size entry.type <= a ==>
        mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH u.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `?dw. lookup_var p s = SOME dw` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `not_fresh_at sa p` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `eval_operand (Var p) s = SOME dw` by simp[eval_operand_def] >>
  `if is_bytestring_type ty then val_store_size entry.type v <= type_memory_size entry.type
   else type_memory_size entry.type <= type_memory_size entry.type` by
    (simp[] >> metis_tac[val_store_size_le]) >>
  `!x. Var p = Var x ==> not_fresh_at sa x` by simp[] >>
  `(if is_word_type ty then sw = typed_val_to_w256 entry.type v
    else val_in_memory entry.type v (w2n sw) s.vs_memory)` by simp[] >>
  drule_all compile_store_memory_run_frame_with_capacity >> strip_tac >>
  qexistsl [`dw`, `t`] >> simp[] >>
  reverse conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  irule stmt_state_rel_write_local >>
  first_assum (irule_at Any) >> simp[] >>
  reverse conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      fs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  drule_all tuple_store_destination_region >> strip_tac >>
  `t.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  irule immutables_rel_mem_agree >> qexists `s` >> simp[] >>
  reverse conj_tac >- fs[stmt_state_rel_def, state_rel_def] >>
  rpt strip_tac >>
  `regions_disjoint off (type_memory_size tv) (w2n dw) sz` by
    (qpat_x_assum `stmt_state_rel ctx _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def, immutable_alloca_sep_def] >> strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     qpat_x_assum `!id b sz. local_region _ _ _ id b sz ==> _` drule >> simp[]) >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ _ = _` irule >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem tuple_local_copy_code_shape:
  !cenv src dst ty sa sb.
    compile_store_memory cenv src dst ty ty sa = ((),sb) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS)
      (emitted_insts sa sb)
Proof
  rpt gen_tac >>
  Cases_on `is_word_type ty` >>
  Cases_on `is_bytestring_type ty` >>
  simp[compile_store_memory_def] >>
  rpt strip_tac >>
  Cases_on `type_memory_bytes cenv ty` >>
  gvs[compile_copy_memory_def, compile_store_bytestring_def,
      compile_bytestring_copy_len_def, emitHelperTheory.emit_op_def,
      emitHelperTheory.emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  simp[same_blocks_def, emitted_insts_def, DROP_APPEND1,
       mk_inst_def, is_terminator_def]
QED

Theorem tuple_local_copy_path:
  !ctx func cenv cx es s id p sz pre env entry rest v src ty sa sb sw.
    compile_store_memory cenv src (Var p) ty ty sa = ((), sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME entry.type /\
    value_has_type entry.type v /\ val_wf entry.type v /\
    val_in_memory entry.type v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size entry.type /\
    type_memory_size entry.type + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?dw t.
      lookup_var p s = SOME dw /\
      gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx
        (es with scopes :=
          pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size entry.type <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  drule_all tuple_local_copy_exec >> strip_tac >>
  drule tuple_local_copy_code_shape >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
         isPREFIX (emitted_insts sa sb)
           (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     qexists `l` >> REFL_TAC) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  drule_all tuple_run_inst_seq_gas_path >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (fs[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  `LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts +
      LENGTH (emitted_insts sa sb)` by metis_tac[LENGTH_APPEND] >>
  simp[gas_marked_path_def] >> strip_tac >>
  qexists `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[same_blocks_def, stmt_state_rel_inst_idx] >>
  qpat_x_assum `u with <|vs_memory := _; vs_vars := _|> = s` mp_tac >>
  simp[venom_state_component_equality, lookup_var_def] >>
  strip_tac >> fs[lookup_var_def] >> metis_tac[]
QED

Theorem tuple_target_local_head_path:
  !ctx func cenv cx es es' s id ty tv v op st sf.
    compile_tuple_store_all cenv [ty] [BaseTarget (NameTarget id)] [op] st =
      ((),sf) /\
    assign_tuple_targets cx (BaseTarget (NameTarget id)) v es = (INL (),es') /\
    tuple_target_aligned cenv cx (BaseTarget (NameTarget id)) ty tv /\
    tuple_target_layout es.scopes (BaseTarget (NameTarget id)) ty tv v /\
    value_has_type tv v /\ val_wf tv v /\
    (if is_word_type ty then eval_operand op s = SOME (typed_val_to_w256 tv v)
     else ?w. eval_operand op s = SOME w /\
       val_in_memory tv v (w2n w) s.vs_memory /\
       type_memory_size tv + 64 < dimword(:256)) /\
    local_ptrs_reserved cenv st /\ (!x. op = Var x ==> not_fresh_at st x) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_has_code st sf func /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t idp sz entry dw.
      stmt_state_rel ctx func cenv cx es' t /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      lookup_scopes id es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var idp) sz) /\
      lookup_var idp s = SOME dw /\
      (!a len. a + len <= w2n dw \/
         w2n dw + (if is_word_type ty then 32 else type_memory_size tv) <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      gas_marked_path F ctx func s 0 (OK t)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[tuple_target_aligned_local, tuple_target_layout_local] >>
  drule_all tuple_target_local_assignment >> strip_tac >>
  drule_all tuple_store_local_singleton_code >> strip_tac >>
  Cases_on `is_word_type ty`
  >- suspend "word" >>
  gvs[] >> drule_all tuple_local_copy_path >> strip_tac >>
  first_assum (irule_at Any) >> simp[] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Resume tuple_target_local_head_path[word]:
  gvs[] >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `?dw. lookup_var p s = SOME dw` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  drule_all stmt_state_rel_write_local_store >> strip_tac >>
  drule_all emit_mstore_marked_path >> strip_tac >>
  `sf.cs_current_bb = st.cs_current_bb /\
   LENGTH sf.cs_current_insts = SUC (LENGTH st.cs_current_insts)` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `!a len. a + len <= w2n dw \/ w2n dw + 32 <= a ==>
     mem_bytes_at a len (mstore (w2n dw) (typed_val_to_w256 entry.type v) s).vs_memory =
     mem_bytes_at a len s.vs_memory` by
    (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  qexists `mstore (w2n dw) (typed_val_to_w256 entry.type v) s with
              vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[stmt_state_rel_inst_idx, lookup_var_def, mstore_def, LET_THM] >>
  fs[mstore_def, LET_THM]
QED

Finalise tuple_target_local_head_path

Theorem tuple_target_nonlocal_head_path:
  !ctx func cenv cx es es' s g ty tv v op st sf.
    compile_tuple_store_all cenv [ty] [g] [op] st = ((),sf) /\
    assign_tuple_targets cx g v es = (INL (),es') /\
    tuple_target_aligned cenv cx g ty tv /\
    (!id. g <> BaseTarget (NameTarget id)) /\ value_has_type tv v /\
    eval_operand op s = SOME (typed_val_to_w256 tv v) /\
    local_ptrs_reserved cenv st /\ (!x. op = Var x ==> not_fresh_at st x) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_has_code st sf func /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\ t.vs_memory = s.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      gas_marked_path F ctx func s 0 (OK t)
Proof
  rpt gen_tac >> simp[tuple_target_aligned_def] >> strip_tac >> gvs[]
  >- (drule_all tuple_target_toplevel_place >>
      disch_then (qspec_then `es` assume_tac) >>
      drule_all tuple_target_storage_assignment >> strip_tac >>
      drule_all compile_get_target_ptr_toplevel >>
      disch_then (qspec_then `st` assume_tac) >> gvs[] >>
      drule_all tuple_store_word_step >> strip_tac >>
      qpat_x_assum `compile_tuple_store_all _ [_] [_] [_] _ = _` kall_tac >>
      gvs[compile_tuple_store_all_def, comp_return_def] >>
      drule_all encode_value_word_typed >> strip_tac >>
      `eval_operand (Lit (n2w k)) s = SOME (n2w k)` by simp[eval_operand_def] >>
      drule_all tuple_storage_store_head_path >> strip_tac >>
      first_assum (irule_at Any) >> simp[]) >>
  drule_all tuple_target_field_place >>
  disch_then (qspec_then `es` assume_tac) >>
  drule_all tuple_target_storage_assignment >> strip_tac >>
  Cases_on `emit_op ADD [Lit (n2w k); Lit (n2w (struct_field_offset_slots
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))] st` >>
  rename1 `emit_op ADD _ st = (dst,sp)` >>
  drule_all tuple_target_field_pointer >> strip_tac >>
  drule_all tuple_store_word_step >> strip_tac >>
  qpat_x_assum `compile_tuple_store_all _ [_] [_] [_] _ = _` kall_tac >>
  gvs[compile_tuple_store_all_def, comp_return_def] >>
  drule_all encode_value_word_typed >> strip_tac >>
  drule_all tuple_field_storage_head_path >> strip_tac >>
  first_assum (irule_at Any) >> simp[]
QED

Theorem tuple_target_store_head_path:
  !ctx func cenv cx es es' s g ty tv v op st sf.
    compile_tuple_store_all cenv [ty] [g] [op] st = ((),sf) /\
    assign_tuple_targets cx g v es = (INL (),es') /\
    tuple_target_aligned cenv cx g ty tv /\
    tuple_target_layout es.scopes g ty tv v /\
    value_has_type tv v /\ val_wf tv v /\
    (if is_word_type ty then eval_operand op s = SOME (typed_val_to_w256 tv v)
     else ?w. eval_operand op s = SOME w /\
       val_in_memory tv v (w2n w) s.vs_memory /\
       type_memory_size tv + 64 < dimword(:256)) /\
    local_ptrs_reserved cenv st /\ (!x. op = Var x ==> not_fresh_at st x) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_has_code st sf func /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      MAP FDOM es.scopes = MAP FDOM es'.scopes /\
      (!n. OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es'.scopes) =
           OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es.scopes)) /\
      (t.vs_memory = s.vs_memory \/ ?id p sz entry dw.
        g = BaseTarget (NameTarget id) /\
        lookup_scopes id es.scopes = SOME entry /\
        FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
        lookup_var p s = SOME dw /\
        (!a len. a + len <= w2n dw \/
           w2n dw + (if is_word_type ty then 32 else type_memory_size tv) <= a ==>
           mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)) /\
      gas_marked_path F ctx func s 0 (OK t)
Proof
  rpt strip_tac >> drule_all tuple_target_assignment_scope_frame >> strip_tac >>
  Cases_on `?id. g = BaseTarget (NameTarget id)`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      drule_all tuple_target_local_head_path >> strip_tac >>
      first_assum (irule_at Any) >> simp[] >>
      disj2_tac >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  `is_word_type ty` by metis_tac[tuple_target_aligned_nonlocal_word] >>
  gvs[] >> drule_all tuple_target_nonlocal_head_path >> strip_tac >>
  first_assum (irule_at Any) >> simp[]
QED

Theorem tuple_target_store_memory_tail:
  !ctx func cenv cx es s t st scopes' g ty tv tvs v vs b sz addr.
    stmt_state_rel ctx func cenv cx es s /\
    tuple_target_layout es.scopes g ty tv v /\
    local_ptrs_reserved cenv st /\ MAP FDOM es.scopes = MAP FDOM scopes' /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
    (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==> FLOOKUP t.vs_allocas aid = SOME bs) /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
     (?name. local_region cenv es.scopes s name b sz)) /\
    b <= addr /\ addr + type_memory_size_list (tv::tvs) <= b + sz /\
    (is_word_type ty ==> type_memory_size tv = 32) /\
    tuple_in_memory (v::vs) (tv::tvs) addr s.vs_memory /\
    tuple_val_wf (v::vs) (tv::tvs) /\
    (t.vs_memory = s.vs_memory \/ ?id p dsz entry dw.
      g = BaseTarget (NameTarget id) /\
      lookup_scopes id es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) dsz) /\
      lookup_var p s = SOME dw /\
      (!a len. a + len <= w2n dw \/
         w2n dw + (if is_word_type ty then 32 else type_memory_size tv) <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)) ==>
    b <= addr + type_memory_size tv /\
    addr + type_memory_size tv + type_memory_size_list tvs <= b + sz /\
    ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
     (?name. local_region cenv scopes' t name b sz)) /\
    tuple_in_memory vs tvs (addr + type_memory_size tv) t.vs_memory /\
    tuple_val_wf vs tvs
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `t.vs_memory = _ \/ _` strip_assume_tac
  >- suspend "unchanged"
  >> `entry.type = tv` by (gvs[tuple_target_layout_local]) >>
  `((if is_word_type ty then 32 else type_memory_size tv) <= type_memory_size tv) /\
   ((if is_word_type ty then 32 else type_memory_size tv) <= type_memory_size entry.type)` by
    (Cases_on `is_word_type ty` >> gvs[]) >>
  drule_all tuple_store_memory_tail >> simp[]
QED

Resume tuple_target_store_memory_tail[unchanged]:
  `!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
     lookup_var x t = SOME w` by metis_tac[] >>
  drule_all tuple_container_transport >> disch_tac >>
  qpat_x_assum `tuple_in_memory (_::_) _ _ _` mp_tac >>
  simp_tac (srw_ss()) [val_in_memory_def, LET_THM] >> strip_tac >>
  qpat_x_assum `tuple_val_wf (_::_) _` mp_tac >>
  simp_tac (srw_ss()) [val_wf_def] >> strip_tac >>
  simp[type_memory_size_def] >> fs[type_memory_size_def]
QED

Finalise tuple_target_store_memory_tail


Theorem tuple_store_targets_path:
  !gs m tys tvs vs ops addr b sz ctx func cenv cx es es' s st st'.
    compile_tuple_store_all cenv tys gs ops st = ((),st') /\
    assign_tuple_target_list cx gs vs es = (INL (),es') /\
    LENGTH gs = LENGTH tys /\ LENGTH tys = LENGTH tvs /\
    LENGTH tvs = LENGTH vs /\ LENGTH ops = LENGTH vs /\
    (~m ==> EVERY is_word_type tys) /\
    EVERY (\op. ?x. op = Var x) ops /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at st x) ops /\
    local_ptrs_reserved cenv st /\ values_have_types tvs vs /\ tuple_val_wf vs tvs /\
    (!i. i < LENGTH gs ==>
       ?w. eval_operand (EL i ops) s = SOME w /\
         (if is_word_type (EL i tys) then
            w = typed_val_to_w256 (EL i tvs) (EL i vs)
          else w2n w = addr + SUM (MAP type_memory_size (TAKE i tvs)))) /\
    (!i. i < LENGTH gs ==>
       tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
       tuple_target_layout es.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)) /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
       type_memory_size (EL i tvs) + 64 < dimword(:256)) /\
    (m ==> (!i. i < LENGTH tys ==>
          evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
          (is_word_type (EL i tys) ==> type_memory_size (EL i tvs) = 32)) /\
       b <= addr /\ addr + type_memory_size_list tvs <= b + sz /\
       ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
        (?name. local_region cenv es.scopes s name b sz)) /\
       tuple_in_memory vs tvs addr s.vs_memory) /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\ stmt_state_rel ctx func cenv cx es s ==>
    (gs <> [] \/ ~block_is_terminated st ==> ~block_is_terminated st') /\
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
        t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
        (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==> FLOOKUP t.vs_allocas aid = SOME bs) /\
        gas_marked_path F ctx func s 0 (OK t)
Proof
  Induct
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      gvs[compile_tuple_store_all_def, comp_return_def, Once evaluate_def,
          return_def] >> qexists `s` >> simp[gas_marked_path_def] >>
      irule (cj 1 fragGasPathTheory.gas_path_rules) >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `tys` >- fs[] >> Cases_on `tvs` >- fs[] >>
  Cases_on `vs` >- fs[] >> Cases_on `ops` >- fs[] >>
  rename1 `compile_tuple_store_all cenv (ty::tys1) _ (op::ops1) st = _` >>
  rename1 `assign_tuple_target_list cx _ (v::vs1) es = _` >>
  rename1 `tuple_val_wf (v::vs1) (tv::tvs1)` >>
  qpat_x_assum `!m tys tvs vs ops addr b sz ctx func cenv cx es es' s st st'. _`
    (mk_asm "ih") >>
  qpat_assum `!i. i < LENGTH (h::gs) ==> tuple_target_aligned _ _ _ _ _ /\ _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `value_has_type tv v /\ val_wf tv v` by
    (qpat_x_assum `ih :- _` kall_tac >>
     fs[value_has_type_def, val_wf_def]) >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all tuple_target_list_cons_success >> strip_tac >>
  drule_all tuple_target_aligned_compiler >> strip_tac >>
  drule tuple_compiler_target_base >>
  disch_then (qx_choose_then `bt` SUBST_ALL_TAC) >>
  drule tuple_store_base_cons >> strip_tac >>
  suspend "head_setup"
QED

Resume tuple_store_targets_path[head_setup]:
  qpat_assum `compile_tuple_store_all _ [_] [_] [_] _ = _`
    (mp_then Any strip_assume_tac tuple_target_stores_growth) >>
  qpat_assum `compile_tuple_store_all _ tys1 gs ops1 sm = _`
    (mp_then Any strip_assume_tac tuple_target_stores_growth) >>
  `fn_has_code st sm func /\ fn_has_code sm st' func` by
    metis_tac[fn_has_code_split] >>
  `if is_word_type ty then eval_operand op s = SOME (typed_val_to_w256 tv v)
   else ?w. eval_operand op s = SOME w /\
     val_in_memory tv v (w2n w) s.vs_memory /\
     type_memory_size tv + 64 < dimword(:256)` by
    suspend "head_operand" >>
  `!x. op = Var x ==> not_fresh_at st x` by fs[] >>
  drule_all tuple_target_store_head_path >>
  disch_then (qx_choose_then `s1` (map_every assume_tac o CONJUNCTS)) >>
  suspend "tail"
QED

Resume tuple_store_targets_path[head_operand]:
  qpat_x_assum `ih :- _` kall_tac >>
  qpat_assum `!i. i < LENGTH (_::gs) ==> ?w. _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
  disch_then (qx_choose_then `w` (map_every assume_tac o CONJUNCTS)) >>
  Cases_on `is_word_type ty` >- fs[] >>
  `m` by fs[] >>
  `type_memory_size tv + 64 < dimword(:256)` by
    (qpat_x_assum `!i. i < LENGTH (ty::tys1) /\ _ ==> _`
      (qspec_then `0` mp_tac) >> simp[]) >>
  qpat_x_assum `m ==> _` mp_tac >> simp[] >> strip_tac >>
  gns[val_in_memory_def] >> qexists `w` >> simp[]
QED

Resume tuple_store_targets_path[tail]:
  asm_x "ih" drule >> disch_then drule >>
  disch_then (qspecl_then [`m`, `tvs1`, `addr + type_memory_size tv`, `b`,
    `sz`, `ctx`, `func`, `s1`] mp_tac) >>
  (impl_tac >- suspend "tail_premises") >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "compose"
QED

Resume tuple_store_targets_path[tail_premises]:
  rpt conj_tac
  >- fs[] >- fs[] >- fs[] >- fs[] >- fs[] >- fs[]
  >- suspend "tail_fresh"
  >- (irule local_ptrs_reserved_next_var >> qexists `st` >> simp[])
  >- fs[value_has_type_def]
  >- fs[val_wf_def]
  >- suspend "tail_operands"
  >- suspend "tail_layout"
  >- suspend "tail_sizes"
  >- suspend "tail_memory"
  >> asm_rewrite_tac []
QED

Resume tuple_store_targets_path[tail_fresh]:
  fs[EVERY_MEM] >> rpt strip_tac >>
  irule not_fresh_at_mono >> qexists `st` >> simp[] >> metis_tac[]
QED

Resume tuple_store_targets_path[tail_operands]:
  gen_tac >> strip_tac >>
  `LENGTH ops1 = LENGTH gs` by fs[] >>
  drule (Q.SPEC `T` tuple_store_operands_tail) >>
  disch_then (qspecl_then [`st`, `s`, `s1`] mp_tac) >>
  disch_then irule >>
  goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
  qexistsl [`BaseTarget bt`, `op`, `ty`, `v`] >> asm_rewrite_tac []
QED

Resume tuple_store_targets_path[tail_layout]:
  drule tuple_target_layout_transport >> disch_tac >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH (BaseTarget bt::gs) ==> tuple_target_aligned _ _ _ _ _ /\ _`
    (qspec_then `SUC i` mp_tac) >> simp[] >>
  `i < LENGTH vs1` by fs[] >> simp[]
QED

Resume tuple_store_targets_path[tail_sizes]:
  rpt strip_tac >>
  `i < LENGTH vs1` by fs[] >>
  qpat_x_assum `!i. i < LENGTH (ty::tys1) /\ _ ==> _`
    (qspec_then `SUC i` mp_tac) >> simp[]
QED

Resume tuple_store_targets_path[tail_memory]:
  strip_tac >>
  qpat_x_assum `m ==> _` mp_tac >>
  (impl_tac >- asm_rewrite_tac []) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `is_word_type ty ==> type_memory_size tv = 32` by
    (qpat_assum `!i. _ ==> evaluate_type _ _ = _ /\ _`
      (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
     strip_tac >> asm_rewrite_tac []) >>
  drule_all tuple_target_store_memory_tail >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  asm_rewrite_tac [] >>
  gen_tac >> strip_tac >>
  `i < LENGTH vs1` by fs[] >>
  qpat_x_assum `!i. i < LENGTH (ty::tys1) ==> _`
    (qspec_then `SUC i` mp_tac) >> simp[]
QED

Resume tuple_store_targets_path[compose]:
  `~block_is_terminated sm` by
    (drule_all tuple_store_singleton_open >> simp[]) >>
  conj_tac >- simp[] >>
  qpat_x_assum `?t. stmt_state_rel _ _ _ _ _ t /\ _`
    (qx_choose_then `sf` (map_every assume_tac o CONJUNCTS)) >>
  qexists `sf` >> asm_rewrite_tac [] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by
        (irule not_fresh_at_mono >> qexists `st` >> simp[]) >>
      metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  irule (gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
  first_assum (irule_at Any) >> simp[]
QED

Finalise tuple_store_targets_path
