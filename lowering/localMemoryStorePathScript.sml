(* Counted paths into memory-backed locals: storage into an existing
   local, and a fresh allocation filled by a memory copy. *)
Theory localMemoryStorePath
Ancestors
  stmtSimProps exprSimProps stmtSimDefs exprSimDefs loweringPosts
  list rich_list finite_map pred_set fragExec localPtrsProps loweringSlice
  stmtSimDeclStore stmtSimDecl stmtSimAssignStore stmtSimAssign
  valueCopy valueCopySource valueCopyBytes exprOperandVar freshWrites
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding vyperInterpreter vyperState vyperValue vyperLookup
  vyperExprNoControl venomExecSemantics venomExecProofs venomInst venomState
  fragGasSeq fragGasMode context exprSimBufferStore stmtSimDeclPath
Libs
  monadsyntax

Theorem local_copy_immutables:
  stmt_state_rel ctx func cenv cx es s /\
  local_region cenv es.scopes s id b sz /\ n <= sz /\
  t.vs_data_section = s.vs_data_section /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!a len. a + len <= b \/ b + n <= a ==>
     mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) ==>
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t
Proof
  strip_tac >> irule immutables_rel_mem_agree >> qexists_tac `s` >>
  simp[] >> reverse conj_tac >- fs[stmt_state_rel_def, state_rel_def] >>
  rpt strip_tac >>
  `regions_disjoint off (type_memory_size tv) b sz` by
    (qpat_x_assum `stmt_state_rel ctx _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def, immutable_alloca_sep_def] >> strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     qpat_x_assum `!id b sz. local_region _ _ _ id b sz ==> _` drule >> simp[]) >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ _ = _` irule >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem bytestring_copy_len_no_gas[local]:
  compile_bytestring_copy_len src sa = (out,sb) ==>
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  simp_tac bool_ss [compile_bytestring_copy_len_def, comp_bind_def, LET_THM] >>
  ntac 3 (pairarg_tac >> gvs[]) >>
  strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  gvs[emitted_insts_def, DROP_APPEND1, mk_inst_def]
QED

Theorem compile_store_memory_no_gas:
  compile_store_memory cenv src dst ty sty sa = ((),sb) /\
  ~is_word_type ty /\
  (ty = sty \/ is_bytestring_type ty /\ is_bytestring_type sty) ==>
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_bytestring_type ty`
  >- (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
      asm_rewrite_tac [compile_store_memory_def, compile_store_bytestring_def] >>
      simp_tac bool_ss [comp_bind_def, LET_THM] >>
      pairarg_tac >> gvs[] >> strip_tac >>
      drule bytestring_copy_len_no_gas >> strip_tac >>
      drule buffer_copy_len_shape >> strip_tac >>
      drule emitted_insts_emit_void >> strip_tac >>
      `emitted_insts sa sb = emitted_insts sa cs' ++ emitted_insts cs' sb` by
        (irule emitted_insts_append >> simp[]) >>
      simp[FILTER_APPEND, mk_inst_def]) >>
  `ty = sty` by metis_tac[] >> gvs[] >>
  qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_store_memory_def] >>
  Cases_on `type_memory_bytes cenv sty`
  >- simp[compile_copy_memory_def, comp_return_def, emitted_insts_def] >>
  simp[compile_copy_memory_def] >> strip_tac >>
  drule emitted_insts_emit_void >> simp[mk_inst_def]
QED

Theorem local_memory_store_path:
  !ctx func cenv cx es s id p sz pre env entry rest v src ty sa sb sw tyv sty stv.
    compile_store_memory cenv src (Var p) ty sty sa = ((), sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    entry.type = tyv /\ value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    (ty = sty \/ is_bytestring_type ty /\ is_bytestring_type sty) /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?dw t. lookup_var p s = SOME dw /\
        stmt_state_rel ctx func cenv cx
          (es with scopes :=
             pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) ::
             rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        (!a len. a + len <= w2n dw \/
           w2n dw + MIN (type_memory_size stv) (type_memory_size tyv) <= a ==>
           mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
        alloca_frame cenv es sa s cenv
          (es with scopes :=
             pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
        gas_marked_path F ctx func s 0 (OK t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `?w. lookup_var p s = SOME w` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     metis_tac[]) >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  `~is_word_type sty` by metis_tac[is_bytestring_word_type] >>
  `if is_word_type sty then sw = typed_val_to_w256 stv v
   else val_in_memory stv v (w2n sw) s.vs_memory` by simp[] >>
  `!x. Var p = Var x ==> not_fresh_at sa x` by simp[] >>
  drule_all compile_store_memory_run_source_bound_with_capacity >> strip_tac >>
  `!a len. a + len <= w2n w \/ w2n w + type_memory_size tyv <= a ==>
     mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory` by
    (rpt strip_tac >> first_x_assum irule >> simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (drule_all compile_store_memory_no_gas >> simp[]) >>
  qpat_x_assum `ty = sty \/ _` kall_tac >>
  `!q. ~not_local_ptr cenv es.scopes q ==> lookup_var q t = lookup_var q s` by
    (rpt strip_tac >> first_x_assum irule >>
     fs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  qpat_x_assum `entry.type = tyv` (SUBST_ALL_TAC o SYM) >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel ctx func cenv cx es1` >>
  `type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  `local_region cenv es.scopes s id (w2n w) sz` by simp[local_region_def] >>
  `t.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp_tac (srw_ss()) [venom_state_component_equality]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (irule local_copy_immutables >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     qexists_tac `type_memory_size entry.type` >> simp[] >>
     rpt strip_tac >> qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ _ = _` irule >>
     decide_tac) >>
  `stmt_state_rel ctx func cenv cx es1 t` by
    (drule_all stmt_state_rel_write_local >> simp[Abbr `es1`]) >>
  `t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
       DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
   s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND, same_blocks_def] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  `gas_path ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_all tuple_run_inst_seq_gas_path >> simp[]) >>
  `MAP FDOM es1.scopes = MAP FDOM es.scopes` by
    (drule find_containing_scope_structure >> strip_tac >>
     simp[Abbr `es1`, FDOM_FUPDATE] >>
     gvs[FLOOKUP_DEF, pred_setTheory.ABSORPTION_RWT]) >>
  `alloca_frame cenv es sa s cenv es1 t` by
    (irule alloca_frame_local_store >>
     simp[] >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`w2n w`, `es`, `id`, `type_memory_size entry.type`, `s`, `sz`] >>
     simp[alloca_frame_def] >>
     rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  qexistsl_tac [`w`, `t with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  simp[stmt_state_rel_inst_idx, lookup_var_def, gas_marked_path_def] >>
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
  simp[venom_state_component_equality] >>
  strip_tac >> gvs[same_blocks_def, lookup_var_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule alloca_frame_same_state >> goal_assum (drule_at Any) >> simp[]
QED

Theorem alloc_copy_memory_framed_path:
  !ctx func cenv cx es sa sm sb s0 p src sz sw tv v.
    emit_inst ALLOCA [Lit (n2w sz)] [p] sa = ((), sm) /\
    emit_void MCOPY [Var p; src; Lit (n2w sz)] sm = ((), sb) /\
    stmt_state_rel ctx func cenv cx es s0 /\ fn_inst_ids_distinct func /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
    not_local_ptr cenv es.scopes p /\ sz < dimword (:256) /\
    src <> Var p /\ eval_operand src s0 = SOME sw /\
    val_in_memory tv v (w2n sw) s0.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= sz /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?s2 w. lookup_var p s2 = SOME w /\
      FLOOKUP s2.vs_allocas sa.cs_next_id = SOME (w2n w, sz) /\
      stmt_state_rel ctx func cenv cx es s2 /\
      val_in_memory tv v (w2n w) s2.vs_memory /\
      (!ad len. ad + len <= w2n w \/ w2n w + sz <= ad ==>
         mem_bytes_at ad len s2.vs_memory = mem_bytes_at ad len s0.vs_memory) /\
      (!x. x <> p ==> lookup_var x s2 = lookup_var x s0) /\
      (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                   FLOOKUP s2.vs_allocas aid = SOME entry) /\
      ~s2.vs_halted /\ s2.vs_current_bb = sb.cs_current_bb /\
      s2.vs_inst_idx = LENGTH sb.cs_current_insts /\
      gas_marked_path F ctx func s0 0 (OK s2)
Proof
  rpt strip_tac >> drule_all annassign_alloca_operand_framed_path >>
  disch_then (qx_choosel_then [`s1`, `w`] strip_assume_tac) >>
  `eval_operand src s1 = SOME sw` by simp[] >>
  `val_in_memory tv v (w2n sw) s1.vs_memory` by simp[] >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
   inst.inst_id = sa.cs_next_id` by simp[Abbr `inst`, mk_inst_def] >>
  `stmt_state_rel ctx func cenv cx es (mcopy (w2n w) (w2n sw) sz s1)` by
    (irule stmt_state_rel_mcopy_alloca >> simp[] >>
     qexistsl_tac [`sz`, `inst`, `p`] >> simp[]) >>
  `val_in_memory tv v (w2n w) (mcopy (w2n w) (w2n sw) sz s1).vs_memory` by
    (irule mcopy_val_in_memory >> simp[]) >>
  `gas_marked_path F ctx func s1 0
     (OK (mcopy (w2n w) (w2n sw) sz s1 with vs_inst_idx := SUC s1.vs_inst_idx))` by
    (irule emit_inst_zero_marked_path >> simp[] >>
     qexistsl_tac [`[Var p; src; Lit (n2w sz)]`, `MCOPY`, `[]`, `sm`, `sb`] >>
     gvs[emit_void_def, emit_inst_def, step_inst_base_def, mk_inst_def, eval_operand_def,
         is_terminator_def, wordsTheory.w2n_n2w]) >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sm.cs_current_insts)` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def, comp_return_def, emit_def] >>
  `gas_marked_path F ctx func s0 0
     (OK (mcopy (w2n w) (w2n sw) sz s1 with vs_inst_idx := SUC s1.vs_inst_idx))` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `!ad len. ad + len <= w2n w \/ w2n w + sz <= ad ==>
     mem_bytes_at ad len (mcopy (w2n w) (w2n sw) sz s1).vs_memory =
     mem_bytes_at ad len s0.vs_memory` by
    (rpt strip_tac >> simp[valueEncodingPropsTheory.mcopy_mem_bytes_at_disjoint]) >>
  qexistsl_tac [`mcopy (w2n w) (w2n sw) sz s1 with vs_inst_idx := SUC s1.vs_inst_idx`, `w`] >>
  simp[stmt_state_rel_inst_idx] >>
  gvs[mcopy_def, write_memory_with_expansion_def, LET_THM, lookup_var_def] >>
  first_assum ACCEPT_TAC
QED

Theorem alloca_frame_owned_copy:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
         lookup_var x t = SOME w) /\
  venomMemDefs$allocas_non_overlapping t /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
               FLOOKUP t.vs_allocas aid = SOME entry) /\
  FLOOKUP t.vs_allocas bid = SOME (b,z) /\ sa.cs_next_id <= bid /\
  (!ad len. ad + len <= b \/ b + z <= ad ==>
     mem_bytes_at ad len t.vs_memory = mem_bytes_at ad len s.vs_memory) ==>
  alloca_frame cenv es sa s cenv es t
Proof
  strip_tac >> irule alloca_frame_of_mem_frame >>
  goal_assum (drule_at Any) >> simp[] >>
  reverse conj_tac >- metis_tac[] >> rpt strip_tac >>
  first_x_assum irule >>
  `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
  `aid <> bid` by decide_tac >>
  fs[venomMemDefsTheory.allocas_non_overlapping_def] >> metis_tac[]
QED
