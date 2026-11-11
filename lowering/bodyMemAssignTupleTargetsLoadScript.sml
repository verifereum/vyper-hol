(* Memory checks for the actual tuple-element loads. *)
Theory bodyMemAssignTupleTargetsLoad
Ancestors
  bodyMemAssignTupleTargetsFacts tupleLoadProps stmtSimReturn
  fragExecMem instMemFrontier context emitHelper emitHelperProps
  venomExecSemantics venomState venomInst compileEnv loweringStateRelDefs exprLoweringProps
  list rich_list words unitTransformDefs memSafeRun contextCodegenRel codegenRel
  stmtLowering freshWrites tupleTypedLoad tupleMemoryLayout valueEncodingProofs
  bodyDeclMemoryCounted bodyDeclMemoryCore loweringPosts bodyMemoryDefs allocaHistory
  tupleStageProps valueTypingMemoryProps valueEncoding valueEncodingDefs vyperTyping gasCount fragGasPathMem
Libs
  monadsyntax

Theorem tuple_elem_load_head_mem_ok:
  !bop off sa pv sm v sb s w load.
    emit_op ADD [bop; Lit off] sa = (pv,sm) /\
    compile_load_memory pv load sm = (v,sb) /\
    eval_operand bop s = SOME w /\
    (load ==> w2n (w + off) + 32 <= s.vs_alloca_next) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `load` >>
  gvs[compile_load_memory_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def,
      comp_return_def] >>
  simp[emitted_insts_def, DROP_APPEND1, mk_inst_def,
       run_inst_seq_mem_ok_def, inst_mem_below_frontier_def,
       inst_dload_in_section_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[venomInstTheory.instruction_accessors,
                   venomInstTheory.instruction_accfupds,
                   combinTheory.K_THM, venomInstTheory.opcode_case_def] >>
  simp[exec_pure2_def, eval_operand_def,
       bind_outputs_def, lookup_var_update_var] >>
  simp[inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       eval_operand_def, lookup_var_update_var, update_var_def] >>
  simp[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  CASE_TAC >> simp[]
QED

Theorem compile_tuple_load_all_mem_ok:
  !tys cenv bop off sa elems sb s w.
    compile_tuple_load_all cenv bop tys off sa = (elems,sb) /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    eval_operand bop s = SOME w /\
    (!i. i < LENGTH tys /\ is_word_type (EL i tys) ==>
      w2n (w + n2w (off + SUM
        (MAP (type_memory_bytes cenv) (TAKE i tys)))) + 32 <=
      s.vs_alloca_next) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Induct
  >- (simp[compile_tuple_load_all_def, comp_return_def, emitted_insts_def,
           run_inst_seq_mem_ok_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_tuple_load_all _ _ _ _ _ = _` mp_tac >>
  simp[compile_tuple_load_all_def, comp_bind_def, LET_THM] >>
  rename1 `type_memory_bytes cenv ht` >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD _ sa = (pv,sm)` >>
  rename1 `compile_load_memory _ _ sm = (v,sh)` >>
  rename1 `compile_tuple_load_all _ _ _ _ sh = (rest,sf)` >>
  `is_word_type ht ==> w2n (w + n2w off) + 32 <= s.vs_alloca_next` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  drule_all tuple_elem_load_head_mem_ok >> strip_tac >>
  drule_all tuple_elem_load_head_run >> strip_tac >> gvs[] >>
  `sa.cs_next_var <= sh.cs_next_var` by simp[] >>
  `(!x. bop = Var x ==> not_fresh_at sh x) /\
   eval_operand bop (s with vs_vars := vs) = SOME w` by
    (conj_tac >- metis_tac[not_fresh_at_mono] >>
     `eval_operand bop (s with vs_vars := vs) = eval_operand bop s` by
       (irule eval_operand_old_vars >> simp[] >> qexists_tac `sa` >> simp[]) >>
     simp[]) >>
  qpat_x_assum `!cenv bop off sa elems sb s w. _`
    (drule_at (Pos hd)) >>
  disch_then (qspec_then `s with vs_vars := vs` mp_tac) >>
  simp[] >> impl_tac
  >- (rpt strip_tac >>
      `off + (type_memory_bytes cenv ht +
         SUM (MAP (type_memory_bytes cenv) (TAKE i tys))) =
       off + (SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) +
         type_memory_bytes cenv ht)` by decide_tac >>
      first_x_assum (qspec_then `SUC i` mp_tac) >>
      pure_rewrite_tac[TAKE, MAP, SUM, EL, HD, TL,
                       arithmeticTheory.LESS_MONO_EQ] >>
      asm_rewrite_tac[]) >>
  strip_tac >>
  drule_all compile_tuple_load_all_run >> strip_tac >>
  `emitted_insts sa sf = emitted_insts sa sh ++ emitted_insts sh sf` by
    metis_tac[emitted_insts_append] >>
  simp[] >> irule run_inst_seq_mem_ok_append >> simp[] >>
  rpt strip_tac >> gvs[]
QED

Theorem compile_tuple_load_all_typed_mem_ok:
  !tys tvs tenv cenv bop sa elems sb s w.
    compile_tuple_load_all cenv bop tys 0 sa = (elems,sb) /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    eval_operand bop s = SOME w /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
    w2n w + type_memory_size_list tvs < dimword (:256) /\
    w2n w + type_memory_size_list tvs <= s.vs_alloca_next ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  rpt gen_tac >> strip_tac >> irule compile_tuple_load_all_mem_ok >>
  simp[] >> qexistsl_tac [`bop`, `cenv`, `elems`, `0`, `tys`, `w`] >>
  simp[] >> rpt strip_tac >>
  `i < LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >>
  `evaluate_type tenv (EL i tys) = SOME (EL i tvs)` by
    fs[LIST_REL_EL_EQN] >>
  `type_memory_size (EL i tvs) = 32` by metis_tac[word_type_sizes] >>
  drule tuple_prefix_sizes >> disch_then (qspec_then `i` assume_tac) >>
  drule tuple_element_interval >> strip_tac >>
  `w2n w + SUM (MAP type_memory_size (TAKE i tvs)) < dimword (:256)` by
    (fs[type_memory_size_list_sum] >> decide_tac) >>
  `w2n (w + n2w (SUM (MAP (type_memory_bytes cenv) (TAKE i tys)))) =
    w2n w + SUM (MAP type_memory_size (TAKE i tvs))` by
    (Cases_on `w` >> gvs[word_add_n2w]) >>
  fs[type_memory_size_list_sum] >> decide_tac
QED

Theorem compile_tuple_load_all_typed_path_mem:
  !tys tvs vals tenv cenv bop sa elems sb s w ctx func cx es d.
    compile_tuple_load_all cenv bop tys 0 sa = (elems,sb) /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    eval_operand bop s = SOME w /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
    values_have_types tvs vals /\ tuple_in_memory vals tvs (w2n w) s.vs_memory /\
    w2n w + type_memory_size_list tvs < dimword (:256) /\
    w2n w + type_memory_size_list tvs <= s.vs_alloca_next /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    stmt_state_rel ctx func cenv cx es s /\
    local_ptrs_reserved cenv sa /\ alloca_history func s /\
    return_buf_frame d cenv sa s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    LENGTH elems = LENGTH tys /\ EVERY (\op. ?x. op = Var x) elems /\
    (!x. MEM (Var x) elems ==> not_fresh_at sb x) /\
    local_ptrs_reserved cenv sb /\
    ?t. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      stmt_state_rel ctx func cenv cx es t /\ alloca_history func t /\
      return_buf_frame d cenv sb t /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!name b sz. local_region cenv es.scopes t name b sz =
                   local_region cenv es.scopes s name b sz) /\
      (!i. i < LENGTH tys ==> ?v. eval_operand (EL i elems) t = SOME v /\
        if is_word_type (EL i tys) then
          v = typed_val_to_w256 (EL i tvs) (EL i vals)
        else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_tuple_load_all_typed_mem_ok >> strip_tac >>
  drule_all compile_tuple_load_all_typed_run >> strip_tac >> gvs[] >>
  drule_all tuple_load_vars_frame >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all body_decl_cursor_path >> strip_tac >> simp[] >>
  qexists_tac `(s with vs_vars := V) with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx, lookup_var_def] >>
  conj_tac
  >- (`alloca_inv s` by fs[stmt_state_rel_def] >>
      drule_all body_store_memory_history >> simp[]) >>
  conj_tac
  >- (irule return_buf_frame_frame >>
      qexistsl_tac [`cenv`, `s`, `sa`] >> simp[lookup_var_def] >>
      fs[lookup_var_def]) >>
  fs[local_region_def, lookup_var_def]
QED

(* Counted counterpart of tupleStageProps.optional_tuple_stage_run. *)
Theorem optional_tuple_stage_path_mem:
  !ctx func cenv cx es flag tys tvs vs se sa sb staged op s sw d.
    (if flag then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT tys)))];
          comp_return buf.buf_operand od
     else comp_return op) sa = (staged,sb) /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
    expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op s /\
    expr_val_at cenv cx (TupleT tys) se sa es (ArrayV (TupleV vs)) op s /\
    eval_operand op s = SOME sw /\
    0 < type_memory_size_list tvs /\
    type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs /\
    (flag ==> type_memory_size_list tvs < dimword (:256)) /\
    fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    alloca_history func s /\ return_buf_frame d cenv sa s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    tuple_val_wf vs tvs /\ values_have_types tvs vs /\
    ?t w. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand staged t = SOME w /\
      tuple_in_memory vs tvs (w2n w) t.vs_memory /\
      stmt_state_rel ctx func cenv cx es t /\ alloca_history func t /\
      return_buf_frame d cenv sb t /\
      s.vs_alloca_next <= t.vs_alloca_next /\
      w2n w + type_memory_size_list tvs <= t.vs_alloca_next /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!x. staged = Var x ==> not_fresh_at sb x) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (?b sz. b <= w2n w /\
        w2n w + type_memory_size_list tvs <= b + sz /\
        b + sz <= t.vs_alloca_next /\
        ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
         (?name. local_region cenv es.scopes t name b sz)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all expr_tuple_memory_owned >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`b`, `sz`] (MAP_EVERY assume_tac o CONJUNCTS)))) >>
  `values_have_types tvs vs` by gvs[value_has_type_def] >>
  `b + sz <= s.vs_alloca_next` by
    (irule tuple_container_frontier >> metis_tac[]) >>
  `w2n sw + type_memory_size_list tvs <= s.vs_alloca_next` by decide_tac >>
  simp[] >> Cases_on `flag`
  >- (qpat_x_assum `(?aid. _) \/ (?name. _)` kall_tac >> gvs[] >>
      `val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n sw) s.vs_memory /\
       val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
       val_footprint (TupleTV tvs) (ArrayV (TupleV vs)) <= type_memory_size_list tvs` by
        simp[val_in_memory_def, val_wf_def, val_footprint_def, type_memory_size_def] >>
      `w2n sw + type_memory_size_list tvs <= s.vs_alloca_next` by decide_tac >>
      drule_all tuple_stage_copy_path_mem >> strip_tac >>
      qexistsl_tac [`t`, `w`] >> simp[] >>
      conj_tac >- fs[val_in_memory_def] >>
      conj_tac
      >- (drule_all tuple_stage_copy_parts >> strip_tac >> gvs[]) >>
      qexistsl_tac [`w2n w`, `type_memory_size_list tvs`] >> simp[] >>
      metis_tac[]) >>
  gvs[comp_return_def] >> qexistsl_tac [`s`, `sw`] >> simp[] >>
  simp[cj 1 gas_path_mem_rules] >>
  qexistsl_tac [`b`, `sz`] >> simp[] >> metis_tac[]
QED
