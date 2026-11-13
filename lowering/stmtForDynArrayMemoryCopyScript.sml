(* Memory certificates for the header-shifted dynamic array copy prefix. *)
Theory stmtForDynArrayMemoryCopy
Ancestors
  stmtForArrayMemoryCopy stmtForArrayMemoryRounds whitelistForIterDynLoop
  stmtSimForArray stmtSimForArrayLoop stmtSimProps exprSimProps
  stmtLowering emitHelper emitHelperProps exprLoweringProps fragExecMem
  fragGasPathMem fragGasMode stmtForArrayMemoryBodyEntry
  allocaHistory venomInstProofs venomExecSemantics
  venomState compileEnv loweringStateRelDefs words arithmetic list
  venomInst memSafeRun instMemFrontier

Theorem dynarray_body_prefix_mem_ok:
  compile_iter_elem_copy ce (Var ep) (Var p) stride LocMemory F ty ty sa = ((),sb) /\
  (!x. x = ep \/ x = p ==> not_fresh_at sa x) /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_arr_base s = SOME arr_base /\
  (!x. saved_arr_base = Var x ==> x <> ov /\ x <> tot) /\ ov <> tot /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> tot /\ p <> ep /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  stride = type_memory_size tv /\ type_memory_bytes ce ty = stride /\
  val_in_memory tv v (w2n arr_base + 32 + k * stride) s.vs_memory /\
  w2n arr_base + 32 + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  w2n arr_base + 32 + k * stride + stride <= s.vs_alloca_next /\
  w2n dst + stride <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
      mk_inst j4 ADD [Lit 32w; Var ov] [tot];
      mk_inst j5 ADD [saved_arr_base; Var tot] [ep]] ++ emitted_insts sa sb) s
Proof
  strip_tac >> irule run_inst_seq_mem_ok_append >>
  reverse conj_tac
  >- (irule run_inst_seq_mem_ok_every >>
      simp[mk_inst_def, inst_dload_in_section_def] >>
      rpt conj_tac >> gen_tac >> irule below_frontier_no_ranges >> simp[]) >>
  drule_all dynarray_address_prefix_run >> simp[] >> rpt strip_tac >> gvs[] >>
  irule array_iter_copy_mem_ok >>
  goal_assum (drule_at (Pat `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
  qexistsl_tac [`dst`, `n2w (w2n arr_base + 32 + k * type_memory_size tv)`, `v`] >>
  simp[eval_operand_def, lookup_var_update_var, update_var_def, w2n_n2w] >>
  metis_tac[]
QED

Theorem dynarray_round_copy_entry_mem:
  !ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
   idx saved_base arr_base k stride ov tot ep j3 j4 j5 bb.
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arr_base + 32 + k * stride) s.vs_memory /\
  w2n arr_base + 32 + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  w2n arr_base + 32 + k * stride + stride <= s.vs_alloca_next /\
  w2n dst + stride <= s.vs_alloca_next /\
  stmt_state_rel ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes tot /\
  not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_base s = SOME arr_base /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> tot /\ p <> ep /\ ov <> tot /\
  (!x. saved_base = Var x ==> x <> ov /\ x <> tot) /\
  not_fresh_at sa ep /\ not_fresh_at sa p /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  sb0.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [Lit 32w; Var ov] [tot];
     mk_inst j5 ADD [saved_base; Var tot] [ep]] ++ emitted_insts sa sb0 /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  alloca_history func s /\ alloca_inv s ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\ alloca_history func t /\
    stmt_state_rel ctx func bc cx
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
          :: es.scopes) t /\
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = LENGTH sb0.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
      lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dynarray_for_body_entry_run >>
  disch_then (qspecl_then [`j3`, `j4`, `j5`] strip_assume_tac) >>
  `run_inst_seq_mem_ok sb0.cs_current_insts s` by
    (`!x. x = ep \/ x = p ==> not_fresh_at sa x` by metis_tac[] >>
     drule_all dynarray_body_prefix_mem_ok >>
     disch_then (qspecl_then [`j5`, `j4`, `j3`] mp_tac) >> simp[]) >>
  `run_inst_seq sb0.cs_current_insts s = OK t` by gvs[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    sb0.cs_current_insts` by simp[mk_inst_def, is_terminator_def] >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb0)` by
    (irule array_iter_copy_no_gas >> goal_assum (drule_at Any)) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) sb0.cs_current_insts) = 0` by
    (simp[mk_inst_def] >> fs[EVERY_FILTER, FILTER_EQ_NIL, EVERY_MEM]) >>
  `isPREFIX sb0.cs_current_insts (DROP s.vs_inst_idx bb.bb_instructions)`
    by (qpat_assum `s.vs_inst_idx = 0` (fn th => rewrite_tac[th, DROP_0]) >>
        first_assum ACCEPT_TAC) >>
  drule_all array_prefix_counted_history >> simp[] >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb0.cs_current_insts` >>
  simp[gas_marked_path_def, stmt_state_rel_inst_idx] >>
  fs[venom_state_component_equality, lookup_var_def]
QED
