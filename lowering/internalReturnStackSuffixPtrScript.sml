(* Counted stack-return suffix, independent of source expression evaluation. *)
Theory internalReturnStackSuffixPtr
Ancestors internalReturnStackPtr internalReturnCountedPtr stmtLowering
  exprLoweringProps compileEnv fragGasPathPtr stateFrame

Theorem internal_return_stack_suffix_path_ptr:
  compile_internal_return_from_env ce ty sty op (Var rpc) sa = ((),sb) /\
  (!off sz. ce.ce_return_buf <> SOME (MemLoc off sz)) /\
  0 < ce.ce_returns_count /\
  ets = (case ty of TupleT ts => ts | StructT ns =>
    MAP (FST o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string ns))
    | _ => []) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa rpc /\ lookup_var rpc s = SOME pc /\
  op_taint tn (Var rpc) = {} /\
  (ets = [] ==> eval_operand op s = SOME w /\ op_taint tn op = {}) /\
  (ets <> [] ==> op = Var src /\ not_fresh_at sa src /\
    lookup_var src s = SOME bw /\
    (!i. i < LENGTH ets ==>
      ptr_covers G tn src s
        (SUM (MAP (type_memory_bytes ce) (TAKE i ets)) + 32) /\
      w2n bw + SUM (MAP (type_memory_bytes ce) (TAKE i ets)) + 32 <= dimword (:256) /\
      (!j. w2n bw + SUM (MAP (type_memory_bytes ce) (TAKE i ets)) <= j /\
        j < w2n bw + SUM (MAP (type_memory_bytes ce) (TAKE i ets)) + 32 ==>
        j NOTIN tn.t_mem))) ==>
  ?t H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm
      (IntRet <| iret_values := (if ets = [] then [w]
        else tuple_words ce bw ets 0 s.vs_memory); iret_adopt_fmp := NONE |> t) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_internal_return ce (SOME op) (Var rpc) ce.ce_returns_count
    ty sty ets NONE sa = ((),sb)` by
    (qpat_x_assum `compile_internal_return_from_env _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `ce.ce_return_buf` >>
     simp[compile_internal_return_from_env_def, comp_bind_def, comp_return_def] >>
     TRY (rename1 `ce.ce_return_buf = SOME loc` >> Cases_on `loc`) >>
     fs[compile_internal_return_def, comp_bind_def, comp_return_def] >>
     Cases_on `ty` >> fs[]) >>
  qpat_x_assum `ets = _` kall_tac >>
  Cases_on `ets = []`
  >- (gns[compile_internal_return_def] >>
      qexistsl_tac [`s`, `G`, `tn`] >> simp[] >>
      irule emit_ret_values_path_ptr >>
      simp[ptrDisciplineTheory.allocas_from_def] >>
      qexistsl_tac [`[op]`, `pc`, `rpc`, `sa`, `sb`] >>
      simp[ptrDisciplineTheory.allocas_from_def, venomStateTheory.eval_operands_def]) >>
  gns[compile_internal_return_def, comp_bind_def] >>
  qpat_x_assum `(\(elems,cs'). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_load_tuple_elements ce (Var src) ets 0 sa = (elems,sm)` >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[stmtSimReturnTheory.compile_load_tuple_elements_extends,
      fragExecTheory.cs_extends_emit_inst] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  drule compile_load_tuple_elements_path_ptr >>
  disch_then (qspecl_then [`s`, `bw`, `G`, `tn`, `D`, `ctx`, `func`, `PG`] mp_tac) >>
  (impl_tac >- (simp[] >> gvs[] >> metis_tac[])) >> strip_tac >>
  rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK t)` >>
  `lookup_var rpc t = SOME pc /\ op_taint tm (Var rpc) = {}` by metis_tac[] >>
  `gas_path_ptr D 0 ctx func PG H tm t 0 H tm
    (IntRet <| iret_values := tuple_words ce bw ets 0 s.vs_memory;
               iret_adopt_fmp := NONE |> t)` by
    (irule emit_ret_values_path_ptr >>
     simp[ptrDisciplineTheory.allocas_from_def] >>
     qexistsl_tac [`elems`, `pc`, `rpc`, `sm`, `sb`] >> simp[]) >>
  qexistsl_tac [`t`, `H`, `tm`] >> simp[] >>
  conj_tac >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_0] >>
  gvs[stateFrameTheory.state_frame_def, venomStateTheory.venom_state_component_equality]
QED
