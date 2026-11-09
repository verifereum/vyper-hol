(* The fixed-array element prefix keeps disjoint memory at its own endpoint. *)
Theory bodyIntCallFamStmtForArrayFrame
Ancestors
  stmtSimForArray stmtSimForArrayLoop exprLoweringProps emitHelperProps
  compileEnv venomState venomExecSemantics venomInst finite_map words
  valueEncoding vyperValue stmtSimProps fragGasSeq fragGasMode fragGasPath
  list rich_list

Theorem intcall_array_prefix_frame:
  compile_iter_elem_copy ce (Var ep) (Var p) stride LocMemory F et et sa = ((),sb) /\
  stride = type_memory_size tv /\ type_memory_bytes ce et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arrbase + k * stride) s.vs_memory /\
  w2n arrbase + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved s = SOME arrbase /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> ep /\
  (!x. saved = Var x ==> x <> ov) /\
  not_fresh_at sa ep /\ not_fresh_at sa p ==>
  ?t. run_inst_seq
       ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
         mk_inst j4 ADD [saved; Var ov] [ep]] ++ emitted_insts sa sb) s = OK t /\
      (!a len. a + len <= w2n dst \/ w2n dst + stride <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  strip_tac >>
  qabbrev_tac `s2 = update_var ep (n2w (w2n arrbase + k * stride))
                       (update_var ov (n2w (k * stride)) s)` >>
  `run_inst_seq [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
                  mk_inst j4 ADD [saved; Var ov] [ep]] s = OK s2` by
    (simp[Abbr `s2`] >> irule array_address_prefix_run >> gvs[]) >>
  `eval_operand (Var ep) s2 = SOME (n2w (w2n arrbase + k * stride)) /\
   eval_operand (Var p) s2 = SOME dst /\ s2.vs_memory = s.vs_memory` by
    (fs[Abbr `s2`, eval_operand_def, lookup_var_def,
        update_var_def, FLOOKUP_UPDATE]) >>
  drule array_iter_copy_run >>
  disch_then (qspecl_then [`s2`, `tenv`, `tv`, `v`,
                           `n2w (w2n arrbase + k * stride)`, `dst`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  qexists_tac `t` >> conj_tac
  >- (qpat_x_assum `run_inst_seq [_; _] _ = _`
        (mp_then Any mp_tac run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts sa sb` mp_tac) >> gvs[]) >>
  gvs[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem intcall_array_body_entry_run_frame:
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arr_base + k * stride) s.vs_memory /\
  w2n arr_base + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_base s = SOME arr_base /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> ep /\
  (!x. saved_base = Var x ==> x <> ov) /\ not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz ==>
  ?t. run_inst_seq
    ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
      mk_inst j4 ADD [saved_base; Var ov] [ep]] ++ emitted_insts sa sb0) s = OK t /\
    stmt_state_rel ctx func bc cx
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) t /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
      lookup_var x t = lookup_var x s) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb0) /\
    (!a len. a + len <= w2n dst \/ w2n dst + stride <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  strip_tac >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  drule_all array_for_body_entry_run >>
  disch_then (qspecl_then [`j3`, `j4`] strip_assume_tac) >>
  drule_all intcall_array_prefix_frame >>
  disch_then (qspecl_then [`j4`, `j3`] strip_assume_tac) >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

(* Preserve the memory of the actual straight-line execution, not merely
   some endpoint satisfying the ordinary existential simulation. *)
Theorem intcall_array_prefix_continuation_frame:
  lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb.cs_current_insts bb.bb_instructions /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  run_inst_seq sb.cs_current_insts s = OK t /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    sb.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> GAS) sb.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es t /\
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s ==>
  ?s2. s2.vs_current_bb = sb.cs_current_bb /\
    s2.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~s2.vs_halted /\
    stmt_state_rel ctx func cenv cx es s2 /\
    s2.vs_vars = t.vs_vars /\ s2.vs_allocas = s.vs_allocas /\
    s2.vs_memory = t.vs_memory /\
    gas_marked_path F ctx func s 0 (OK s2) /\
    (!fuel rr. run_from fuel ctx func s2 = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func s = rr)
Proof
  strip_tac >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
   t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `_ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `FILTER (\i. i.inst_opcode = GAS) sb.cs_current_insts = []` by
    (simp[FILTER_EQ_NIL]) >>
  `gas_path ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_at (Pos last) tuple_run_inst_seq_gas_path >>
     disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx, gas_marked_path_def] >>
  metis_tac[gas_path_normal]
QED
