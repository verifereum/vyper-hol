(* Memory-checked stores for the existing-local tuple assignment suffix. *)
Theory bodyMemAssignTupleLocalsStores
Ancestors
  bodyMemAssignTupleLocalsFacts bodyDeclWordMemory bodyMemAssignLocalWord
  tupleLocalStoreRun stmtSimAssignStore stmtSimDeclStore
  fragGasMode fragGasPathMem fragExecMem emitHelperProps emitHelper
  stmtSimDefs exprLoweringProps localPtrsProps valueEncoding valueEncodingProofs
  venomState venomInst vyperState vyperLookup finite_map list compileEnv
  valueEncodingProps valueCopy valueCopyBytes bodyDeclMemoryCore exprSimProps
  valueTypingMemoryProps bodyMemAssignLocalMem bodyDeclMemoryCounted

(* Word branch of S1 tuple_local_store_head_path, including the disjoint
   memory frame needed to retain the unread tuple suffix. *)
Theorem tuple_local_word_store_head_path_mem:
  emit_void MSTORE [Var p; op] st = ((), st') /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  stmt_state_rel ctx func cenv cx es s /\ alloca_history func s /\
  find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  store_lays_out tv entry.type v ==>
  ?dw t. lookup_var p s = SOME dw /\
    stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    (!x. lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_history func t /\
    (!a len. a + len <= w2n dw \/ w2n dw + 32 <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
    gas_marked_path T ctx func s 0 (OK t)
Proof
  strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `?dw. lookup_var p s = SOME dw` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  `type_memory_size entry.type = 32` by fs[store_lays_out_def] >>
  `w2n dw + 32 <= s.vs_alloca_next` by
    (irule (tuple_local_destination_room |> cj 3) >>
     qexistsl_tac [`cenv`, `ctx`, `cx`, `entry`, `es`, `func`, `id`, `p`, `sz`] >>
     simp[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all stmt_state_rel_write_local_store >> strip_tac >>
  drule_all annassign_word_mstore_path_mem >> strip_tac >>
  `st'.cs_current_bb = st.cs_current_bb` by
    metis_tac[emit_void_same_blocks, same_blocks_def] >>
  `!a len. a + len <= w2n dw \/ w2n dw + 32 <= a ==>
     mem_bytes_at a len (mstore (w2n dw) (typed_val_to_w256 tv v) s).vs_memory =
     mem_bytes_at a len s.vs_memory` by
    (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  qexistsl_tac [`dw`, `mstore (w2n dw) (typed_val_to_w256 tv v) s with
                              vs_inst_idx := LENGTH st'.cs_current_insts`] >>
  simp[stmt_state_rel_inst_idx, gas_marked_path_def] >>
  fs[mstore_def, lookup_var_def, LET_THM] >> first_assum ACCEPT_TAC
QED

(* Compatible nonword copy: S1's compatible-run normalization, retaining
   the smaller capacity frame for the tuple's unread suffix. *)
Theorem tuple_compatible_store_run_mem:
  !cenv src dst dty sty sa sb s tenv dtv stv v sw dw.
  compile_store_memory cenv src dst dty sty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  ~is_word_type dty /\
  evaluate_type tenv dty = SOME dtv /\ evaluate_type tenv sty = SOME stv /\
  value_has_type dtv v /\ val_wf dtv v /\ value_has_type stv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  (dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_size dtv + 64 < dimword (:256) /\
  w2n sw + val_store_size stv v <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!a len. a + len <= w2n dw \/
       w2n dw + MIN (type_memory_size stv) (type_memory_size dtv) <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_store_memory cenv src dst dty dty sa = ((),sb) /\
   val_in_memory dtv v (w2n sw) s.vs_memory /\
   val_store_size dtv v = val_store_size stv v /\
   (if is_bytestring_type dty then val_store_size dtv v
    else type_memory_size dtv) <= MIN (type_memory_size stv) (type_memory_size dtv)` by
    (Cases_on `dty = sty`
     >- (gvs[] >> drule val_store_size_le >>
         Cases_on `is_bytestring_type dty` >> simp[]) >>
     gvs[] >>
     `val_wf stv v` by metis_tac[value_has_type_memory_wf] >>
     `val_store_size dtv v = val_store_size stv v` by
       metis_tac[bytestring_val_store_size_eq] >>
     `val_store_size dtv v <= type_memory_size dtv /\
      val_store_size stv v <= type_memory_size stv` by
       metis_tac[val_store_size_le] >>
     conj_tac >- metis_tac[compile_store_memory_bytestring_src] >>
     conj_tac >- metis_tac[bytestring_val_in_memory_transfer] >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule body_typed_store_memory_mem_ok >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     qexistsl_tac [`dw`, `tenv`, `dtv`, `v`, `sw`] >> simp[] >>
     metis_tac[]) >>
  drule compile_store_memory_run_frame_with_capacity >>
  disch_then (qspecl_then [`s`, `tenv`, `dtv`, `v`, `sw`, `dw`,
     `MIN (type_memory_size stv) (type_memory_size dtv)`] mp_tac) >>
  (impl_tac >- (Cases_on `is_bytestring_type dty` >> gvs[])) >>
  strip_tac >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
  simp[venom_state_component_equality]
QED

Theorem tuple_local_nonword_store_head_path_mem:
  compile_store_memory cenv op (Var p) vt ty st = ((),st') /\
  (!x. op = Var x ==> not_fresh_at st x) /\
  local_ptrs_reserved cenv st /\ eval_operand op s = SOME w /\
  ~is_word_type vt /\ evaluate_type (get_tenv cx) vt = SOME entry.type /\
  value_has_type entry.type v /\ val_wf entry.type v /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
  type_memory_bytes cenv vt = type_memory_size entry.type /\
  type_memory_size entry.type + 64 < dimword (:256) /\
  w2n w + val_store_size tv v <= s.vs_alloca_next /\
  stmt_state_rel ctx func cenv cx es s /\ alloca_history func s /\
  find_containing_scope id es.scopes = SOME (pre,env,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) dsz) /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?dw t. lookup_var p s = SOME dw /\
    stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_history func t /\
    (!a len. a + len <= w2n dw \/
       w2n dw + MIN (type_memory_size tv) (type_memory_size entry.type) <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
    gas_marked_path T ctx func s 0 (OK t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `?dw. lookup_var p s = SOME dw /\
        w2n dw + type_memory_size entry.type <= s.vs_alloca_next` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >> gvs[] >> metis_tac[]) >>
  `not_fresh_at st p` by
    (gns[local_ptrs_reserved_def] >> metis_tac[]) >>
  `eval_operand (Var p) s = SOME dw` by simp[eval_operand_def] >>
  drule tuple_compatible_store_run_mem >>
  disch_then (qspecl_then [`s`, `get_tenv cx`, `entry.type`, `tv`, `v`, `w`, `dw`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!a len. a + len <= w2n dw \/ w2n dw + type_memory_size entry.type <= a ==>
     mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     qpat_x_assum `!a len. _ ==> mem_bytes_at a len t.vs_memory = _` irule >>
     simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  `stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t` by
    (irule local_memory_write_frame >> simp[] >>
     qexistsl_tac [`s`, `st`, `dw`] >>
     simp[] >> conj_tac
     >- metis_tac[arithmeticTheory.ADD_COMM] >>
     qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts st st')` by
    metis_tac[compile_store_memory_same_no_gas, compile_store_memory_bytestring_src] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts st st')` by fs[EVERY_MEM] >>
  `gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH st'.cs_current_insts)) /\
   ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[] >> qexists_tac `st` >> simp[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func (t with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >> qexistsl_tac [`s`, `st`] >> simp[]) >>
  qexistsl_tac [`dw`, `t with vs_inst_idx := LENGTH st'.cs_current_insts`] >>
  simp[stmt_state_rel_inst_idx, gas_marked_path_def, lookup_var_def] >>
  conj_tac >- fs[lookup_var_def] >> first_assum ACCEPT_TAC
QED

Theorem tuple_local_store_head_path_mem:
  (if is_word_type ty then emit_void MSTORE [Var p; op]
   else compile_store_memory cenv op (Var p) vt ty) st = ((),st') /\
  eval_operand op s = SOME w /\
  (if is_word_type ty then
     w = typed_val_to_w256 tv v /\ store_lays_out tv entry.type v
   else
     ~is_word_type vt /\ evaluate_type (get_tenv cx) vt = SOME entry.type /\
     value_has_type entry.type v /\ val_wf entry.type v /\
     val_in_memory tv v (w2n w) s.vs_memory /\
     evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
     (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
     type_memory_bytes cenv vt = type_memory_size entry.type /\
     type_memory_size entry.type + 64 < dimword (:256) /\
     w2n w + val_store_size tv v <= s.vs_alloca_next) /\
  (!x. op = Var x ==> not_fresh_at st x) /\ local_ptrs_reserved cenv st /\
  stmt_state_rel ctx func cenv cx es s /\ alloca_history func s /\
  find_containing_scope id es.scopes = SOME (pre,env,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) dsz) /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?dw t. lookup_var p s = SOME dw /\
    stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_history func t /\
    (!a len. a + len <= w2n dw \/
       w2n dw + (if is_word_type ty then 32
                  else MIN (type_memory_size tv) (type_memory_size entry.type)) <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
    gas_marked_path T ctx func s 0 (OK t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type ty`
  >- (gvs[] >> drule_all tuple_local_word_store_head_path_mem >>
      strip_tac >> goal_assum (drule_at Any) >> simp[] >>
      first_assum ACCEPT_TAC) >>
  gnvs[] >>
  qpat_x_assum `~is_word_type vt /\ _`
    (map_every assume_tac o CONJUNCTS) >>
  drule_all tuple_local_nonword_store_head_path_mem >>
  strip_tac >> goal_assum (drule_at Any) >> simp[] >> first_assum ACCEPT_TAC
QED
