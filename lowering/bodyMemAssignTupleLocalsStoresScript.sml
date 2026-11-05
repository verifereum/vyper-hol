(* Memory-checked stores for the existing-local tuple assignment suffix. *)
Theory bodyMemAssignTupleLocalsStores
Ancestors
  bodyMemAssignTupleLocalsFacts bodyDeclWordMemory bodyMemAssignLocalWord
  tupleLocalStoreRun stmtSimAssignStore stmtSimDeclStore
  fragGasMode fragGasPathMem fragExecMem emitHelperProps emitHelper
  stmtSimDefs exprLoweringProps localPtrsProps valueEncoding valueEncodingProofs
  venomState venomInst vyperState vyperLookup finite_map list compileEnv
  valueEncodingProps

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
