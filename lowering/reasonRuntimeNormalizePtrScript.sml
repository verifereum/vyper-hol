(* Compiler-facing runtime string normalization at one checked endpoint. *)
Theory reasonRuntimeNormalizePtr
Ancestors
  reasonNormalizeHead reasonNormalizePtr stringUnwrapLayout appendStorageGhostPtr
  reasonCopySourcePtr loweringPosts bodyPtrDefs venomState venomMemDefs
  compileEnv context exprLowering words arithmetic vyperValue valueEncoding
  exprSimCopy vyperInterpreter vyperTypeSystem vyperState

Theorem unwrap_storage_string_positive_path_ptr:
  0 < max /\ p.ptr_location = (if tr then LocTransient else LocStorage) /\
  unwrap_value cenv (LocatedValue (BaseT (StringT max)) p) sa = (out,sb) /\
  storage_holds cx tr (BaseT (StringT max)) tv a es s /\
  read_result cx tv es = (INL (StringV str),es) /\
  val_wf (BaseTV (StringT max)) (StringV str) /\
  fn_has_code sa sb fn /\ copy_old_operand sa p.ptr_operand /\
  eval_operand p.ptr_operand s = SOME a /\ op_taint tn p.ptr_operand = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) a = {} /\
  type_slot_size (BaseTV (StringT max)) < dimword(:256) /\
  32 * type_slot_size (BaseTV (StringT max)) < dimword(:256) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_inv s /\ alloca_room ctx fn s /\ fn_inst_ids_distinct fn /\
  (!i w q sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (q,sz) ==> sz = w2n w) ==>
  ?root b t Gf tf.
    out = Var root /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand out t = SOME (n2w b) /\
    ptr_covers Gf tf root t (val_store_size (BaseTV (StringT max)) (StringV str)) /\
    b + val_store_size (BaseTV (StringT max)) (StringV str) < dimword(:256) /\
    mload b t = n2w (LENGTH str) /\ mem_word_taint tf.t_mem b = {} /\
    (!x C. not_fresh_at sa x /\ ptr_covers G tn x s C ==>
      lookup_var x t = lookup_var x s /\ ptr_covers Gf tf x t C) /\
    alloca_inv t /\ alloca_room ctx fn t /\
    (!aid q sz. FLOOKUP s.vs_allocas aid = SOME (q,sz) ==>
      FLOOKUP t.vs_allocas aid = SOME (q,sz)) /\
    (!i w q sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (q,sz) ==> sz = w2n w)
Proof
  strip_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_string_storage_layout >>
  (impl_tac >- (Cases_on `tr` >> gvs[])) >> strip_tac >>
  drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`)
    allocated_storage_string_path_ptr >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `val_wf _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `op_taint _ _ = _`)) >>
  disch_then (drule_at (Pat `alloca_room _ _ _`)) >>
  disch_then (qspecl_then [`PG`,`G`,`D`] mp_tac) >>
  (impl_tac >- (Cases_on `tr` >> gvs[] >> metis_tac[])) >> strip_tac >>
  `mem_word_at b t.vs_memory = n2w (LENGTH str)` by
    (irule storage_copy_string_head >>
     goal_assum (drule_at (Pat `storage_holds _ _ _ _ _ _ _`)) >>
     qexistsl [`type_slot_size (BaseTV (StringT max))`,`sm`] >>
     gvs[type_slot_size_def]) >>
  drule string_store_size_slots >> strip_tac >>
  qexistsl [`root`,`b`,`t`,`Gf`,`tf`] >> gvs[mload_def, mem_word_at_def, mem_bytes_at_def, lookup_var_def] >>
  conj_tac
  >- (rpt strip_tac >> irule ptr_covers_old_transport >>
      goal_assum (drule_at Any) >> qexists `sa` >> simp[lookup_var_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem unwrap_runtime_immutable_string_path_ptr:
  ~cenv.ce_is_ctor /\ p.ptr_location = LocCode /\
  unwrap_value cenv (LocatedValue (BaseT (StringT max)) p) sa = (out,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\
  immutable_holds cenv cx (BaseT (StringT max)) (Value (StringV str)) a es s /\
  evaluate_type (get_tenv cx) (BaseT (StringT max)) = SOME (BaseTV (StringT max)) /\
  fn_has_code sa sb fn /\ copy_old_operand sa p.ptr_operand /\
  eval_operand p.ptr_operand s = SOME a /\ op_taint tn p.ptr_operand = {} /\
  32 * type_slot_size (BaseTV (StringT max)) < dimword(:256) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_inv s /\ alloca_room ctx fn s /\ fn_inst_ids_distinct fn /\
  (!i w q sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (q,sz) ==> sz = w2n w) ==>
  ?root b t Gf tf.
    out = Var root /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand out t = SOME (n2w b) /\
    ptr_covers Gf tf root t (val_store_size (BaseTV (StringT max)) (StringV str)) /\
    b + val_store_size (BaseTV (StringT max)) (StringV str) < dimword(:256) /\
    mload b t = n2w (LENGTH str) /\ mem_word_taint tf.t_mem b = {} /\
    (!x C. not_fresh_at sa x /\ ptr_covers G tn x s C ==>
      lookup_var x t = lookup_var x s /\ ptr_covers Gf tf x t C) /\
    alloca_inv t /\ alloca_room ctx fn t /\
    (!aid q sz. FLOOKUP s.vs_allocas aid = SOME (q,sz) ==>
      FLOOKUP t.vs_allocas aid = SOME (q,sz)) /\
    (!i w q sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (q,sz) ==> sz = w2n w)
Proof
  strip_tac >> drule_all immutable_holds_bounds >> strip_tac >>
  drule_all immutable_holds_data >> strip_tac >>
  `tvt = BaseTV (StringT max) /\ v = StringV str` by
    fs[read_result_def, return_def, evaluate_type_def] >> gvs[] >>
  drule_all unwrap_string_code_layout >> strip_tac >>
  qpat_x_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  drule_all allocated_runtime_immutable_string_path_ptr >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  `mem_word_at b t.vs_memory = n2w (LENGTH str)` by
    (irule immutable_runtime_string_head >>
     goal_assum (drule_at (Pat `val_in_memory _ _ _ _`)) >>
     qexistsl [`type_slot_size (BaseTV (StringT max))`,`sm`] >> simp[] >>
     fs[type_memory_size_def, type_slot_size_def]) >>
  drule string_store_size_slots >> strip_tac >>
  qexistsl [`root`,`b`,`t`,`Gf`,`tf`] >>
  gvs[mload_def, mem_word_at_def, mem_bytes_at_def, lookup_var_def] >>
  conj_tac
  >- (rpt strip_tac >> irule ptr_covers_old_transport >>
      goal_assum (drule_at Any) >> qexists `sa` >> simp[lookup_var_def] >> metis_tac[]) >>
  metis_tac[]
QED
