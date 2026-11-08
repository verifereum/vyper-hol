(* Compiler boundary for a single storage/transient word copied to memory. *)
Theory storageWordCompilePtr
Ancestors
  storageCopyWordPtr reasonNormalizePtr literalAllocPathPtr loweringHalt exprSimCopy
  emitHelper emitHelperProps context compileEnv exprLoweringProps fragExec
  moduleLoweringProps localPtrsProps venomInst venomState words arithmetic list rich_list
  ptrDiscipline fragGasPathPtr vfmConstants

Theorem storage_word_emission:
  emit_op opc [src] sa = (v,sd) /\
  emit_void MSTORE [dst;v] sd = (u,sb) ==>
  ?x. v = Var x /\ ~not_fresh_at sa x /\
    sa.cs_next_var <= sb.cs_next_var /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id opc [src] [x];
       mk_inst (sa.cs_next_id+1) MSTORE [dst;Var x] []] /\
    cs_extends sa sb
Proof
  simp[emit_op_def, emit_void_def, emit_inst_def, fresh_var_def, fresh_id_def,
    emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[not_fresh_at_def, fresh_var_distinct,
    cs_extends_def, IS_PREFIX_APPEND]
QED

Theorem allocated_storage_word_code:
  compile_alloc_buffer cap sa = (buf,sc) /\
  emit_op opc [src] sc = (v,sd) /\
  emit_void MSTORE [buf.buf_operand;v] sd = (u,sb) /\
  fn_has_code sa sb fn ==>
  fn_has_code sa sc fn /\ fn_has_code sc sb fn /\
  sa.cs_next_var <= sc.cs_next_var
Proof
  strip_tac >> drule_all storage_word_emission >> strip_tac >>
  `cs_extends sa sc` by metis_tac[compile_alloc_buffer_extends] >>
  drule compile_alloc_buffer_emission >> strip_tac >>
  drule_all fn_has_code_split >> simp[]
QED

Theorem storage_word_registered_layout:
  emit_op opc [src] sa = (v,sd) /\
  emit_void MSTORE [dst;v] sd = (u,sb) /\ fn_has_code sa sb fn ==>
  ?x bb post. v = Var x /\ ~not_fresh_at sa x /\
    lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id opc [src] [x];
       mk_inst (sa.cs_next_id+1) MSTORE [dst;Var x] []] ++ post /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts+2
Proof
  strip_tac >> drule_all storage_word_emission >> strip_tac >>
  gvs[fn_has_code_def, emitted_blocks_def] >>
  gvs[IS_PREFIX_APPEND] >>
  qexistsl [`x`,`bb`,`l`] >> simp[GSYM APPEND_ASSOC]
QED

Theorem compile_storage_word_path_ptr:
  emit_op (if tr then TLOAD else SLOAD) [src] sa = (v,sd) /\
  emit_void MSTORE [Var root;v] sd = (u,sb) /\ fn_has_code sa sb fn /\
  copy_old_operand sa src /\ not_fresh_at sa root /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  op_taint tn src = {} /\ ptr_covers G tn root s 32 /\
  w2n b+32 < dimword(:256) /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_inv s /\ alloca_room ctx fn s /\
  (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w) ==>
  ?t Gf tf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    copy_prefix (if tr then LocTransient else LocStorage) a (w2n b) 1 s 1 t /\
    lookup_var root t = SOME b /\ ptr_covers Gf tf root t 32 /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!h. h < 32 ==> (w2n b+h IN tf.t_mem <=>
      (a,h) IN (if tr then tf.t_trans else tf.t_stor))) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    t.vs_allocas = s.vs_allocas /\ alloca_inv t /\ alloca_room ctx fn t /\
    (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w)
Proof
  strip_tac >> drule_all storage_word_registered_layout >> strip_tac >>
  `root <> x /\ src <> Var x` by
    (Cases_on `src` >> fs[copy_old_operand_def] >> metis_tac[]) >>
  drule_at (Pat `_ = _ ++ _ ++ _`) storage_copy_word_path_ptr >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_room _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qexistsl [`t`,`G'`,`tn'`] >> simp[] >>
  metis_tac[]
QED

Theorem allocated_storage_word_path_ptr:
  compile_alloc_buffer 32 sa = (buf,sc) /\
  emit_op (if tr then TLOAD else SLOAD) [src] sc = (v,sd) /\
  emit_void MSTORE [buf.buf_operand;v] sd = (u,sb) /\
  fn_has_code sa sb fn /\ copy_old_operand sa src /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_inv s /\ alloca_room ctx fn s /\ fn_inst_ids_distinct fn /\
  (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w) ==>
  ?root b sm t Gf tf.
    buf.buf_operand = Var root /\
    sm.vs_accounts = s.vs_accounts /\ sm.vs_transient = s.vs_transient /\
    sm.vs_call_ctx = s.vs_call_ctx /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    lookup_var root t = SOME (n2w b) /\ ptr_covers Gf tf root t 32 /\
    b+32 < dimword(:256) /\
    copy_prefix (if tr then LocTransient else LocStorage) a b 1 sm 1 t /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!h. h < 32 ==> (b+h IN tf.t_mem <=>
      (a,h) IN (if tr then tn.t_trans else tn.t_stor))) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    alloca_inv t /\ alloca_room ctx fn t /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas aid = SOME (p,sz)) /\
    (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w)
Proof
  strip_tac >> drule_all allocated_storage_word_code >> strip_tac >>
  `32 < dimword(:256)` by simp[dimword_def] >>
  drule_all compile_alloc_buffer_path_resources_ptr >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  rename1 `ptr_covers gm tm root sm 32` >>
  `copy_old_operand sc src` by metis_tac[copy_old_operand_mono] >>
  `eval_operand src sm = SOME a /\ op_taint tm src = {}` by
    (Cases_on `src` >> fs[copy_old_operand_def, eval_operand_def, op_taint_def]) >>
  qpat_x_assum `emit_void _ _ _ = _` mp_tac >> asm_rewrite_tac[] >> disch_tac >>
  `w2n (n2w b : bytes32) = b` by simp[] >>
  drule_at (Pat `emit_void _ _ _ = _`) compile_storage_word_path_ptr >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_room _ _ _`)) >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >> suspend "endpoint"
QED
Resume allocated_storage_word_path_ptr[endpoint]:
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t)` by
    metis_tac[fragGasPathPtrTheory.gas_path_ptr_then, ADD] >>
  qexistsl [`root`,`b`,`sm`,`t`,`Gf`,`tf`] >> gvs[] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sc x` by
        (qpat_x_assum `not_fresh_at sa x` mp_tac >>
         simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
      metis_tac[]) >>
  metis_tac[]
QED
Finalise allocated_storage_word_path_ptr
