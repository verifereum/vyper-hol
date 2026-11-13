(* Counted clean offsets and member child application. *)
Theory storeSlotsPtrMemberOffset
Ancestors
  storeSlotsPtrInterface reasonCodeOffsetPtr bodyPtrAttributeAdd
  emitHelper exprLoweringProps stateFrame venomState ptrDiscipline
  fragGasPathPtr bodyPtrDefs context compileEnv words finite_map arithmetic list

Theorem store_slots_clean_add_resources:
  emit_op ADD [op; Lit (n2w off)] sa = (r,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand op s = SOME a /\ op_taint tn op = {} ==>
  ?Gf tf u. gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK u) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    eval_operand r u = SOME (a + n2w off) /\ op_taint tf r = {} /\
    execution_frame u = execution_frame s /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==> lookup_var p u = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   op_taint tn (Lit (n2w off)) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`]
    attribute_emit_binop_path_ptr)) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >> gvs[] >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G tn s 0 g1 t1 (OK s1)` >>
  qexistsl_tac [`g1`, `t1`, `s1`] >> simp[] >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[emit_op_def, fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  simp[Abbr `s1`, execution_frame_def, update_var_def, lookup_var_def,
    eval_operand_def, FLOOKUP_UPDATE] >>
  drule code_offset_emit_shape >> strip_tac >> rpt strip_tac >>
  `p <> out` by metis_tac[] >> simp[FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem store_slots_clean_offset_resources:
  compile_lit_byte_offset op off sa = (r,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand op s = SOME a /\ op_taint tn op = {} ==>
  ?Gf tf u. gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK u) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    eval_operand r u = SOME (a + n2w off) /\ op_taint tf r = {} /\
    execution_frame u = execution_frame s /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==> lookup_var p u = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> Cases_on `off = 0`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >> simp[WORD_ADD_0] >>
      irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  Cases_on `op`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def, eval_operand_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >> simp[eval_operand_def, op_taint_def] >>
      irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  gvs[compile_lit_byte_offset_def] >>
  drule_all store_slots_clean_add_resources >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tf`, `u`] >> fs[execution_frame_def]
QED

Theorem store_slots_member_offset_run_ptr:
  compile_lit_byte_offset (Var root) mo sa = (ms,a) /\
  compile_lit_byte_offset slot so a = (ds,b) /\
  compile_store_slots cenv ms ds ty tr b = ((),sc) /\
  store_slots_ptr_entry cenv D ctx PG ty tv v /\
  not_fresh_at sa root /\ (!x. slot = Var x ==> not_fresh_at sa x) /\
  lookup_var root s = SOME sw /\ eval_operand slot s = SOME dw /\
  op_taint tn slot = {} /\ ptr_covers G tn root s capacity /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n sw + mo) m) /\
  mo + val_store_size tv v <= capacity /\ mo < dimword (:256) /\
  w2n sw + mo + type_memory_size tv < dimword (:256) /\
  w2n dw + so + type_slot_size tv <= dimword (:256) /\
  encode_value tv v = SOME writes /\
  fn_has_code sa a func /\ fn_has_code a b func /\ fn_has_code b sc func /\
  fn_inst_ids_distinct func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  ~s.vs_call_ctx.cc_static /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tf u ks p tp.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK u) /\
    store_slots_ptr_frame tr (sw+n2w mo) (dw+n2w so) p tp ks u tf /\
    execution_frame p = execution_frame s /\
    tp.t_mem = tn.t_mem /\ tp.t_imm = tn.t_imm /\
    tp.t_stor = tn.t_stor /\ tp.t_trans = tn.t_trans /\
    (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_labels = s.vs_labels /\
    u.vs_call_ctx = s.vs_call_ctx /\
    ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts
Proof
  strip_tac >>
  `w2n sw + mo < dimword (:256)` by decide_tac >>
  drule_all store_slots_offset_resources >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 g1 t1 (OK s1)` >>
  `eval_operand slot s1 = SOME dw /\ op_taint t1 slot = {}` by
    (Cases_on `slot` >> gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  `not_fresh_at a out /\ (!x. not_fresh_at sa x ==> not_fresh_at a x)` by
    (qpat_assum `compile_lit_byte_offset (Var root) _ _ = _`
       (mp_then Any mp_tac reasonCodeTransferPtrTheory.code_offset_compiler_frame) >>
     simp[] >> metis_tac[]) >>
  drule_all store_slots_clean_offset_resources >>
  disch_then (qspecl_then [`PG`, `g1`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx func PG g1 t1 s1 0 g2 t2 (OK s2)` >>
  suspend "child"
QED

Resume store_slots_member_offset_run_ptr[child]:
  `(!x. slot = Var x ==> not_fresh_at a x)` by metis_tac[] >>
  `not_fresh_at b out /\ (!x. ds = Var x ==> not_fresh_at b x) /\
   (!x. not_fresh_at a x ==> not_fresh_at b x)` by
    (qpat_assum `compile_lit_byte_offset slot _ _ = _`
      (mp_then Any mp_tac reasonCodeTransferPtrTheory.code_offset_compiler_frame) >>
     simp[] >> metis_tac[]) >>
  `lookup_var out s2 = SOME (sw+n2w mo) /\
   ptr_covers g2 t2 out s2 (val_store_size tv v)` by
    (qpat_assum `!p. not_fresh_at a p ==> _`
       (qspec_then `out` mp_tac) >> simp[] >>
     fs[ptr_covers_def] >> gvs[]) >>
  `w2n (sw+n2w mo) = w2n sw + mo` by
    (simp[w2n_add_2] >> decide_tac) >>
  `w2n (dw+n2w so) + type_slot_size tv <= dimword (:256)` by
    (simp[word_add_def, w2n_n2w] >>
     mp_tac (Q.INST [`x` |-> `w2n (dw:bytes32) + so`, `y` |-> `dimword (:256)`]
       MOD_LESS_EQ) >> simp[ADD_COMM] >> decide_tac) >>
  `(!m. mem_agree_outside t2.t_mem s2.vs_memory m ==>
    val_in_memory tv v (w2n (sw+n2w mo)) m) /\ ~s2.vs_call_ctx.cc_static` by
    (fs[execution_frame_def] >> metis_tac[]) >>
  qpat_x_assum `ms = Var out` SUBST_ALL_TAC >>
  qpat_x_assum `store_slots_ptr_entry _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[store_slots_ptr_entry_def] >>
  disch_then (drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `encode_value _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`sw+n2w mo`, `dw+n2w so`] mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >> suspend "compose"
QED
Resume store_slots_member_offset_run_ptr[compose]:
  `gas_path_ptr D 0 ctx func PG G tn s 0 g2 t2 (OK s2)` by
    (metis_tac[gas_path_ptr_then, ADD_0]) >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK u)` by
    (metis_tac[gas_path_ptr_then, ADD_0]) >>
  qexistsl_tac [`Gf`, `tf`, `u`, `ks`, `s2`, `t2`] >>
  simp[] >>
  conj_tac >- gvs[] >>
  fs[execution_frame_def] >> metis_tac[]
QED
Finalise store_slots_member_offset_run_ptr
