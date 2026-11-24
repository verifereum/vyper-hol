(* The address computation after a successful memory Append guard. *)
Theory bodyAppendMemoryAddressMods
Ancestors
  bodyFullStoreSlotsAddresses typedCopyOriginPtrBase typedMemoryCopy
  bodyPtrDefs assignTuplePtrCopyLen fragGasOriginPtrLoop fragExec
  ptrDiscipline venomState venomInst compileEnv exprLoweringProps freshWrites
  vyperLookupStorage finite_map words

Theorem address_scalar_frame[local]:
  t = (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) /\
  (!p. not_fresh_at a p ==> lookup_var p t = lookup_var p s) ==>
  typed_copy_state_frame a 0 0 s t
Proof
  strip_tac >> simp[typed_copy_state_frame_def] >>
  simp[update_var_def, venom_state_component_equality, typed_copy_frame_def]
QED

Theorem address_cover_cursor[local]:
  ptr_covers G tn p (s with vs_inst_idx := i) n <=> ptr_covers G tn p s n
Proof
  simp[ptr_covers_def, lookup_var_def]
QED

Theorem address_add_offset[local]:
  emit_op ADD [Var p; op] a = (dst,b) /\ fn_has_code a b func /\
  lookup_var p s = SOME bp /\ eval_operand op s = SOME (n2w delta) /\
  op_taint tn op = {} /\ ptr_covers G tn p s extent /\ delta + n <= extent /\
  w2n bp + delta < dimword (:256) /\ not_fresh_at a p /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?x t Gf tf.
    dst = Var x /\ not_fresh_at b x /\
    lookup_var x t = SOME (n2w (w2n bp + delta)) /\ ptr_covers Gf tf x t n /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    typed_copy_state_frame a 0 0 s t /\ t.vs_memory = s.vs_memory /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_labels = s.vs_labels /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!y. not_fresh_at a y ==> lookup_var y t = lookup_var y s /\
      FLOOKUP Gf y = FLOOKUP G y /\ op_taint tf (Var y) = op_taint tn (Var y))
Proof
  strip_tac >>
  `eval_operand (Var p) s = SOME bp` by simp[eval_operand_def] >>
  `op_taint tn (Var p) = {}` by fs[ptr_covers_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `w` |-> `x+y`]
    store_address_binop_uniform)) >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choose_then `out` strip_assume_tac)) >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK t,Gf,tf)` >>
  `p <> out` by simp[] >>
  `ptr_covers Gf tf out t n` by
    (simp[Abbr `Gf`, Abbr `tf`, Abbr `t`, address_cover_cursor] >>
     irule typed_copy_origin_ptr_offset_covers >> simp[] >> qexists_tac `extent` >> simp[]) >>
  `typed_copy_state_frame a 0 0 s t` by
    (irule address_scalar_frame >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`out`,`bp + n2w delta`] >> simp[Abbr `t`]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    metis_tac[typed_copy_state_frame_allocas_below_fmp] >>
  `bp + n2w delta = n2w (w2n bp + delta)` by simp[GSYM word_add_n2w] >>
  qexistsl_tac [`out`,`t`,`Gf`,`tf`] >> simp[] >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE, allocas_from_def] >>
  fs[allocas_from_def]
QED

Theorem address_scale_length[local]:
  emit_op MUL [Var lenvar; Lit (n2w stride)] a = (off,b) /\
  fn_has_code a b func /\
  lookup_var lenvar s = SOME (n2w len) /\ op_taint tn (Var lenvar) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t Gf tf.
    eval_operand off t = SOME (n2w (len*stride)) /\ op_taint tf off = {} /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    typed_copy_state_frame a 0 0 s t /\ t.vs_memory = s.vs_memory /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_labels = s.vs_labels /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!y. not_fresh_at a y ==> lookup_var y t = lookup_var y s /\
      FLOOKUP Gf y = FLOOKUP G y /\ op_taint tf (Var y) = op_taint tn (Var y))
Proof
  strip_tac >>
  `eval_operand (Var lenvar) s = SOME (n2w len) /\
   eval_operand (Lit (n2w stride)) s = SOME (n2w stride) /\
   op_taint tn (Lit (n2w stride)) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `MUL`, `w` |-> `x*y`]
    store_address_binop_uniform)) >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choose_then `out` strip_assume_tac)) >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK t,Gf,tf)` >>
  `typed_copy_state_frame a 0 0 s t` by
    (irule address_scalar_frame >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`out`,`n2w len * n2w stride : bytes32`] >> simp[Abbr `t`]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    metis_tac[typed_copy_state_frame_allocas_below_fmp] >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[] >>
  simp[Abbr `t`, update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
       allocas_from_def, word_mul_n2w] >> fs[allocas_from_def]
QED

Theorem append_memory_address_path_mods:
  emit_op ADD [Var p; Lit 32w] a = (dop,a1) /\
  emit_op MUL [Var lenvar; Lit (n2w stride)] a1 = (off,a2) /\
  emit_op ADD [dop;off] a2 = (dst,a3) /\ fn_has_code a a3 func /\
  not_fresh_at a p /\ not_fresh_at a lenvar /\
  lookup_var p s = SOME bp /\ lookup_var lenvar s = SOME (n2w (LENGTH vs)) /\
  ptr_covers G tn p s (32+cap*stride) /\ op_taint tn (Var lenvar) = {} /\
  0 < stride /\ LENGTH vs < cap /\ w2n bp + (32+cap*stride) <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?xd t Gf tf.
    dst = Var xd /\ not_fresh_at a3 xd /\
    lookup_var xd t = SOME (n2w (w2n bp + 32 + LENGTH vs*stride)) /\
    ptr_covers Gf tf xd t stride /\
    w2n bp + 32 + LENGTH vs*stride + stride <= t.vs_alloca_next /\
    t.vs_alloca_next < dimword (:256) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    typed_copy_state_frame a 0 0 s t /\ t.vs_memory = s.vs_memory /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_labels = s.vs_labels /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = a3.cs_current_bb /\
    t.vs_inst_idx = LENGTH a3.cs_current_insts /\
    (!y. not_fresh_at a y ==> not_fresh_at a3 y /\ lookup_var y t = lookup_var y s /\
      FLOOKUP Gf y = FLOOKUP G y /\ op_taint tf (Var y) = op_taint tn (Var y))
Proof
  strip_tac >>
  `ci_mono a a1 /\ ci_mono a1 a2 /\ ci_mono a2 a3` by
    metis_tac[typed_copy_emit_op_mono] >>
  `cs_extends a a1 /\ cs_extends a1 a2 /\ cs_extends a2 a3` by fs[ci_mono_def] >>
  `fn_has_code a a1 func /\ fn_has_code a1 a2 func /\ fn_has_code a2 a3 func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `!x. (not_fresh_at a x ==> not_fresh_at a1 x) /\
       (not_fresh_at a1 x ==> not_fresh_at a2 x) /\
       (not_fresh_at a2 x ==> not_fresh_at a3 x)` by
    metis_tac[not_fresh_at_mono, ci_mono_def] >>
  `LENGTH vs * stride + stride <= cap*stride` by simp[array_index_element_end_bound] >>
  `w2n bp + 32 < dimword (:256) /\
   w2n bp + 32 + LENGTH vs*stride + stride <= s.vs_alloca_next` by decide_tac >>
  `eval_operand (Lit 32w) s = SOME (n2w 32) /\ op_taint tn (Lit 32w) = {} /\
   32 + cap*stride <= 32 + cap*stride` by simp[eval_operand_def, op_taint_def] >>
  drule_all (Q.INST [`delta` |-> `32`, `n` |-> `cap*stride`] address_add_offset) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`xd0`,`q1`,`G1`,`tn1`] strip_assume_tac)) >>
  `lookup_var lenvar q1 = SOME (n2w (LENGTH vs)) /\ op_taint tn1 (Var lenvar) = {}` by simp[] >>
  drule_all address_scale_length >>
  disch_then (qspecl_then [`explicit`,`PG`,`G1`]
    (qx_choosel_then [`q2`,`G2`,`tn2`] strip_assume_tac)) >>
  `lookup_var xd0 q2 = SOME (n2w (w2n bp + 32)) /\ ptr_covers G2 tn2 xd0 q2 (cap*stride)` by
    (conj_tac >- simp[] >> irule ptr_covers_lookup_frame >> metis_tac[]) >>
  `not_fresh_at a2 xd0` by simp[] >>
  `w2n ((n2w (w2n bp + 32)):bytes32) + LENGTH vs*stride < dimword (:256)` by
    (simp[] >> decide_tac) >>
  qpat_x_assum `dop = Var xd0` SUBST_ALL_TAC >>
  drule_all (Q.INST [`delta` |-> `LENGTH vs*stride`, `n` |-> `stride`] address_add_offset) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`xd`,`t`,`Gf`,`tf`] strip_assume_tac)) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)` by
    metis_tac[gas_origin_ptr_path_trans] >>
  `typed_copy_state_frame a 0 0 s t` by
    (`ci_mono a a2` by metis_tac[ci_mono_trans] >>
     `typed_copy_state_frame a 0 0 q1 q2 /\ typed_copy_state_frame a 0 0 q2 t` by
       metis_tac[typed_copy_state_frame_mono] >>
     metis_tac[typed_copy_state_frame_trans]) >>
  qexistsl_tac [`xd`,`t`,`Gf`,`tf`] >> simp[] >>
  rpt strip_tac >> metis_tac[]
QED
