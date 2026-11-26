(* Free-element addressing at the successful storage Append guard cursor. *)
Theory bodyAppendSlotAddressMods
Ancestors
  bodyFullStoreSlotsAddresses typedCopyOriginPtrBase typedMemoryCopy
  stmtSimStoreCopy fragGasOriginPtrLoop fragExec exprLoweringProps
  compileEnv freshWrites ptrDiscipline venomState venomInst
  vyperLookupStorage finite_map words

Theorem slot_child_end_bound[local]:
  len < cap /\ w2n (slot:bytes32) + (1 + cap * stride) <= dimword (:256) ==>
  w2n (slot + n2w (1 + len * stride)) + stride <= dimword (:256)
Proof
  strip_tac >> Cases_on `stride = 0`
  >- (simp[] >> irule arithmeticTheory.LESS_IMP_LESS_OR_EQ >> simp[w2n_lt]) >>
  `len * stride + stride <= cap * stride` by simp[array_index_element_end_bound] >>
  `w2n slot + (1 + len * stride) < dimword (:256)` by decide_tac >>
  `w2n (slot + n2w (1 + len * stride)) = w2n slot + (1 + len * stride)` by
    (simp[word_add_def, w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  decide_tac
QED

Theorem slot_operand_kept[local]:
  t.vs_labels = s.vs_labels /\
  (!p. not_fresh_at a p ==> lookup_var p t = lookup_var p s /\
    FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
  (!p. op = Var p ==> not_fresh_at a p) ==>
  eval_operand op t = eval_operand op s /\ op_prov Gf op = op_prov G op /\
  op_taint tf op = op_taint tn op
Proof
  Cases_on `op` >> simp[eval_operand_def, op_prov_def, op_taint_def] >> metis_tac[]
QED

Theorem slot_address_binop[local]:
  emit_op opc [left;right] a = (op,b) /\ fn_has_code a b func /\
  (opc = MUL /\ w = x*y \/ opc = ADD /\ w = x+y) /\
  eval_operand left s = SOME x /\ eval_operand right s = SOME y /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?out t Gf tf.
    op = Var out /\ not_fresh_at b out /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    eval_operand op t = SOME w /\ op_taint tf op = {} /\
    typed_copy_state_frame a 0 0 s t /\ t.vs_memory = s.vs_memory /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_labels = s.vs_labels /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!p. not_fresh_at a p ==> not_fresh_at b p /\
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    (!arg. (!p. arg = Var p ==> not_fresh_at a p) ==>
      eval_operand arg t = eval_operand arg s /\ op_prov Gf arg = op_prov G arg /\
      op_taint tf arg = op_taint tn arg)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all store_address_binop_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choosel_then [`out`,`t`,`Gf`,`tf`] strip_assume_tac)) >>
  `!p. not_fresh_at a p ==> lookup_var p t = lookup_var p s /\
    FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)` by
    (rpt strip_tac >> res_tac) >>
  `typed_copy_state_frame a 0 0 s t` by
    (simp[typed_copy_state_frame_def, typed_copy_frame_def] >>
     qpat_assum `t = _` (fn th => simp[Once th, update_var_def,
       venom_state_component_equality])) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    metis_tac[typed_copy_state_frame_allocas_below_fmp] >>
  `!p. not_fresh_at a p ==> not_fresh_at b p` by
    metis_tac[typed_copy_emit_op_mono, ci_mono_def, freshWritesTheory.not_fresh_at_mono] >>
  qpat_x_assum `t = _` kall_tac >> qpat_x_assum `Gf = _` kall_tac >>
  qpat_x_assum `tf = _` kall_tac >>
  qexistsl_tac [`out`,`t`,`Gf`,`tf`] >> asm_rewrite_tac[] >> conj_tac
  >- (gen_tac >> strip_tac >> simp[]) >>
  rpt gen_tac >> strip_tac >> irule slot_operand_kept >> simp[] >> qexists_tac `a` >> simp[]
QED

Theorem append_slot_address_run_mods:
  emit_op ADD [bop; Lit 1w] s3 = (dop,s4) /\
  emit_op MUL [lop; Lit (n2w stride)] s4 = (off,s5) /\
  emit_op ADD [dop; off] s5 = (pop,s6) /\ fn_has_code s3 s6 func /\
  (!x. bop = Var x \/ lop = Var x ==> not_fresh_at s3 x) /\
  eval_operand bop s = SOME slot /\ eval_operand lop s = SOME (n2w len) /\
  op_taint tn bop = {} /\ op_taint tn lop = {} /\
  len < cap /\ w2n slot + (1 + cap * stride) <= dimword (:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = s3.cs_current_bb /\
  s.vs_inst_idx = LENGTH s3.cs_current_insts ==>
  ?out t Gf tf.
    pop = Var out /\ not_fresh_at s6 out /\
    eval_operand pop t = SOME (slot + n2w (1 + len * stride)) /\ op_taint tf pop = {} /\
    w2n (slot + n2w (1 + len * stride)) + stride <= dimword (:256) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    typed_copy_state_frame s3 0 0 s t /\ store_copy_normalize s t = s /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_labels = s.vs_labels /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    ~t.vs_halted /\ t.vs_current_bb = s6.cs_current_bb /\
    t.vs_inst_idx = LENGTH s6.cs_current_insts /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    eval_operand bop t = SOME slot /\ op_taint tf bop = {} /\
    eval_operand lop t = SOME (n2w len) /\ op_taint tf lop = {} /\
    (!x. not_fresh_at s3 x ==> not_fresh_at s6 x /\ lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!op. (!x. op = Var x ==> not_fresh_at s3 x) ==>
      eval_operand op t = eval_operand op s /\ op_prov Gf op = op_prov G op /\
      op_taint tf op = op_taint tn op)
Proof
  strip_tac >>
  `ci_mono s3 s4 /\ ci_mono s4 s5 /\ ci_mono s5 s6` by
    metis_tac[typed_copy_emit_op_mono] >>
  `cs_extends s3 s4 /\ cs_extends s4 s5 /\ cs_extends s5 s6` by fs[ci_mono_def] >>
  `fn_has_code s3 s4 func /\ fn_has_code s4 s5 func /\ fn_has_code s5 s6 func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `eval_operand (Lit 1w) s = SOME 1w /\ op_taint tn (Lit 1w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `w` |-> `x+y`, `right` |-> `Lit 1w`]
    slot_address_binop)) >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choosel_then [`xd`,`q1`,`G1`,`t1`] strip_assume_tac)) >>
  `!x. lop = Var x ==> not_fresh_at s3 x` by simp[] >>
  `eval_operand lop q1 = SOME (n2w len) /\ op_taint t1 lop = {}` by
    (qpat_assum `!arg. _ ==> eval_operand arg q1 = _ /\ _` (qspec_then `lop` mp_tac) >> simp[]) >>
  `eval_operand (Lit (n2w stride)) q1 = SOME (n2w stride) /\
   op_taint t1 (Lit (n2w stride)) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `MUL`, `w` |-> `x*y`, `s` |-> `q1`]
    slot_address_binop)) >>
  disch_then (qspecl_then [`explicit`,`PG`,`G1`]
    (qx_choosel_then [`xo`,`q2`,`G2`,`t2`] strip_assume_tac)) >>
  `!x. dop = Var x ==> not_fresh_at s4 x` by simp[] >>
  `eval_operand dop q2 = SOME (slot+1w) /\ op_taint t2 dop = {}` by
    (qpat_assum `!arg. _ ==> eval_operand arg q2 = _ /\ _` (qspec_then `dop` mp_tac) >> simp[]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `w` |-> `x+y`, `s` |-> `q2`]
    slot_address_binop)) >>
  disch_then (qspecl_then [`explicit`,`PG`,`G2`]
    (qx_choosel_then [`out`,`t`,`Gf`,`tf`] strip_assume_tac)) >>
  suspend "compose"
QED

Resume append_slot_address_run_mods[compose]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)` by
    metis_tac[gas_origin_ptr_path_trans] >>
  `typed_copy_state_frame s3 0 0 s t` by
    (`ci_mono s3 s5` by metis_tac[ci_mono_trans] >>
     `typed_copy_state_frame s3 0 0 q1 q2 /\ typed_copy_state_frame s3 0 0 q2 t` by
       metis_tac[typed_copy_state_frame_mono] >>
     metis_tac[typed_copy_state_frame_trans]) >>
  `t.vs_memory = s.vs_memory` by simp[] >>
  `store_copy_normalize s t = s` by
    (qpat_assum `typed_copy_state_frame s3 0 0 s t`
       (mp_tac o SIMP_RULE (srw_ss()) [typed_copy_state_frame_def]) >>
     simp[store_copy_normalize_def, venom_state_component_equality]) >>
  `!x. not_fresh_at s3 x ==> not_fresh_at s6 x /\ lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at s3 x ==> not_fresh_at s4 x /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at s4 x ==> not_fresh_at s5 x /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at s5 x ==> not_fresh_at s6 x /\ _` (drule_then strip_assume_tac) >> simp[]) >>
  `!op. (!x. op = Var x ==> not_fresh_at s3 x) ==>
    eval_operand op t = eval_operand op s /\ op_prov Gf op = op_prov G op /\
    op_taint tf op = op_taint tn op` by
    (rpt gen_tac >> strip_tac >> irule slot_operand_kept >> simp[] >>
     qexists_tac `s3` >> simp[] >> gen_tac >> strip_tac >> simp[]) >>
  `eval_operand bop t = SOME slot /\ op_taint tf bop = {} /\
   eval_operand lop t = SOME (n2w len) /\ op_taint tf lop = {}` by
    (qpat_assum `!op. _ ==> eval_operand op t = _ /\ _`
       (fn th => mp_tac (Q.SPEC `bop` th) >> mp_tac (Q.SPEC `lop` th)) >> simp[]) >>
  `slot + 1w + n2w len * n2w stride = slot + n2w (1 + len * stride)` by
    (pure_rewrite_tac[word_mul_n2w, WORD_ADD_ASSOC, GSYM word_add_n2w] >> REFL_TAC) >>
  drule_all_then assume_tac slot_child_end_bound >>
  qexistsl_tac [`out`,`t`,`Gf`,`tf`] >> simp[]
QED

Finalise append_slot_address_run_mods
