(* Uniform recursive element step and scalar backedge boundaries. *)
Theory fullStoreSlotsElementStep
Ancestors
  fullStoreSlotsElementAddress fullStoreSlotsElements fullStoreSlotsMemberFrame
  fullStoreSlotsMembers
  typedCopyOriginPtrBase fragGasOriginPtr context emitHelper exprLoweringProps
  loweringStateRelDefs compileEnv venomState ptrDiscipline venomInst
  finite_map list arithmetic words stateFrame stmtLoweringMono
  typedMemoryCopy fragExec pair

Theorem store_slots_element_backedge_origin_ptr:
  emit_op ADD [Var cv;Lit 1w] a = (Var inc,b) /\
  emit_inst ASSIGN [Var inc] [cv] b = ((),c) /\
  emit_inst JMP [Label hdr] [] c = ((),d) /\
  not_fresh_at a cv /\ lookup_var cv s = SOME (n2w j) /\
  FLOOKUP G cv = NONE /\ op_taint tn (Var cv) = {} /\
  j < n /\ n < dimword(:256) /\ fn_has_code a d func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s ==>
  inc <> cv /\ j+1 < dimword(:256) /\
  (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to hdr (update_var cv (n2w (j+1))
      (update_var inc (n2w (j+1)) s))),
     DRESTRICT (DRESTRICT G (COMPL {inc})) (COMPL {cv}),
     tn with t_var := (tn.t_var |+ (inc,{})) |+ (cv,{})))
Proof
  strip_tac >>
  drule_all typed_copy_origin_ptr_counter_backedge_path >>
  disch_then (fn th => assume_tac th >>
    qspecl_then [`ARB`,`ARB`,`ARB`] strip_assume_tac th) >>
  gvs[] >> rpt gen_tac >>
  first_x_assum (qspecl_then [`explicit`,`PG`,`D`] strip_assume_tac) >> gvs[]
QED

Theorem store_slots_element_backedge_frame:
  t = jump_to hdr (update_var cv w (update_var inc w s)) /\
  Gf = DRESTRICT (DRESTRICT G (COMPL {inc})) (COMPL {cv}) /\
  tf = tn with t_var := (tn.t_var |+ (inc,{})) |+ (cv,{}) ==>
  execution_frame t = execution_frame s /\
  tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
  lookup_var cv t = SOME w /\ FLOOKUP Gf cv = NONE /\
  op_taint tf (Var cv) = {} /\
  t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
  t.vs_halted = s.vs_halted /\
  (!p. p <> cv /\ p <> inc ==>
    lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> gvs[] >>
  simp[execution_frame_def,jump_to_def,update_var_def,lookup_var_def,
    FLOOKUP_UPDATE,FLOOKUP_DRESTRICT,op_taint_def] >>
  rpt strip_tac >> simp[FLOOKUP_UPDATE,FLOOKUP_DRESTRICT]
QED

Theorem store_slots_element_body_code:
  emit_op MUL [Var cv;Lit (n2w ms)] sa = (Var so,sb) /\
  emit_op ADD [Var xs;Var so] sb = (Var sp,sc) /\
  emit_op MUL [Var cv;Lit (n2w slots)] sc = (Var off,sd) /\
  emit_op ADD [dst;Var off] sd = (Var dp,se) /\
  compile_store_slots cenv (Var sp) (Var dp) ty tr se = ((),sf) /\
  emit_op ADD [Var cv;Lit 1w] sf = (Var inc,sg) /\
  emit_inst ASSIGN [Var inc] [cv] sg = ((),sh) /\
  emit_inst JMP [Label hdr] [] sh = ((),si) /\
  fn_has_code sa si func ==>
  fn_has_code sa se func /\ fn_has_code se sf func /\
  fn_has_code sf si func /\
  (!p. not_fresh_at sa p ==> not_fresh_at se p /\
    not_fresh_at sf p /\ p <> inc)
Proof
  strip_tac >>
  `ci_mono sa sb /\ ci_mono sb sc /\ ci_mono sc sd /\
   ci_mono sd se /\ ci_mono se sf /\ ci_mono sf sg /\
   ci_mono sg sh /\ ci_mono sh si` by
    (metis_tac[typed_copy_emit_op_mono,ci_mono_emit_inst,
      cj 1 ci_mono_compile_store_slots,SND]) >>
  `cs_extends sa se /\ cs_extends se sf /\ cs_extends sf si` by
    metis_tac[ci_mono_def,cs_extends_trans] >>
  `fn_has_code sa se func /\ fn_has_code se sf func /\
   fn_has_code sf si func` by metis_tac[fn_has_code_split,cs_extends_trans] >>
  simp[] >> rpt strip_tac >>
  `not_fresh_at se p /\ not_fresh_at sf p` by
    metis_tac[ci_mono_def,freshWritesTheory.not_fresh_at_mono,LESS_EQ_TRANS] >>
  simp[] >> drule store_slots_add_code >> strip_tac >> gvs[]
QED
