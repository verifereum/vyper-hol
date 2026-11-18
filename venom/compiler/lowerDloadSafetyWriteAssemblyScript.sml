(* Reachable memory-write consumers. *)
Theory lowerDloadSafetyWriteAssembly
Ancestors
  lowerDloadMemoryWritePointEffect[qualified]
  lowerDloadSafetyAssemblyPremises lowerDloadSafetyRelation lowerDloadSafetyValues
  lowerDloadSafetyAmbient
  codegenRel contextCodegenRel venomWf ptrDiscipline pointerConfinedDefs memLocDefs venomInst venomExecSemantics venomState finite_map list pred_set

(* Compatibility exports for the operand facts used by write consumers. *)
Theorem ld_write_value_nonpointer:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [MSTORE;MSTORE8;ISTORE] /\
  inst.inst_operands = [a;Var v] ==> v NOTIN fn_pv P fn
Proof
  ACCEPT_TAC lowerDloadMemoryWritePointEffectTheory.ld_write_value_nonpointer
QED

Theorem ld_copy_length_nonpointer:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [a;b;Var v] ==>
  v NOTIN fn_pv P fn
Proof
  ACCEPT_TAC lowerDloadMemoryWritePointEffectTheory.ld_copy_length_nonpointer
QED

Theorem ld_write_operand_observation:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ MEM inst (fn_insts f.lf_fn) /\
  ~MEM inst.inst_opcode [ASSIGN;PHI;RET;RETFMP;DRET] /\ MEM op inst.inst_operands /\
  tn.t_var = f.lf_tv /\
  eval_operand op f.lf_src = SOME x /\ eval_operand op f.lf_tgt = SOME y ==>
  (op_prov f.lf_H op = NONE ==> word_agree_except (op_taint tn op) x y) /\
  (!a. op_prov f.lf_H op = SOME a ==> ld_wordrel A (SOME a) x y)
Proof
  ACCEPT_TAC lowerDloadMemoryWritePointEffectTheory.ld_write_operand_observation
QED

Theorem ld_write_operand_defined:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  MEM inst (fn_insts f.lf_fn) /\ MEM op inst.inst_operands /\
  eval_operand op f.lf_tgt = SOME y ==>
  ?x. eval_operand op f.lf_src = SOME x
Proof
  ACCEPT_TAC lowerDloadMemoryWritePointEffectTheory.ld_write_operand_defined
QED

Theorem ld_vars_unselected:
  ld_vars P A f /\ v NOTIN fn_pv P f.lf_fn ==>
  FLOOKUP f.lf_H v = NONE
Proof
  ACCEPT_TAC lowerDloadMemoryWritePointEffectTheory.ld_vars_unselected
QED

Theorem ld_write_scalar_observation:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ MEM inst (fn_insts f.lf_fn) /\
  ~MEM inst.inst_opcode [ASSIGN;PHI;RET;RETFMP;DRET] /\ MEM op inst.inst_operands /\
  tn.t_var = f.lf_tv /\
  eval_operand op f.lf_src = SOME x /\ eval_operand op f.lf_tgt = SOME y /\
  op_prov f.lf_H op = NONE ==>
  word_agree_except (op_taint tn op) x y
Proof
  ACCEPT_TAC lowerDloadMemoryWritePointEffectTheory.ld_write_scalar_observation
QED

Theorem ld_write_address_observation:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ MEM inst (fn_insts f.lf_fn) /\
  ~MEM inst.inst_opcode [ASSIGN;PHI;RET;RETFMP;DRET] /\ MEM op inst.inst_operands /\
  tn.t_var = f.lf_tv /\
  eval_operand op f.lf_src = SOME x /\ eval_operand op f.lf_tgt = SOME y /\
  op_taint tn op = {} ==>
  (op_prov f.lf_H op = NONE ==> x=y) /\
  (!a. op_prov f.lf_H op = SOME a ==> ld_wordrel A (SOME a) x y)
Proof
  ACCEPT_TAC lowerDloadMemoryWritePointEffectTheory.ld_write_address_observation
QED

Theorem ld_write_access_classified:
  access_ok lo (ld_erase A o_f H) fn inst s /\
  ~in_revert_forward fn s /\ mem_write_ops inst = SOME ops /\
  MEM (w2n x,n) (source_memory_write_ranges inst s) /\ 0 < n /\
  (op_prov H ops.iao_ofst = NONE ==> x = y) /\
  (!a. op_prov H ops.iao_ofst = SOME a ==> ld_wordrel A (SOME a) x y) /\
  (!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)) ==>
  (w2n x+n <= lo /\ y=x) \/
  (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
    w2n x=b+delta /\ w2n y=c+delta /\ delta+n <= sz)
Proof
  strip_tac >> drule_all ld_write_access_cases >> metis_tac[]
QED

Theorem ld_read_access_classified:
  access_ok lo (ld_erase A o_f H) fn inst s /\
  ~in_revert_forward fn s /\ mem_read_ops inst = SOME ops /\
  MEM (w2n x,n) (source_memory_read_ranges inst s) /\ 0 < n /\
  (op_prov H ops.iao_ofst = NONE ==> x = y) /\
  (!a. op_prov H ops.iao_ofst = SOME a ==> ld_wordrel A (SOME a) x y) /\
  (!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)) ==>
  (w2n x+n <= lo /\ y=x) \/
  (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
    w2n x=b+delta /\ w2n y=c+delta /\ delta+n <= sz)
Proof
  strip_tac >> drule_all ld_read_access_cases >> metis_tac[]
QED

Theorem ld_write2_operands:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  MEM inst (fn_insts f.lf_fn) /\ inst_wf inst /\
  MEM inst.inst_opcode [MSTORE;MSTORE8;ISTORE] /\
  step_inst_base inst f.lf_tgt = OK ts ==>
  ?a v dst dst' x y. inst.inst_operands = [a;v] /\
    inst.inst_outputs = [] /\
    eval_operand a f.lf_src = SOME dst /\
    eval_operand a f.lf_tgt = SOME dst' /\
    eval_operand v f.lf_src = SOME x /\
    eval_operand v f.lf_tgt = SOME y
Proof
  ACCEPT_TAC lowerDloadMemoryWritePointEffectTheory.ld_write2_operands
QED

Theorem ld_write2_taint:
  taint_ok fn tn inst s /\ MEM inst.inst_opcode [MSTORE;MSTORE8;ISTORE] /\
  inst.inst_operands = [a;v] ==>
  op_taint tn a = {} /\ (inst.inst_opcode = MSTORE8 ==> op_taint tn v = {})
Proof
  ACCEPT_TAC lowerDloadMemoryWritePointEffectTheory.ld_write2_taint
QED
Theorem ld_sync_memory_write_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ f.lf_src = s /\ f.lf_tgt = t /\ f.lf_fn = fn /\
  ptr_discipline lo C vs0 /\ fn_shape_ok fn /\ fn_inst_wf fn /\
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs0 /\
  s.vs_labels = t.vs_labels /\ ~in_revert_forward fn s /\
  t.vs_alloca_next < dimword(:256) /\
  MEM inst.inst_opcode [MSTORE;MSTORE8;MCOPY] /\
  step_inst fuel C' inst t = OK ts ==>
  ?ss. step_inst fuel C inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts;
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss ts /\
    ld_nonghost (step_taint inst s ss tn) ss ts /\
    step_prov PG G inst ss = G /\
    ld_dyn_agree (dyn_floor C vs0) (step_taint inst s ss tn).t_mem
      ss.vs_memory ts.vs_memory /\
    ss.vs_allocas = s.vs_allocas /\ ss.vs_alloca_next = s.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ss.vs_prev_bb = s.vs_prev_bb /\
    ss.vs_inst_idx = s.vs_inst_idx /\
    ts.vs_allocas = t.vs_allocas /\ ts.vs_alloca_next = t.vs_alloca_next /\
    ts.vs_current_bb = t.vs_current_bb /\ ts.vs_prev_bb = t.vs_prev_bb /\
    ts.vs_inst_idx = t.vs_inst_idx /\
    (!a. a IN FRANGE f.lf_H ==> a IN FDOM A)
Proof
  strip_tac >>
  `access_ok lo G fn inst s` by metis_tac[ld_sync_access_ok] >>
  `taint_ok fn tn inst s` by metis_tac[ld_sync_taint_ok] >>
  `FDOM A = ld_slots A (f::fs) /\ EVERY (ld_maps A) (f::fs)` by
    (qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ld_sync_def] >> simp[EVERY_MEM] >>
     strip_tac >> metis_tac[]) >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by
    (drule ld_alloc_target_no_wrap >> simp[] >> metis_tac[]) >>
  drule_all ld_sync_dyn_floor >> strip_tac >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==>
     b+sz <= dyn_floor C vs0 /\ c+sz <= dyn_floor C vs0 /\ c+sz < dimword(:256)` by
    metis_tac[] >>
  drule_all lowerDloadMemoryWritePointEffectTheory.ld_sync_memory_write_effect_at >> simp[]
QED
