Theory lowerDloadSafetyPublicCopy
Ancestors
  lowerDloadPublicCopyPointEffect
  lowerDloadOracleCallAssembly lowerDloadExternalBoundary
  lowerDloadSafetyWriteAssembly lowerDloadSafetyReadCoverage
  lowerDloadSafetyAccountReadEffects lowerDloadSafetyAllocBounds
  lowerDloadSafetyAmbient lowerDloadSafetyUpdates lowerDloadSafetyValues
  lowerDloadSafetyKernel lowerDloadSafetyRelation ptrDiscipline
  lowerDloadSafetyAssemblyPremises contextCodegenRel codegenRel memLocDefs pointerConfinedDefs venomWf venomInst venomExecSemantics venomState
  finite_map pred_set list words arithmetic

(* Preserve the qualified exports while sharing the pointwise implementation. *)
Theorem ld_public_copy_scalar_nonpointer:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  ((MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY] /\
    inst.inst_operands = [dst;src;len] /\ MEM op [src;len]) \/
   (inst.inst_opcode = EXTCODECOPY /\
    inst.inst_operands = [addr;dst;src;len] /\ MEM op [addr;src;len])) /\
  op = Var v ==> v NOTIN fn_pv P fn
Proof
  ACCEPT_TAC lowerDloadPublicCopyPointEffectTheory.ld_public_copy_scalar_nonpointer
QED

Theorem ld_public_copy_scalar_equal:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\
  taint_ok f.lf_fn tn inst f.lf_src /\ tn.t_var = f.lf_tv /\
  ((MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY] /\
    inst.inst_operands = [dst;src;len] /\ MEM op [src;len]) \/
   (inst.inst_opcode = EXTCODECOPY /\
    inst.inst_operands = [addr;dst;src;len] /\ MEM op [addr;src;len])) ==>
  eval_operand op f.lf_src = eval_operand op f.lf_tgt
Proof
  ACCEPT_TAC lowerDloadPublicCopyPointEffectTheory.ld_public_copy_scalar_equal
QED

Theorem ld_public_copy_steps:
  ld_nonghost tn s t /\
  ((MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY] /\
    inst.inst_operands = [dst;src;len]) \/
   (inst.inst_opcode = EXTCODECOPY /\
    inst.inst_operands = [addr;dst;src;len] /\
    eval_operand addr s = eval_operand addr t)) /\
  eval_operand dst s = SOME x /\ eval_operand dst t = SOME y /\
  eval_operand src s = eval_operand src t /\
  eval_operand len s = eval_operand len t /\
  step_inst_base inst t = OK ts ==>
  ?off n xs. eval_operand src s = SOME off /\
    eval_operand len s = SOME n /\ LENGTH xs = w2n n /\
    ts = write_memory_with_expansion (w2n y) xs t /\
    step_inst_base inst s = OK (write_memory_with_expansion (w2n x) xs s)
Proof
  ACCEPT_TAC lowerDloadPublicCopyPointEffectTheory.ld_public_copy_steps
QED

Theorem ld_public_copy_dispatch:
  MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] /\
  step_inst_base inst t = OK ts ==>
  ?dst src len addr y.
    ((MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY] /\
      inst.inst_operands = [dst;src;len]) \/
     (inst.inst_opcode = EXTCODECOPY /\
      inst.inst_operands = [addr;dst;src;len])) /\
    eval_operand dst t = SOME y
Proof
  ACCEPT_TAC lowerDloadPublicCopyPointEffectTheory.ld_public_copy_dispatch
QED

Theorem ld_public_copy_operands:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\
  taint_ok f.lf_fn tn inst f.lf_src /\ tn.t_var = f.lf_tv /\
  ld_nonghost tn f.lf_src f.lf_tgt /\
  MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] /\
  step_inst_base inst f.lf_tgt = OK ts ==>
  ?dst src len addr x y off n xs.
    ((MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY] /\
      inst.inst_operands = [dst;src;len]) \/
     (inst.inst_opcode = EXTCODECOPY /\
      inst.inst_operands = [addr;dst;src;len])) /\
    eval_operand dst f.lf_src = SOME x /\
    eval_operand dst f.lf_tgt = SOME y /\
    eval_operand src f.lf_src = SOME off /\
    eval_operand len f.lf_src = SOME n /\ LENGTH xs = w2n n /\
    (op_prov f.lf_H dst = NONE ==> x = y) /\
    (!k. op_prov f.lf_H dst = SOME k ==> ld_wordrel A (SOME k) x y) /\
    ts = write_memory_with_expansion (w2n y) xs f.lf_tgt /\
    step_inst_base inst f.lf_src =
      OK (write_memory_with_expansion (w2n x) xs f.lf_src)
Proof
  ACCEPT_TAC lowerDloadPublicCopyPointEffectTheory.ld_public_copy_operands
QED

Theorem ld_public_copy_taint:
  MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] /\
  inst.inst_outputs = [] /\ 2 < LENGTH inst.inst_operands /\
  source_memory_write_ranges inst s = [(ro,LENGTH xs)] ==>
  step_taint inst s (write_memory_with_expansion ro xs s) tn =
    tn with t_mem := tn.t_mem DIFF {ro+j | j < LENGTH xs}
Proof
  ACCEPT_TAC lowerDloadPublicCopyPointEffectTheory.ld_public_copy_taint
QED

Theorem ld_public_copy_write_range:
  ((MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY] /\
    inst.inst_operands = [dst;src;len]) \/
   (inst.inst_opcode = EXTCODECOPY /\
    inst.inst_operands = [addr;dst;src;len])) /\
  eval_operand dst s = SOME x /\ eval_operand src s = SOME off /\
  eval_operand len s = SOME n /\ step_inst_base inst s = OK ss ==>
  source_memory_write_ranges inst s = [(w2n x,w2n n)] /\
  ?ops. mem_write_ops inst = SOME ops /\ ops.iao_ofst = dst
Proof
  ACCEPT_TAC lowerDloadPublicCopyPointEffectTheory.ld_public_copy_write_range
QED

Theorem ld_public_copy_effect:
  (xs = [] \/ (ro = rt /\ ro+LENGTH xs <= lo) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     ro = b+delta /\ rt = c+delta /\ delta+LENGTH xs <= sz) \/
   (ro = rt /\ fl <= ro)) /\
  lo <= fl /\ (!a u v z. FLOOKUP A a = SOME (u,v,z) ==> u+z <= fl /\ v+z <= fl) /\
  ld_dyn_agree fl tn.t_mem f.lf_src.vs_memory f.lf_tgt.vs_memory /\
  ld_vars P A f /\ tn.t_var = f.lf_tv /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\ ld_nonghost tn f.lf_src f.lf_tgt /\
  ld_global lo A frames /\ FDOM A = ld_slots A frames /\
  EVERY (ld_maps A) frames /\
  MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] /\
  inst.inst_outputs = [] /\ 2 < LENGTH inst.inst_operands /\
  source_memory_write_ranges inst f.lf_src = [(ro,LENGTH xs)] /\
  step_inst_base inst f.lf_src = OK (write_memory_with_expansion ro xs f.lf_src) /\
  ts = write_memory_with_expansion rt xs f.lf_tgt /\
  (!a. a IN FRANGE f.lf_H ==> a IN FDOM A) ==>
  ?ss H'. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts; lf_H := H';
      lf_tv := (step_taint inst f.lf_src ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
    step_prov PG (ld_erase A o_f f.lf_H) inst ss = ld_erase A o_f H' /\
    ld_dyn_agree fl (step_taint inst f.lf_src ss tn).t_mem ss.vs_memory ts.vs_memory /\
    (!a. a IN FRANGE H' ==> a IN FDOM A) /\
    ss.vs_allocas = f.lf_src.vs_allocas /\ ts.vs_allocas = f.lf_tgt.vs_allocas /\
    ss.vs_alloca_next = f.lf_src.vs_alloca_next /\ ts.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    ss.vs_current_bb = f.lf_src.vs_current_bb /\ ts.vs_current_bb = f.lf_tgt.vs_current_bb /\
    ss.vs_prev_bb = f.lf_src.vs_prev_bb /\ ts.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
    ss.vs_inst_idx = f.lf_src.vs_inst_idx /\ ts.vs_inst_idx = f.lf_tgt.vs_inst_idx
Proof
  ACCEPT_TAC lowerDloadPublicCopyPointEffectTheory.ld_public_copy_effect
QED

Theorem ld_sync_public_copy_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  mem_inv dload_headroom_ok C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  ~in_revert_forward fn s /\ t.vs_alloca_next < dimword(:256) /\
  MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] /\
  step_inst fuel C' inst t = OK ts ==>
  ?ss H'. step_inst fuel C inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts; lf_H := H';
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss ts /\
    ld_nonghost (step_taint inst s ss tn) ss ts /\
    step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q) (ld_erase A o_f f.lf_H)
      inst ss = ld_erase A o_f H' /\
    ld_dyn_agree (dyn_floor C vs0) (step_taint inst s ss tn).t_mem
      ss.vs_memory ts.vs_memory /\
    (!a. a IN FRANGE H' ==> a IN FDOM A) /\
    ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
    ss.vs_alloca_next = s.vs_alloca_next /\ ts.vs_alloca_next = t.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
    ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb /\
    ss.vs_inst_idx = s.vs_inst_idx /\ ts.vs_inst_idx = t.vs_inst_idx
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all ld_sync_taint_ok >> strip_tac >>
  drule_all ld_sync_access_ok >> strip_tac >>
  drule ld_sync_slots >> strip_tac >>
  drule ld_sync_maps >> strip_tac >>
  `EVERY (ld_maps A) (f::fs)` by simp[] >>
  drule_all ld_sync_dyn_floor >> strip_tac >>
  `f.lf_tgt = t` by (drule ld_sync_active >> simp[]) >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by
    (drule ld_alloc_target_no_wrap >> simp[] >> metis_tac[]) >>
  drule_all ld_sync_public_copy_effect_at >> disch_then ACCEPT_TAC
QED
