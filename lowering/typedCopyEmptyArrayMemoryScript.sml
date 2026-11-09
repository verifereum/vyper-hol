Theory typedCopyEmptyArrayMemory
Ancestors
  typedCopyEmptyMemory typedCopyIndexMemory typedCopyControlMemory typedMemoryCopy
  fragExecMem fragLoopMemory fragExec context contextProps compileEnv emitHelper
  exprLoweringProps venomExecSemantics venomState valueEncoding words list arithmetic

Theorem typed_copy_empty_index_child_mem[local]:
  emit_op MUL [Var counter; Lit 0w] a = (so,b) /\
  emit_op MUL [Var counter; Lit 0w] b = (doff,c) /\
  emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
  compile_store_memory_typed cenv dp dty sp sty e = ((),z) /\
  (!dst src sa sb s dw sw.
    compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw ==>
    frag_exec_mem ctx sa sb (\u. u = s)
      (\t. t.vs_memory = s.vs_memory /\ typed_copy_state_frame sa (w2n dw) 0 s t) (\r. F)) /\
  not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw ==>
  frag_exec_mem ctx a z (\u. u = s)
    (\t. t.vs_memory = s.vs_memory /\ typed_copy_state_frame a (w2n dw) 0 s t) (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e` by
    metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono e z` by metis_tac[cj 1 ci_mono_typed_memory_family, pairTheory.SND] >>
  `ci_mono a e` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `(!x. sp = Var x ==> not_fresh_at e x) /\
   (!x. dp = Var x ==> not_fresh_at e x)` by
    metis_tac[typed_copy_emit_op_fresh, typed_copy_operand_fresh_mono] >>
  drule_all (SRULE [] (Q.INST [`ss` |-> `0`, `ds` |-> `0`]
    (SPEC_ALL typed_copy_index_addresses_frag_mem))) >>
  disch_then (qspecl_then [`w2n dw`, `0`, `ctx`] mp_tac) >> simp[] >>
  disch_then (mp_then Any irule frag_exec_mem_then) >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      qpat_x_assum `!dst src sa sb s dw sw. _` (drule_then mp_tac) >>
      disch_then (qspecl_then [`t`, `dw`, `sw`] mp_tac) >> simp[] >>
      disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >>
      rpt strip_tac >> irule typed_copy_state_frame_trans >> qexists_tac `t` >>
      simp[] >> irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[ci_mono_def]
QED

Theorem typed_copy_empty_index_body_mem[local]:
  emit_op MUL [Var counter; Lit 0w] a = (so,b) /\
  emit_op MUL [Var counter; Lit 0w] b = (doff,c) /\
  emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
  compile_store_memory_typed cenv dp dty sp sty e = ((),z) /\
  emit_op ADD [Var counter; Lit 1w] z = (inc,z1) /\
  emit_inst ASSIGN [inc] [counter] z1 = ((),endst) /\
  (!dst src sa sb s dw sw.
    compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw ==>
    frag_exec_mem ctx sa sb (\u. u = s)
      (\t. t.vs_memory = s.vs_memory /\ typed_copy_state_frame sa (w2n dw) 0 s t) (\r. F)) /\
  ci_mono sa a /\ not_fresh_at a counter /\ ~not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME sw /\ eval_operand dst s0 = SOME dw /\
  N < dimword (:256) /\ k < N ==>
  frag_exec_mem ctx a endst
    (\s. k <= N /\ lookup_var counter s = SOME (n2w k) /\
         s.vs_memory = s0.vs_memory /\ typed_copy_state_frame sa (w2n dw) 0 s0 s)
    (\s. SUC k <= N /\ lookup_var counter s = SOME (n2w (SUC k)) /\
         s.vs_memory = s0.vs_memory /\ typed_copy_state_frame sa (w2n dw) 0 s0 s) (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e /\ ci_mono e z` by
    metis_tac[typed_copy_emit_op_mono, cj 1 ci_mono_typed_memory_family, pairTheory.SND] >>
  `ci_mono a z /\ ci_mono sa z` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `not_fresh_at z counter /\
   (!x. src = Var x ==> not_fresh_at a x) /\
   (!x. dst = Var x ==> not_fresh_at a x)` by
    (conj_tac
     >- (gvs[ci_mono_def, not_fresh_at_def] >> decide_tac) >>
     metis_tac[typed_copy_operand_fresh_mono]) >>
  irule frag_exec_mem_pointwise >> qx_gen_tac `s` >> strip_tac >>
  `eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `frag_exec_mem ctx a z (\u. u = s)
    (\t. t.vs_memory = s.vs_memory /\ typed_copy_state_frame a (w2n dw) 0 s t) (\r. F)` by
    (irule typed_copy_empty_index_child_mem >>
     goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
     qpat_assum `emit_op ADD [dst;doff] d = _`
       (irule_at (Pat `emit_op ADD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op MUL _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op MUL _ _ = _`)) >> simp[] >> metis_tac[]) >>
  drule frag_exec_mem_then >> disch_then irule >> conj_tac
  >- (simp[] >> rpt strip_tac >> suspend "increment") >>
  conj_tac >- gvs[ci_mono_def] >>
  `ci_mono z z1` by metis_tac[typed_copy_emit_op_mono] >>
  `cs_extends z z1` by gvs[ci_mono_def] >>
  `cs_extends z1 endst` by metis_tac[cs_extends_emit_inst] >>
  metis_tac[cs_extends_trans]
QED

Resume typed_copy_empty_index_body_mem[increment]:
  `lookup_var counter t = SOME (n2w k)` by
    metis_tac[typed_copy_state_frame_counter] >>
  `k + 1 < dimword (:256)` by decide_tac >>
  drule_all typed_copy_counter_increment_frame_frag_mem >>
  disch_then (qspecl_then [`w2n dw`, `0`, `ctx`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[ADD1] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  irule typed_copy_state_frame_trans >> qexists_tac `s` >> simp[] >>
  irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
  irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >> simp[]
QED

Finalise typed_copy_empty_index_body_mem
