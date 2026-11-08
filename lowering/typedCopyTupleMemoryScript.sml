(* Joint memory execution of heterogeneous typed field copies. *)
Theory typedCopyTupleMemory
Ancestors
  typedCopyControlMemory typedMemoryCopy fragExecMem
  context compileEnv emitHelper exprLoweringProps
  venomExecSemantics venomState valueEncoding words list arithmetic

Theorem typed_copy_state_frame_frontier[local]:
  typed_copy_state_frame sa off len s t ==>
  t.vs_alloca_next = s.vs_alloca_next
Proof
  simp[typed_copy_state_frame_def, venom_state_component_equality]
QED

Theorem typed_copy_entry_offset_frag_mem:
  !cenv ctx dty sty dtv stv v dst src doff soff sa s1 s2 sb dp sp s dw sw.
  (!dst src sa sb s dw sw.
    compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    w2n sw + type_memory_size stv <= s.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= s.vs_alloca_next ==>
    frag_exec_mem ctx sa sb (\u. u = s)
      (\t. val_in_memory dtv v (w2n dw) t.vs_memory /\
           typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t) (\r. F)) /\
  compile_with_byte_offset dst doff sa = (dp,s1) /\
  compile_with_byte_offset src soff s1 = (sp,s2) /\
  compile_store_memory_typed cenv dp dty sp sty s2 = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  val_in_memory stv v (w2n sw + soff) s.vs_memory /\
  w2n sw + soff + type_memory_size stv < dimword (:256) /\
  w2n dw + doff + type_memory_size dtv < dimword (:256) /\
  (w2n sw + soff + type_memory_size stv <= w2n dw + doff \/
   w2n dw + doff + type_memory_size dtv <= w2n sw + soff) /\
  w2n sw + soff + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + doff + type_memory_size dtv <= s.vs_alloca_next ==>
  frag_exec_mem ctx sa sb (\u. u = s)
    (\t. val_in_memory dtv v (w2n dw + doff) t.vs_memory /\
         typed_copy_state_frame sa (w2n dw + doff) (type_memory_size dtv) s t) (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by metis_tac[typed_copy_offset_mono] >>
  `ci_mono s2 sb` by metis_tac[cj 1 ci_mono_typed_memory_family, pairTheory.SND] >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\
   cs_extends s1 sb /\ cs_extends s2 sb` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `w2n (dw + n2w doff) = w2n dw + doff /\
   w2n (sw + n2w soff) = w2n sw + soff` by
    (conj_tac >> irule typed_copy_offset_nonwrap >> decide_tac) >>
  `(!x. dp = Var x ==> not_fresh_at s1 x) /\
   (!x. dp = Var x ==> not_fresh_at s2 x) /\
   (!x. sp = Var x ==> not_fresh_at s2 x)` by
    metis_tac[typed_copy_offset_fresh, typed_copy_operand_fresh_mono] >>
  qpat_assum `compile_with_byte_offset dst _ _ = _`
    (mp_then Any mp_tac typed_copy_offset_frag_mem) >>
  disch_then (drule_at Any) >>
  disch_then (qspecl_then [`ctx`, `w2n dw + doff`, `type_memory_size dtv`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_mem_then) >>
  simp[] >> rpt strip_tac >>
  `eval_operand src t = SOME sw` by
    (drule_all typed_copy_state_frame_operand >> simp[]) >>
  qpat_assum `compile_with_byte_offset src _ _ = _`
    (mp_then Any mp_tac typed_copy_offset_frag_mem) >>
  disch_then (drule_at Any) >>
  disch_then (qspecl_then [`ctx`, `w2n dw + doff`, `type_memory_size dtv`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_mem_then) >>
  simp[ci_mono_def] >> rpt strip_tac >>
  `eval_operand dp t' = SOME (dw + n2w doff)` by
    (drule_all typed_copy_state_frame_operand >> simp[]) >>
  `t'.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[typed_copy_state_frame_frontier] >>
  qpat_x_assum `!dst src sa sb s dw sw. _` mp_tac >>
  disch_then drule >>
  disch_then (qspecl_then [`t'`, `dw + n2w doff`, `sw + n2w soff`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[ADD_COMM]) >>
  disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >>
  rpt strip_tac >>
  irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
  irule typed_copy_state_frame_mono >> qexists_tac `s1` >> simp[] >>
  irule typed_copy_state_frame_trans >> qexists_tac `t'` >> simp[] >>
  metis_tac[typed_copy_state_frame_mono]
QED
