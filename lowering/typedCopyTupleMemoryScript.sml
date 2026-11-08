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

Theorem typed_copy_tuple_frag_mem:
  !dtys stys dtvs stvs vs dst src doff soff sa sb s dw sw.
    LENGTH stys = LENGTH dtys /\ LENGTH dtvs = LENGTH dtys /\
    LENGTH stvs = LENGTH dtys /\ LENGTH vs = LENGTH dtys /\
    (!i. i < LENGTH dtys ==>
      type_memory_bytes cenv (EL i dtys) = type_memory_size (EL i dtvs) /\
      type_memory_bytes cenv (EL i stys) = type_memory_size (EL i stvs) /\
      (!dst src sa sb s dw sw.
        compile_store_memory_typed cenv dst (EL i dtys) src (EL i stys) sa = ((),sb) /\
        (!x. dst = Var x ==> not_fresh_at sa x) /\
        (!x. src = Var x ==> not_fresh_at sa x) /\
        eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
        val_in_memory (EL i stvs) (EL i vs) (w2n sw) s.vs_memory /\
        w2n sw + type_memory_size (EL i stvs) < dimword (:256) /\
        w2n dw + type_memory_size (EL i dtvs) < dimword (:256) /\
        (w2n sw + type_memory_size (EL i stvs) <= w2n dw \/
         w2n dw + type_memory_size (EL i dtvs) <= w2n sw) /\
        w2n sw + type_memory_size (EL i stvs) <= s.vs_alloca_next /\
        w2n dw + type_memory_size (EL i dtvs) <= s.vs_alloca_next ==>
        frag_exec_mem ctx sa sb (\u. u = s)
          (\t. val_in_memory (EL i dtvs) (EL i vs) (w2n dw) t.vs_memory /\
               typed_copy_state_frame sa (w2n dw)
                 (type_memory_size (EL i dtvs)) s t) (\r. F))) /\
    tuple_val_wf vs stvs /\ tuple_val_wf vs dtvs /\
    compile_typed_copy_fields cenv dst src dtys stys doff soff sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
    tuple_in_memory vs stvs (w2n sw + soff) s.vs_memory /\
    w2n sw + soff + type_memory_size_list stvs < dimword (:256) /\
    w2n dw + doff + type_memory_size_list dtvs < dimword (:256) /\
    (w2n sw + soff + type_memory_size_list stvs <= w2n dw + doff \/
     w2n dw + doff + type_memory_size_list dtvs <= w2n sw + soff) /\
    w2n sw + soff + type_memory_size_list stvs <= s.vs_alloca_next /\
    w2n dw + doff + type_memory_size_list dtvs <= s.vs_alloca_next ==>
    frag_exec_mem ctx sa sb (\u. u = s)
      (\t. tuple_in_memory vs dtvs (w2n dw + doff) t.vs_memory /\
           typed_copy_state_frame sa (w2n dw + doff)
             (type_memory_size_list dtvs) s t) (\r. F)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[compile_store_memory_typed_def, comp_return_def,
          val_in_memory_def, type_memory_size_def] >>
      irule frag_exec_mem_refl >> simp[]) >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `stys` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
  gnvs[] >>
  qpat_assum `!i. i < SUC _ ==> _` (qspec_then `0` mp_tac) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  suspend "cons"
QED

Resume typed_copy_tuple_frag_mem[cons]:
  rename1 `compile_typed_copy_fields cenv dst src (dty::dtys) (sty::stys) doff soff sa = ((),sb)` >>
  rename1 `tuple_in_memory (v::vs) (stv::stvs) _ _` >>
  qmatch_goalsub_rename_tac `tuple_in_memory (v::vs) (dtv::dtvs) _ _` >>
  gnvs[val_wf_def, val_in_memory_def, type_memory_size_def] >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  simp[comp_ignore_bind_def, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rpt (qpat_x_assum `_ /\ _` strip_assume_tac) >>
  rename1 `compile_store_memory_typed cenv dst_ptr dty src_ptr sty cs'' = (u,sc)` >>
  Cases_on `u` >> suspend "head"
QED

Resume typed_copy_tuple_frag_mem[head]:
  `ci_mono sa sc /\ ci_mono sc sb` by
    (qpat_x_assum `!stys dtvs stvs vs dst src doff soff sa sb s dw sw. _` kall_tac >>
     `ci_mono sa cs' /\ ci_mono cs' cs''` by metis_tac[typed_copy_offset_mono] >>
     `ci_mono cs'' sc` by metis_tac[cj 1 ci_mono_typed_memory_family, pairTheory.SND] >>
     `ci_mono sc sb` by metis_tac[cj 2 ci_mono_typed_memory_family, pairTheory.SND] >>
     gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  qpat_assum `compile_with_byte_offset dst _ _ = _`
    (mp_then (Pat `compile_with_byte_offset _ _ _ = _`) mp_tac
      typed_copy_entry_offset_frag_mem) >>
  disch_then (drule_at (Pat `compile_with_byte_offset src _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  qpat_x_assum `!dst src sa sb s dw sw. _`
    (assume_tac o ONCE_REWRITE_RULE [ADD_COMM]) >>
  disch_then drule >>
  disch_then (qspecl_then [`s`, `dw`, `sw`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >>
  disch_then (mp_then Any irule frag_exec_mem_then) >>
  `cs_extends sa sc /\ cs_extends sc sb` by gvs[ci_mono_def] >>
  simp[] >> rpt strip_tac >> suspend "suffix"
QED

Resume typed_copy_tuple_frag_mem[suffix]:
  qpat_x_assum `compile_with_byte_offset dst _ _ = _` kall_tac >>
  qpat_x_assum `compile_with_byte_offset src _ _ = _` kall_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `!dst src sa sb s dw sw. _` kall_tac >>
  qpat_x_assum `val_in_memory stv _ _ _` kall_tac >>
  `tuple_in_memory vs stvs (soff + (type_memory_size stv + w2n sw)) t.vs_memory` by
    (irule typed_copy_tuple_frame >> simp[] >>
     qexistsl_tac [`doff + w2n dw`, `type_memory_size dtv`, `s.vs_memory`] >>
     gvs[typed_copy_state_frame_def]) >>
  `eval_operand dst t = SOME dw /\ eval_operand src t = SOME sw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `(!x. dst = Var x ==> not_fresh_at sc x) /\
   (!x. src = Var x ==> not_fresh_at sc x)` by
    metis_tac[typed_copy_operand_fresh_mono] >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[typed_copy_state_frame_frontier] >>
  qpat_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` (fn th =>
    qpat_x_assum `!stys dtvs stvs vs dst src doff soff sa sb s dw sw. _`
      (fn ih => mp_then (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)
        mp_tac ih th)) >>
  disch_then (qspecl_then [`dtvs`, `stvs`, `vs`] mp_tac) >>
  disch_then (qspecl_then [`t`, `dw`, `sw`] mp_tac) >>
  (impl_tac >- (simp[] >> gen_tac >> strip_tac >>
    qpat_assum `!i. i < SUC _ ==> _` (qspec_then `SUC i` mp_tac) >>
    disch_then (mp_tac o SIMP_RULE (srw_ss()) []) >>
    disch_then drule >> strip_tac >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (mp_then Any irule frag_exec_mem_conseq) >>
  simp[] >> rpt strip_tac
  >- suspend "preserve_head" >> suspend "frames"
QED

Resume typed_copy_tuple_frag_mem[preserve_head]:
  irule typed_copy_frame_preserves_source >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`type_memory_size_list dtvs`,
    `doff + (type_memory_size dtv + w2n dw)`, `t.vs_memory`] >>
  fs[typed_copy_state_frame_def] >> decide_tac
QED

Resume typed_copy_tuple_frag_mem[frames]:
  irule typed_copy_state_frame_trans >> qexists_tac `t` >>
  conj_tac
  >- (irule typed_copy_state_frame_subinterval >>
      qexistsl_tac [`doff + w2n dw`, `type_memory_size dtv`] >> simp[]) >>
  irule typed_copy_state_frame_mono >> qexists_tac `sc` >> simp[] >>
  irule typed_copy_state_frame_subinterval >>
  qexistsl_tac [`doff + (type_memory_size dtv + w2n dw)`,
    `type_memory_size_list dtvs`] >> simp[]
QED

Finalise typed_copy_tuple_frag_mem
