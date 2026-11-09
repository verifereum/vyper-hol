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

Theorem typed_copy_sarray_empty_slow_frag_mem[local]:
  compile_copy_sarray_typed cenv dst dty src sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = 0 /\ type_memory_bytes cenv sty = 0 /\
  is_abi_dynamic cenv.ce_struct_fields dty /\ N < dimword (:256) /\
  (!dst src sa sb s dw sw.
    compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw ==>
    frag_exec_mem ctx sa sb (\u. u = s)
      (\t. t.vs_memory = s.vs_memory /\ typed_copy_state_frame sa (w2n dw) 0 s t) (\r. F)) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw ==>
  frag_exec_mem ctx sa sb (\u. u = s)
    (\t. t.vs_memory = s.vs_memory /\ typed_copy_state_frame sa (w2n dw) 0 s t) (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gnvs[] >>
  rename1 `fresh_label "typed_sa_cond" sa = (hdr,l1)` >>
  rename1 `fresh_label "typed_sa_body" l1 = (blabel,l2)` >>
  rename1 `fresh_label "typed_sa_exit" l2 = (exit,l3)` >>
  rename1 `fresh_var l3 = (counter,init)` >>
  rename1 `emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0)` >>
  rename1 `emit_inst JMP [Label hdr] [] st0 = ((),st1)` >>
  rename1 `new_block hdr st1 = (u1,sth)` >>
  rename1 `emit_op LT [Var counter; Lit (n2w N)] sth = (lt,h1)` >>
  rename1 `emit_op ISZERO [lt] h1 = (done,stj)` >>
  rename1 `emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2)` >>
  rename1 `new_block blabel st2 = (u2,stb)` >>
  rename1 `emit_inst ASSIGN [_] [counter] _ = ((),ste)` >>
  rename1 `emit_inst JMP [Label hdr] [] ste = ((),st3)` >>
  rename1 `new_block exit st3 = (u3,stx)` >>
  drule_all (SRULE [type_memory_size_def] (Q.INST
    [`dtv` |-> `TupleTV []`, `stv` |-> `TupleTV []`]
    (SPEC_ALL typed_copy_sarray_slow_layout))) >> strip_tac >>
  qmatch_goalsub_abbrev_tac `frag_exec_mem ctx sa stx P Q R` >>
  qabbrev_tac `Inv = \k t. k <= N /\ lookup_var counter t = SOME (n2w k) /\
    t.vs_memory = s.vs_memory /\ typed_copy_state_frame sa (w2n dw) 0 s t` >>
  qabbrev_tac `J = \k t. Inv k t /\ eval_operand done t = SOME (if k < N then 0w else 1w)` >>
  suspend "compose"
QED

Resume typed_copy_sarray_empty_slow_frag_mem[compose]:
  `frag_exec_mem ctx init st0 P (Inv 0) R` by
    (simp[Abbr `P`, Abbr `Inv`, Abbr `R`] >>
     `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
     drule_all typed_copy_assign_frag_mem >> disch_then (qspec_then `ctx` mp_tac) >>
     disch_then (mp_then Any irule frag_exec_mem_conseq) >>
     simp[Abbr `Q`, typed_copy_state_frame_def] >> metis_tac[]) >>
  `frag_exec_mem ctx sa st0 P (Inv 0) R` by
    (qpat_x_assum `frag_exec_mem _ init _ _ _ _` mp_tac >>
     simp[frag_exec_mem_def, fragExecTheory.fn_has_code_def,
          fragExecTheory.emitted_blocks_def]) >>
  `frag_exec_mem ctx st0 stx (Inv 0) (J N) R` by suspend "loop" >>
  `cs_extends sa st0 /\ cs_extends st0 stx` by metis_tac[ci_mono_def] >>
  drule_all frag_exec_mem_seq >>
  disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >>
  simp[Abbr `J`, Abbr `Inv`, Abbr `Q`]
QED

Resume typed_copy_sarray_empty_slow_frag_mem[loop]:
  irule frag_exec_loop_mem >> conj_tac
  >- (simp[Abbr `Inv`, Abbr `Q`, typed_copy_state_frame_jump,
           typed_copy_lookup_var_jump] >> simp[jump_to_def]) >>
  conj_tac
  >- (simp[Abbr `J`, Abbr `Inv`, Abbr `Q`, typed_copy_state_frame_jump,
           typed_copy_lookup_var_jump, typed_copy_eval_operand_jump] >>
      simp[jump_to_def]) >>
  qexistsl_tac [`blabel`, `done`, `exit`, `hdr`] >>
  goal_assum (drule_at (Pat `new_block exit _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JMP _ _ ste = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JMP _ _ st0 = _`)) >>
  goal_assum (drule_at (Pat `new_block hdr _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `new_block blabel _ = _`)) >> simp[] >>
  conj_tac
  >- (simp[Abbr `J`] >> rpt strip_tac >> gvs[] >> Cases_on `k < N` >> simp[]) >>
  reverse conj_tac >- suspend "header" >>
  rpt strip_tac >>
  irule frag_exec_mem_conseq >>
  irule_at Any typed_copy_empty_index_body_mem >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  qpat_assum `emit_op ADD [dst;_] _ = _` (irule_at (Pat `emit_op ADD _ _ = _`)) >>
  qpat_assum `emit_op ADD [src;_] _ = _` (irule_at (Pat `emit_op ADD _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_op MUL _ _ = _`)) >>
  simp[] >>
  qexistsl_tac [`sw`, `sa`, `s`, `k`, `dw`, `N`] >>
  simp[Abbr `Inv`, Abbr `J`, Abbr `R`] >> gvs[]
QED

Resume typed_copy_sarray_empty_slow_frag_mem[header]:
  rpt strip_tac >> simp[Abbr `J`, Abbr `R`] >>
  irule frag_exec_mem_pointwise >> qx_gen_tac `t` >> strip_tac >>
  `lookup_var counter t = SOME (n2w k)` by gvs[Abbr `Inv`] >>
  drule_all typed_copy_header_frag_mem >>
  disch_then (qspecl_then [`ctx`, `w2n dw`, `0`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >>
  rpt strip_tac >> simp[Abbr `Inv`] >> conj_tac
  >- metis_tac[typed_copy_state_frame_counter] >>
  simp[Abbr `Q`] >> conj_tac >- gvs[] >>
  irule typed_copy_state_frame_trans >> qexists_tac `t` >>
  simp[] >> conj_tac >- gvs[] >>
  irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >> simp[]
QED

Finalise typed_copy_sarray_empty_slow_frag_mem

Theorem typed_copy_sarray_empty_frag_mem:
  compile_copy_sarray_typed cenv dst dty src sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = 0 /\ type_memory_bytes cenv sty = 0 /\
  N < dimword (:256) /\
  (!dst src sa sb s dw sw.
    compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw ==>
    frag_exec_mem ctx sa sb (\u. u = s)
      (\t. t.vs_memory = s.vs_memory /\ typed_copy_state_frame sa (w2n dw) 0 s t) (\r. F)) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw ==>
  frag_exec_mem ctx sa sb (\u. u = s)
    (\t. t.vs_memory = s.vs_memory /\ typed_copy_state_frame sa (w2n dw) 0 s t) (\r. F)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_abi_dynamic cenv.ce_struct_fields dty`
  >- (irule typed_copy_sarray_empty_slow_frag_mem >>
      goal_assum (drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)) >>
      simp[] >> goal_assum (drule_at Any)) >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, compile_copy_memory_zero] >>
  strip_tac >> gvs[] >> irule frag_exec_mem_refl >> simp[]
QED
