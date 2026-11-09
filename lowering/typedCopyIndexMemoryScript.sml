(* Memory-safe indexed typed-copy steps. *)
Theory typedCopyIndexMemory
Ancestors
  typedCopyControlMemory typedMemoryCopy fragExecMem fragLoopMemory fragExec
  context compileEnv emitHelper exprLoweringProps
  venomExecSemantics venomState valueEncoding words list arithmetic

Theorem typed_copy_index_child_frag_mem:
  !cenv ctx dty sty dtv stv v counter src dst a so b doff c sp d dp e z s sw dw k.
    emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] a = (so,b) /\
    emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b = (doff,c) /\
    emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
    compile_store_memory_typed cenv dp dty sp sty e = ((),z) /\
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
    not_fresh_at a counter /\
    (!x. src = Var x ==> not_fresh_at a x) /\
    (!x. dst = Var x ==> not_fresh_at a x) /\
    lookup_var counter s = SOME (n2w k) /\ k < dimword (:256) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    val_in_memory stv v (w2n sw + k * type_memory_size stv) s.vs_memory /\
    w2n sw + k * type_memory_size stv + type_memory_size stv < dimword (:256) /\
    w2n dw + k * type_memory_size dtv + type_memory_size dtv < dimword (:256) /\
    (w2n sw + k * type_memory_size stv + type_memory_size stv <=
       w2n dw + k * type_memory_size dtv \/
     w2n dw + k * type_memory_size dtv + type_memory_size dtv <=
       w2n sw + k * type_memory_size stv) /\
    w2n sw + k * type_memory_size stv + type_memory_size stv <= s.vs_alloca_next /\
    w2n dw + k * type_memory_size dtv + type_memory_size dtv <= s.vs_alloca_next ==>
    frag_exec_mem ctx a z (\u. u = s)
      (\t. val_in_memory dtv v (w2n dw + k * type_memory_size dtv) t.vs_memory /\
           typed_copy_state_frame a (w2n dw + k * type_memory_size dtv)
             (type_memory_size dtv) s t) (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e` by
    metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono e z` by metis_tac[cj 1 ci_mono_typed_memory_family, pairTheory.SND] >>
  `ci_mono a e` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `w2n (sw + n2w (k * type_memory_size stv)) = w2n sw + k * type_memory_size stv /\
   w2n (dw + n2w (k * type_memory_size dtv)) = w2n dw + k * type_memory_size dtv` by
    (conj_tac >> irule typed_copy_offset_nonwrap >> decide_tac) >>
  `(!x. sp = Var x ==> not_fresh_at e x) /\
   (!x. dp = Var x ==> not_fresh_at e x)` by
    metis_tac[typed_copy_emit_op_fresh, typed_copy_operand_fresh_mono] >>
  drule_all typed_copy_index_addresses_frag_mem >>
  disch_then (qspecl_then [`ctx`, `w2n dw + k * type_memory_size dtv`,
                                    `type_memory_size dtv`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_mem_then) >> conj_tac
  >- (simp[] >> rpt strip_tac >> suspend "child") >>
  gvs[ci_mono_def]
QED

Resume typed_copy_index_child_frag_mem[child]:
  `t.vs_alloca_next = s.vs_alloca_next` by
    gvs[typed_copy_state_frame_def, venom_state_component_equality] >>
  qpat_x_assum `!dst src sa sb s dw sw. _` (drule_then mp_tac) >>
  disch_then (qspecl_then [`t`, `dw + n2w (k * type_memory_size dtv)`,
                                 `sw + n2w (k * type_memory_size stv)`] mp_tac) >>
  simp[] >> disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >>
  rpt strip_tac >> irule typed_copy_state_frame_trans >> qexists_tac `t` >>
  simp[] >> irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >> simp[]
QED

Finalise typed_copy_index_child_frag_mem

Theorem typed_copy_index_header_frag_mem:
  emit_op LT [Var counter; Lit (n2w N)] a = (lt,b) /\
  emit_op ISZERO [lt] b = (done,c) /\ ci_mono sa a /\
  not_fresh_at a counter /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\ N < dimword (:256) ==>
  frag_exec_mem ctx a c
    (typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k)
    (\t. typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t /\
         eval_operand done t = SOME (if k < N then 0w else 1w)) (\r. F)
Proof
  rpt strip_tac >> irule frag_exec_mem_pointwise >> qx_gen_tac `s` >> strip_tac >>
  `k <= N /\ lookup_var counter s = SOME (n2w k)` by
    gvs[typed_copy_index_inv_def] >>
  drule_all typed_copy_header_frag_mem >>
  disch_then (qspecl_then [`ctx`, `w2n dw`, `N * type_memory_size dtv`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >>
  rpt strip_tac >> irule typed_copy_index_inv_preserve >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem typed_copy_index_init_frag_mem:
  fresh_label "typed_sa_cond" sa = (hdr,l1) /\
  fresh_label "typed_sa_body" l1 = (blabel,l2) /\
  fresh_label "typed_sa_exit" l2 = (exit,l3) /\
  fresh_var l3 = (counter,init) /\
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) ==>
  frag_exec_mem ctx sa st0 (\u. u = s)
    (typed_copy_index_inv sa counter src dst sw dw f stv dtv N s 0) (\r. F)
Proof
  rpt strip_tac >>
  `~not_fresh_at sa counter /\ sa.cs_current_bb = init.cs_current_bb /\
   sa.cs_current_insts = init.cs_current_insts /\ sa.cs_blocks = init.cs_blocks` by
    (gvs[fresh_label_def, fresh_var_def, not_fresh_at_def,
         ASCIInumbersTheory.toString_inj]) >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  `frag_exec_mem ctx init st0 (\u. u = s)
     (typed_copy_index_inv sa counter src dst sw dw f stv dtv N s 0) (\r. F)` by
    (drule_all typed_copy_assign_frag_mem >> disch_then (qspec_then `ctx` mp_tac) >>
     disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >>
     rpt strip_tac >> rename1 `lookup_var counter t = SOME 0w` >>
     `typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t` by
       (simp[typed_copy_state_frame_def, typed_copy_frame_def] >> metis_tac[]) >>
     `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
       metis_tac[typed_copy_state_frame_operand] >>
     simp[typed_copy_index_inv_def, typed_copy_index_prefix_zero]) >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_mem_def, fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def]
QED

Theorem typed_copy_index_frontier[local]:
  typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t /\
  k < N /\
  w2n sw + N * type_memory_size stv <= s0.vs_alloca_next /\
  w2n dw + N * type_memory_size dtv <= s0.vs_alloca_next ==>
  w2n sw + k * type_memory_size stv + type_memory_size stv <= t.vs_alloca_next /\
  w2n dw + k * type_memory_size dtv + type_memory_size dtv <= t.vs_alloca_next
Proof
  rpt strip_tac >>
  `t.vs_alloca_next = s0.vs_alloca_next` by
    gvs[typed_copy_index_inv_def, typed_copy_state_frame_def,
        venom_state_component_equality] >>
  metis_tac[typed_copy_array_subinterval, LESS_EQ_TRANS]
QED

Theorem typed_copy_index_body_frag_mem:
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] a = (so,b) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b = (doff,c) /\
  emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
  compile_store_memory_typed cenv dp dty sp sty e = ((),z) /\
  emit_op ADD [Var counter; Lit 1w] z = (inc,z1) /\
  emit_inst ASSIGN [inc] [counter] z1 = ((),endst) /\
  ci_mono sa a /\ not_fresh_at a counter /\ ~not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!i. i < N ==>
    (!dst src sa sb s dw sw.
      compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
      (!x. dst = Var x ==> not_fresh_at sa x) /\
      (!x. src = Var x ==> not_fresh_at sa x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      val_in_memory stv (f i) (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      (w2n sw + type_memory_size stv <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw) /\
      w2n sw + type_memory_size stv <= s.vs_alloca_next /\
      w2n dw + type_memory_size dtv <= s.vs_alloca_next ==>
      frag_exec_mem ctx sa sb (\u. u = s)
        (\t. val_in_memory dtv (f i) (w2n dw) t.vs_memory /\
             typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t) (\r. F)) /\
    val_wf stv (f i) /\ val_wf dtv (f i)) /\
  N < dimword (:256) /\ k < N /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  w2n sw + N * type_memory_size stv <= s0.vs_alloca_next /\
  w2n dw + N * type_memory_size dtv <= s0.vs_alloca_next ==>
  frag_exec_mem ctx a endst
    (typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k)
    (typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 (SUC k)) (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e /\ ci_mono e z` by
    metis_tac[typed_copy_emit_op_mono, cj 1 ci_mono_typed_memory_family, pairTheory.SND] >>
  `ci_mono z z1` by metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono z1 endst` by
    (qspecl_then [`ASSIGN`, `[inc]`, `[counter]`, `z1`] mp_tac ci_mono_emit_inst >> simp[]) >>
  `ci_mono a z /\ ci_mono sa z /\ ci_mono z endst` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `not_fresh_at z counter /\
   (!x. src = Var x ==> not_fresh_at a x) /\
   (!x. dst = Var x ==> not_fresh_at a x)` by
    (conj_tac
     >- (gvs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
     conj_tac >> metis_tac[typed_copy_operand_fresh_mono]) >>
  `w2n sw <= w2n sw + k * type_memory_size stv /\
   w2n sw + k * type_memory_size stv + type_memory_size stv <=
     w2n sw + N * type_memory_size stv` by metis_tac[typed_copy_array_subinterval] >>
  `w2n dw <= w2n dw + k * type_memory_size dtv /\
   w2n dw + k * type_memory_size dtv + type_memory_size dtv <=
     w2n dw + N * type_memory_size dtv` by metis_tac[typed_copy_array_subinterval] >>
  irule frag_exec_mem_pointwise >> qx_gen_tac `s` >> strip_tac >>
  `lookup_var counter s = SOME (n2w k) /\
   eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
   val_in_memory stv (f k) (w2n sw + k * type_memory_size stv) s.vs_memory` by
    gvs[typed_copy_index_inv_def] >>
  `k < dimword (:256) /\ k + 1 < dimword (:256)` by decide_tac >>
  `w2n sw + k * type_memory_size stv + type_memory_size stv <= s.vs_alloca_next /\
   w2n dw + k * type_memory_size dtv + type_memory_size dtv <= s.vs_alloca_next` by
    metis_tac[typed_copy_index_frontier] >>
  `frag_exec_mem ctx a z (\u. u = s)
     (\t. val_in_memory dtv (f k) (w2n dw + k * type_memory_size dtv) t.vs_memory /\
          typed_copy_state_frame a (w2n dw + k * type_memory_size dtv)
            (type_memory_size dtv) s t) (\r. F)` by
    (irule typed_copy_index_child_frag_mem >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op MUL _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op MUL _ _ = _`)) >>
     qexists_tac `sw` >> simp[]
     >- (qpat_x_assum `!i. i < N ==> _` (qspec_then `k` mp_tac) >>
         simp[ADD_COMM] >> metis_tac[]) >> decide_tac) >>
  drule frag_exec_mem_then >> disch_then irule >> conj_tac
  >- (simp[] >> rpt strip_tac >> suspend "increment") >>
  gvs[ci_mono_def]
QED

Resume typed_copy_index_body_frag_mem[increment]:
  `lookup_var counter t = SOME (n2w k)` by
    metis_tac[typed_copy_state_frame_counter] >>
  drule_all typed_copy_counter_increment_frame_frag_mem >>
  disch_then (qspecl_then [`w2n dw + k * type_memory_size dtv`,
                                `type_memory_size dtv`, `ctx`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >>
  rpt strip_tac >>
  `typed_copy_state_frame sa (w2n dw + k * type_memory_size dtv)
     (type_memory_size dtv) s t` by
    (irule typed_copy_state_frame_mono >> qexists_tac `a` >> simp[]) >>
  `eval_operand src s'' = SOME sw /\ eval_operand dst s'' = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  irule typed_copy_index_inv_step >> simp[ADD1] >>
  qexists_tac `s` >> simp[] >>
  irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[]
QED

Finalise typed_copy_index_body_frag_mem

Theorem typed_copy_sarray_slow_frag_mem:
  compile_copy_sarray_typed cenv dst dty src sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  ~(type_memory_size dtv = type_memory_size stv /\
    ~is_abi_dynamic cenv.ce_struct_fields dty) /\
  N < dimword (:256) /\
  (!i. i < N ==>
    (!dst src sa sb s dw sw.
      compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
      (!x. dst = Var x ==> not_fresh_at sa x) /\
      (!x. src = Var x ==> not_fresh_at sa x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      val_in_memory stv (f i) (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      (w2n sw + type_memory_size stv <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw) /\
      w2n sw + type_memory_size stv <= s.vs_alloca_next /\
      w2n dw + type_memory_size dtv <= s.vs_alloca_next ==>
      frag_exec_mem ctx sa sb (\u. u = s)
        (\t. val_in_memory dtv (f i) (w2n dw) t.vs_memory /\
             typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t) (\r. F)) /\
    val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!i. i < N ==> val_in_memory stv (f i)
    (w2n sw + i * type_memory_size stv) s.vs_memory) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  w2n sw + N * type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + N * type_memory_size dtv <= s.vs_alloca_next ==>
  frag_exec_mem ctx sa sb (\u. u = s)
    (\t. (!i. i < N ==> val_in_memory dtv (f i)
       (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
       typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t) (\r. F)
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
  rename1 `emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] stb = (so,b1)` >>
  rename1 `emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b1 = (doff,b2)` >>
  rename1 `emit_op ADD [src;so] b2 = (sp,b3)` >>
  rename1 `emit_op ADD [dst;doff] b3 = (dp,b4)` >>
  rename1 `compile_store_memory_typed cenv dp dty sp sty b4 = ((),b5)` >>
  rename1 `emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6)` >>
  rename1 `emit_inst ASSIGN [inc] [counter] b6 = ((),ste)` >>
  rename1 `emit_inst JMP [Label hdr] [] ste = ((),st3)` >>
  rename1 `new_block exit st3 = (u3,stx)` >>
  drule_all typed_copy_sarray_slow_layout >> strip_tac >>
  `(!x. src = Var x ==> not_fresh_at sth x) /\
   (!x. dst = Var x ==> not_fresh_at sth x)` by
    metis_tac[typed_copy_operand_fresh_mono] >>
  qmatch_goalsub_abbrev_tac `frag_exec_mem ctx sa stx P Q R` >>
  qabbrev_tac `Inv = typed_copy_index_inv sa counter src dst sw dw f stv dtv N s` >>
  qabbrev_tac `J = \k t. Inv k t /\ eval_operand done t = SOME (if k < N then 0w else 1w)` >>
  suspend "compose"
QED

Resume typed_copy_sarray_slow_frag_mem[compose]:
  `frag_exec_mem ctx sa st0 P (Inv 0) R` by
    (simp[Abbr `P`, Abbr `Inv`, Abbr `R`] >>
     irule typed_copy_index_init_frag_mem >> simp[] >>
     goal_assum (drule_at (Pat `fresh_var _ = _`)) >>
     goal_assum (drule_at (Pat `fresh_label "typed_sa_exit" _ = _`)) >>
     goal_assum (drule_at (Pat `fresh_label "typed_sa_body" _ = _`)) >>
     goal_assum (drule_at (Pat `fresh_label "typed_sa_cond" _ = _`)) >> simp[]) >>
  `frag_exec_mem ctx st0 stx (Inv 0) (J N) R` by suspend "loop" >>
  `cs_extends sa st0 /\ cs_extends st0 stx` by metis_tac[ci_mono_def] >>
  drule_all frag_exec_mem_seq >>
  disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >>
  simp[Abbr `J`, Abbr `Inv`, Abbr `Q`, typed_copy_index_inv_def,
       typed_copy_index_prefix_complete]
QED

Resume typed_copy_sarray_slow_frag_mem[loop]:
  irule frag_exec_loop_mem >> conj_tac
  >- simp[Abbr `Inv`, typed_copy_index_inv_jump] >>
  conj_tac
  >- simp[Abbr `J`, Abbr `Inv`, typed_copy_index_inv_jump,
          typed_copy_eval_operand_jump] >>
  qexistsl_tac [`blabel`, `done`, `exit`, `hdr`] >>
  goal_assum (drule_at (Pat `new_block exit _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JMP _ _ ste = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JMP _ _ st0 = _`)) >>
  goal_assum (drule_at (Pat `new_block hdr _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `new_block blabel _ = _`)) >> simp[] >>
  rpt (qpat_x_assum `fresh_label _ _ = _` kall_tac) >>
  qpat_x_assum `fresh_var _ = _` kall_tac >>
  rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_inst JMP _ _ _ = _` kall_tac) >>
  qpat_x_assum `emit_inst JNZ _ _ _ = _` kall_tac >>
  conj_tac
  >- (simp[Abbr `J`] >> rpt strip_tac >> Cases_on `k < N` >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> simp[Abbr `Inv`, Abbr `J`, Abbr `R`] >>
      drule_all (SRULE [ADD_COMM] typed_copy_index_body_frag_mem) >>
      disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[]) >>
  rpt strip_tac >> simp[Abbr `Inv`, Abbr `J`, Abbr `R`] >>
  irule typed_copy_index_header_frag_mem >> simp[] >>
  goal_assum (drule_at (Pat `emit_op ISZERO _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_op LT _ _ = _`)) >> simp[]
QED

Finalise typed_copy_sarray_slow_frag_mem
