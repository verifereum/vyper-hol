Theory stmtSimCustomErrorMemCopyLoop
Ancestors
  stmtSimCustomErrorMemCopyInterface stmtSimCustomErrorMemCopyPrimitive placeTypedCopyRecursivePath
  placeTypedCopyPath typedMemoryCopy fragGasMode fragGasPathMem
  context emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs
  valueEncoding valueEncodingDefs valueEncodingProps valueCopy venomState venomExecSemantics
  words list arithmetic pair memSafeRun venomMemDefs contextCodegenRel fragExec placeCopyControlPath

Theorem typed_copy_index_child_checked:
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] a = (so,b) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b = (doff,c) /\
  emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
  compile_store_memory_typed cenv dp dty sp sty e = ((),z) /\
  typed_copy_checked_entry cenv ctx dty sty dtv stv v /\ not_fresh_at a counter /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  lookup_var counter s = SOME (n2w k) /\ k < dimword (:256) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  val_in_memory stv v (w2n sw + k * type_memory_size stv) s.vs_memory /\
  w2n sw + k * type_memory_size stv + type_memory_size stv < dimword (:256) /\
  w2n dw + k * type_memory_size dtv + type_memory_size dtv < dimword (:256) /\
  w2n sw + k * type_memory_size stv + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + k * type_memory_size dtv + type_memory_size dtv <= s.vs_alloca_next /\
  (w2n sw + k * type_memory_size stv + type_memory_size stv <=
     w2n dw + k * type_memory_size dtv \/
   w2n dw + k * type_memory_size dtv + type_memory_size dtv <=
     w2n sw + k * type_memory_size stv) /\
  fn_has_code a z func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw + k * type_memory_size dtv) t.vs_memory /\
      typed_copy_state_frame a (w2n dw + k * type_memory_size dtv)
        (type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = z.cs_current_bb /\
      t.vs_inst_idx = LENGTH z.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e` by
    metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono e z` by metis_tac[cj 1 ci_mono_typed_memory_family, pairTheory.SND] >>
  `ci_mono a e` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `cs_extends a e /\ cs_extends e z` by gvs[ci_mono_def] >>
  `fn_has_code a e func /\ fn_has_code e z func` by metis_tac[fn_has_code_split] >>
  `w2n (sw + n2w (k * type_memory_size stv)) = w2n sw + k * type_memory_size stv /\
   w2n (dw + n2w (k * type_memory_size dtv)) = w2n dw + k * type_memory_size dtv` by
    (conj_tac >> irule typed_copy_offset_nonwrap >> decide_tac) >>
  `(!x. sp = Var x ==> not_fresh_at e x) /\
   (!x. dp = Var x ==> not_fresh_at e x)` by
    metis_tac[typed_copy_emit_op_fresh, typed_copy_operand_fresh_mono] >>
  drule_all typed_copy_index_addresses_checked >>
  disch_then (qspecl_then [`w2n dw + k * type_memory_size dtv`,
                          `type_memory_size dtv`, `ctx`] strip_assume_tac) >>
  suspend "child"
QED

Resume typed_copy_index_child_checked[child]:
  `alloca_inv t` by
    (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
         typed_copy_state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  drule typed_copy_checked_entry_run >> disch_then drule >>
  disch_then (qspecl_then [`sw + n2w (k * type_memory_size stv)`, `t`, `func`,
                          `dw + n2w (k * type_memory_size dtv)`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[] >>
  `typed_copy_state_frame a (w2n dw + k * type_memory_size dtv)
     (type_memory_size dtv) s t'` by
    (irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
     irule typed_copy_state_frame_mono >> qexists_tac `e` >> simp[]) >>
  gvs[gas_marked_path_def] >>
  qpat_assum `gas_path_mem ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_path_mem_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `t'` >> simp[]
QED

Finalise typed_copy_index_child_checked

Theorem typed_copy_index_body_checked:
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] a = (so,b) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b = (doff,c) /\
  emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
  compile_store_memory_typed cenv dp dty sp sty e = ((),z) /\
  emit_op ADD [Var counter; Lit 1w] z = (inc,z1) /\
  emit_inst ASSIGN [inc] [counter] z1 = ((),endst) /\
  ci_mono sa a /\ not_fresh_at a counter /\ ~not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!i. i < N ==> typed_copy_checked_entry cenv ctx dty sty dtv stv (f i) /\
                   val_wf stv (f i) /\ val_wf dtv (f i)) /\
  N < dimword (:256) /\ k < N /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  w2n sw + N * type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + N * type_memory_size dtv <= s.vs_alloca_next /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k s /\
  fn_has_code a endst func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 (SUC k) t /\
      ~t.vs_halted /\ t.vs_current_bb = endst.cs_current_bb /\
      t.vs_inst_idx = LENGTH endst.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e /\ ci_mono e z /\
   ci_mono z z1 /\ ci_mono z1 endst` by
    metis_tac[typed_copy_emit_op_mono, cj 1 ci_mono_typed_memory_family,
              ci_mono_emit_inst, pairTheory.SND] >>
  `ci_mono a z /\ ci_mono sa z /\ ci_mono z endst` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `cs_extends a z /\ cs_extends z endst` by gvs[ci_mono_def] >>
  `fn_has_code a z func /\ fn_has_code z endst func` by metis_tac[fn_has_code_split] >>
  `not_fresh_at z counter /\
   (!x. src = Var x ==> not_fresh_at a x) /\
   (!x. dst = Var x ==> not_fresh_at a x)` by
    (conj_tac
     >- (gvs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
     conj_tac >> metis_tac[typed_copy_operand_fresh_mono]) >>
  suspend "copy"
QED

Resume typed_copy_index_body_checked[copy]:
  `w2n sw <= w2n sw + k * type_memory_size stv /\
   w2n sw + k * type_memory_size stv + type_memory_size stv <=
     w2n sw + N * type_memory_size stv` by metis_tac[typed_copy_array_subinterval] >>
  `w2n dw <= w2n dw + k * type_memory_size dtv /\
   w2n dw + k * type_memory_size dtv + type_memory_size dtv <=
     w2n dw + N * type_memory_size dtv` by metis_tac[typed_copy_array_subinterval] >>
  `lookup_var counter s = SOME (n2w k) /\
   eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
   val_in_memory stv (f k) (w2n sw + k * type_memory_size stv) s.vs_memory` by
    gvs[typed_copy_index_inv_def] >>
  `k < dimword (:256) /\ k + 1 < dimword (:256)` by decide_tac >>
  `typed_copy_checked_entry cenv ctx dty sty dtv stv (f k)` by metis_tac[] >>
  `w2n sw + k * type_memory_size stv + type_memory_size stv < dimword (:256) /\
   w2n dw + k * type_memory_size dtv + type_memory_size dtv < dimword (:256)` by decide_tac >>
  `?t. gas_marked_path T ctx func s 0 (OK t) /\
       val_in_memory dtv (f k) (w2n dw + k * type_memory_size dtv) t.vs_memory /\
       typed_copy_state_frame a (w2n dw + k * type_memory_size dtv)
         (type_memory_size dtv) s t /\
       ~t.vs_halted /\ t.vs_current_bb = z.cs_current_bb /\
       t.vs_inst_idx = LENGTH z.cs_current_insts /\
       alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next` by
    (irule typed_copy_index_child_checked >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op MUL _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op MUL _ _ = _`)) >>
     qexists_tac `sw` >> simp[] >> decide_tac) >>
  suspend "increment"
QED

Resume typed_copy_index_body_checked[increment]:
  `lookup_var counter t = SOME (n2w k)` by
    metis_tac[typed_copy_state_frame_counter] >>
  `alloca_inv t` by
    (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
         typed_copy_state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  drule_all typed_copy_counter_increment_checked >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `typed_copy_state_frame sa (w2n dw + k * type_memory_size dtv)
     (type_memory_size dtv) t t'` by
    (simp[typed_copy_state_frame_def] >> rpt strip_tac >>
     first_x_assum irule >> gvs[ci_mono_def, not_fresh_at_def] >> decide_tac) >>
  `typed_copy_state_frame sa (w2n dw + k * type_memory_size dtv)
     (type_memory_size dtv) s t` by
    (irule typed_copy_state_frame_mono >> qexists_tac `a` >> simp[]) >>
  `eval_operand src t' = SOME sw /\ eval_operand dst t' = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 (SUC k) t'` by
    (irule typed_copy_index_inv_step >> simp[ADD1] >>
     qexists_tac `s` >> simp[] >>
     irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[]) >>
  gvs[gas_marked_path_def] >>
  qpat_assum `gas_path_mem ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_path_mem_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `t'` >> simp[]
QED

Finalise typed_copy_index_body_checked

Theorem typed_copy_index_header_branch_checked:
  emit_op LT [Var counter; length] a = (lt,b) /\
  emit_op ISZERO [lt] b = (done,c) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] c = ((),d) /\
  ci_mono sa a /\ not_fresh_at a counter /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k s /\
  eval_operand length s = SOME (n2w N) /\ N < dimword (:256) /\
  fn_has_code a d func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t /\
      ~t.vs_halted /\ t.vs_inst_idx = 0 /\
      t.vs_current_bb = (if k = N then exit else blabel) /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d` by
    metis_tac[typed_copy_emit_op_mono, ci_mono_emit_inst, pairTheory.SND] >>
  `cs_extends a c /\ cs_extends c d` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code a c func /\ fn_has_code c d func` by
    metis_tac[fn_has_code_split] >>
  `k <= N /\ lookup_var counter s = SOME (n2w k)` by
    gvs[typed_copy_index_inv_def] >>
  drule_all typed_copy_header_checked >>
  disch_then (qspecl_then [`w2n dw`, `N * type_memory_size dtv`, `ctx`]
    strip_assume_tac) >>
  `typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t` by
    (irule typed_copy_index_inv_preserve >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all typed_copy_branch_checked >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_assum `gas_path_mem ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_path_mem_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `jump_to (if (if k < N then 0w else 1w) = 0w then blabel else exit) t` >>
  simp[gas_marked_path_def, typed_copy_index_inv_jump, jump_to_def] >>
  Cases_on `k < N` >> gvs[jump_to_def]
QED

Theorem typed_copy_index_loop_checked:
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  emit_inst JMP [Label hdr] [] st0 = ((),st1) /\
  new_block hdr st1 = (u1,sth) /\
  emit_op LT [Var counter; length] sth = (lt,h1) /\
  emit_op ISZERO [lt] h1 = (done,stj) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2) /\
  new_block blabel st2 = (u2,stb) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] stb = (so,b1) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b1 = (doff,b2) /\
  emit_op ADD [src;so] b2 = (sp,b3) /\
  emit_op ADD [dst;doff] b3 = (dp,b4) /\
  compile_store_memory_typed cenv dp dty sp sty b4 = ((),b5) /\
  emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6) /\
  emit_inst ASSIGN [inc] [counter] b6 = ((),ste) /\
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\
  new_block exit st3 = (u3,stx) /\
  ci_mono sa init /\ ci_mono sa st0 /\ ci_mono sa sth /\ ci_mono sa stb /\
  ci_mono init st0 /\ ci_mono st0 stx /\
  cs_extends sth stj /\ cs_extends stb ste /\
  ~not_fresh_at sa counter /\ not_fresh_at sth counter /\
  not_fresh_at stb counter /\
  sa.cs_current_bb = init.cs_current_bb /\
  sa.cs_current_insts = init.cs_current_insts /\ sa.cs_blocks = init.cs_blocks /\
  (!x. length = Var x ==> not_fresh_at sa x) /\
  eval_operand length s = SOME (n2w N) /\ N < dimword (:256) /\
  (!i. i < N ==> typed_copy_checked_entry cenv ctx dty sty dtv stv (f i) /\
                   val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  w2n sw + N * type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + N * type_memory_size dtv <= s.vs_alloca_next /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  fn_has_code sa stx func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      (!i. i < N ==> val_in_memory dtv (f i)
         (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
      typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = stx.cs_current_bb /\
      t.vs_inst_idx = LENGTH stx.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> suspend "slices"
QED

Resume typed_copy_index_loop_checked[slices]:
  `cs_extends st0 st1 /\ cs_extends stj st2 /\ cs_extends ste st3` by
    metis_tac[ci_mono_emit_inst, ci_mono_def, pairTheory.SND] >>
  `cs_extends st1 sth /\ cs_extends st2 stb /\ cs_extends st3 stx` by
    metis_tac[ci_mono_new_block, ci_mono_def, pairTheory.SND] >>
  `cs_extends stb stx` by metis_tac[cs_extends_trans] >>
  `cs_extends stj stx` by metis_tac[cs_extends_trans] >>
  `cs_extends sa init /\ cs_extends sa st0 /\ cs_extends sa sth /\
   cs_extends sa stb` by gvs[ci_mono_def] >>
  `fn_has_code init st0 func /\ fn_has_code st0 st1 func /\
   fn_has_code sth st2 func /\ fn_has_code stb ste func /\
   fn_has_code ste st3 func` by
    (rpt conj_tac >> irule fn_has_code_mid >>
     (conj_tac >- metis_tac[ci_mono_def, cs_extends_trans]) >>
     qexistsl_tac [`stx`, `sa`] >> simp[] >>
     metis_tac[cs_extends_trans]) >>
  `sth.cs_current_bb = hdr /\ sth.cs_current_insts = [] /\
   stb.cs_current_bb = blabel /\ stb.cs_current_insts = [] /\
   stx.cs_current_bb = exit /\ stx.cs_current_insts = []` by
    gvs[new_block_def] >> suspend "init"
QED

Resume typed_copy_index_loop_checked[init]:
  `s.vs_current_bb = init.cs_current_bb /\
   s.vs_inst_idx = LENGTH init.cs_current_insts` by simp[] >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  drule_all typed_copy_assign_checked >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t` by
    (gvs[typed_copy_state_frame_def, typed_copy_frame_def,
         venom_state_component_equality] >> metis_tac[]) >>
  `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `typed_copy_index_inv sa counter src dst sw dw f stv dtv N s 0 t` by
    simp[typed_copy_index_inv_def, typed_copy_index_prefix_zero] >>
  drule_all typed_copy_jump_checked >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> suspend "iterate"
QED

Resume typed_copy_index_loop_checked[iterate]:
  rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
  qpat_x_assum `emit_inst ASSIGN [Lit 0w] _ _ = _` kall_tac >>
  qpat_x_assum `emit_inst JMP _ _ st0 = _` kall_tac >>
  qabbrev_tac `Inv = \j q. typed_copy_index_inv sa counter src dst sw dw f stv dtv N s j q /\
                         alloca_history func q /\ q.vs_alloca_next = s.vs_alloca_next` >>
  `(!x. src = Var x ==> not_fresh_at sth x) /\
   (!x. dst = Var x ==> not_fresh_at sth x)` by
    metis_tac[typed_copy_operand_fresh_mono] >>
  `!j q. Inv j q ==> alloca_inv q` by
    (rpt strip_tac >>
     gvs[Abbr `Inv`, typed_copy_index_inv_def, alloca_inv_def,
         allocas_non_overlapping_def, alloca_next_valid_def,
         typed_copy_state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  `!j q. j <= N /\ Inv j q /\ ~q.vs_halted /\
     q.vs_current_bb = hdr /\ q.vs_inst_idx = 0 ==>
     ?r. gas_marked_path T ctx func q 0 (OK r) /\ Inv j r /\
         ~r.vs_halted /\ r.vs_inst_idx = 0 /\
         r.vs_current_bb = (if j = N then exit else blabel)` by
    (rpt strip_tac >>
     `eval_operand length q = SOME (n2w N)` by
       (fs[Abbr `Inv`, typed_copy_index_inv_def] >>
        metis_tac[typed_copy_state_frame_operand]) >>
     `alloca_inv q` by metis_tac[] >>
     `typed_copy_index_inv sa counter src dst sw dw f stv dtv N s j q /\
      alloca_history func q /\ q.vs_alloca_next = s.vs_alloca_next` by gvs[Abbr `Inv`] >>
     `q.vs_current_bb = sth.cs_current_bb /\
      q.vs_inst_idx = LENGTH sth.cs_current_insts` by simp[] >>
     drule_all typed_copy_index_header_branch_checked >>
     disch_then (qspec_then `ctx` strip_assume_tac) >>
     qexists_tac `t'` >> simp[Abbr `Inv`]) >> suspend "body"
QED

Resume typed_copy_index_loop_checked[body]:
  `!j q. j < N /\ Inv j q /\ ~q.vs_halted /\
     q.vs_current_bb = blabel /\ q.vs_inst_idx = 0 ==>
     ?r. gas_marked_path T ctx func q 0 (OK r) /\ Inv (j+1) r /\
         ~r.vs_halted /\ r.vs_current_bb = hdr /\ r.vs_inst_idx = 0` by
    (rpt strip_tac >>
     `q.vs_current_bb = stb.cs_current_bb /\
      q.vs_inst_idx = LENGTH stb.cs_current_insts` by simp[] >>
     `typed_copy_index_inv sa counter src dst sw dw f stv dtv N s j q /\
      alloca_history func q /\ q.vs_alloca_next = s.vs_alloca_next` by gvs[Abbr `Inv`] >>
     `alloca_inv q` by metis_tac[] >>
     `w2n sw + N * type_memory_size stv <= q.vs_alloca_next /\
      w2n dw + N * type_memory_size dtv <= q.vs_alloca_next` by simp[] >>
     drule_all typed_copy_index_body_checked >> strip_tac >>
     drule_all typed_copy_jump_checked >>
     disch_then (qspec_then `ctx` strip_assume_tac) >>
     gvs[gas_marked_path_def] >>
     qpat_assum `gas_path_mem ctx func q 0 (OK _)`
       (mp_then Any mp_tac gas_path_mem_then) >>
     disch_then drule >> simp[] >> strip_tac >>
     goal_assum (drule_at Any) >>
     simp[Abbr `Inv`, typed_copy_index_inv_jump, GSYM ADD1] >>
     gvs[jump_to_def]) >> suspend "finish"
QED

Resume typed_copy_index_loop_checked[finish]:
  `Inv 0 (jump_to hdr t)` by
    (simp[Abbr `Inv`] >> simp[typed_copy_index_inv_jump, jump_to_def]) >>
  `?u. gas_marked_path T ctx func (jump_to hdr t) 0 (OK u) /\
       Inv N u /\ ~u.vs_halted /\ u.vs_current_bb = exit /\ u.vs_inst_idx = 0` by
    (irule place_copy_iterate_path >>
     (conj_tac >- simp[jump_to_def]) >>
     (conj_tac >- (qexistsl_tac [`hdr`, `blabel`] >> simp[jump_to_def])) >>
     (conj_tac >- simp[jump_to_def]) >>
     qexistsl_tac [`0`, `N`] >> simp[]) >>
  gvs[gas_marked_path_def] >>
  qpat_assum `gas_path_mem ctx func t 0 (OK (jump_to hdr t))`
    (mp_then Any mp_tac gas_path_mem_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qpat_assum `gas_path_mem ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_path_mem_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `u` >> simp[] >>
  qpat_x_assum `Inv N u` mp_tac >>
  simp[Abbr `Inv`, typed_copy_index_inv_def, typed_copy_index_prefix_complete]
QED

Finalise typed_copy_index_loop_checked

Theorem typed_copy_sarray_slow_checked_path:
  compile_copy_sarray_typed cenv dst dty src sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  ~(type_memory_size dtv = type_memory_size stv /\
    ~is_abi_dynamic cenv.ce_struct_fields dty) /\ N < dimword (:256) /\
  (!i. i < N ==> typed_copy_checked_entry cenv ctx dty sty dtv stv (f i) /\
                   val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  w2n sw + N * type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + N * type_memory_size dtv <= s.vs_alloca_next /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      (!i. i < N ==> val_in_memory dtv (f i)
         (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
      typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gnvs[] >>
  drule_all typed_copy_sarray_slow_layout >> strip_tac >>
  irule typed_copy_index_loop_checked >> simp[eval_operand_def] >>
  qpat_assum `emit_inst ASSIGN [Lit 0w] _ _ = _`
    (irule_at (Pat `emit_inst ASSIGN [Lit 0w] _ _ = _`)) >>
  qpat_assum `emit_op LT _ _ = _` (irule_at (Pat `emit_op LT _ _ = _`)) >>
  qpat_assum `emit_op ISZERO _ _ = _` (irule_at (Pat `emit_op ISZERO _ _ = _`)) >>
  qpat_assum `emit_inst JNZ _ _ _ = _` (irule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _`
    (irule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  rpt (goal_assum (drule_at Any)) >> simp[eval_operand_def]
QED

Theorem typed_copy_sarray_checked_path:
  compile_copy_sarray_typed cenv dst dty src sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  (!i. i < N ==> typed_copy_checked_entry cenv ctx dty sty dtv stv
     (case ALOOKUP kvs i of NONE => default_value stv | SOME v => v)) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  N < dimword (:256) /\
  val_in_memory (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) (w2n sw) s.vs_memory /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  w2n sw + N * type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + N * type_memory_size dtv <= s.vs_alloca_next /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      val_in_memory (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `type_memory_size dtv = type_memory_size stv /\
            ~is_abi_dynamic cenv.ce_struct_fields dty`
  >- suspend "bulk" >>
  drule_all typed_copy_sarray_representation >> strip_tac >>
  `?t. gas_marked_path T ctx func s 0 (OK t) /\
       (!i. i < N ==> val_in_memory dtv
          (case ALOOKUP kvs i of NONE => default_value stv | SOME v => v)
          (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
       typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next` by
    (ho_match_mp_tac typed_copy_sarray_slow_checked_path >> simp[] >> metis_tac[]) >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

Resume typed_copy_sarray_checked_path[bulk]:
  `stv = dtv` by metis_tac[typed_copy_static_widening] >>
  qpat_x_assum `stv = dtv` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >> strip_tac >>
  `N * type_memory_size stv < dimword (:256)` by decide_tac >>
  drule_all compile_copy_memory_checked_path >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[LET_THM] >> strip_tac >>
  qexists_tac `(if N * type_memory_size stv = 0 then s
               else mcopy (w2n dw) (w2n sw) (N * type_memory_size stv) s)
                 with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[gas_marked_path_def] >> suspend "bulk_post"
QED

Resume typed_copy_sarray_checked_path[bulk_post]:
  Cases_on `N * type_memory_size stv = 0`
  >- (gvs[] >>
      (conj_tac
       >- (irule val_in_memory_relocate >> simp[] >>
           qexistsl_tac [`w2n sw`, `0`, `s.vs_memory`] >>
           simp[mem_bytes_at_def, loweringPostsTheory.val_footprint_def, type_memory_size_def]) >>
       simp[typed_copy_state_frame_def, typed_copy_frame_def, venom_state_component_equality,
            lookup_var_def])) >>
  gvs[] >>
  (conj_tac
   >- (irule mcopy_val_in_memory >>
       simp[loweringPostsTheory.val_footprint_def, type_memory_size_def]) >>
   simp[typed_copy_mcopy_state_frame])
QED

Finalise typed_copy_sarray_checked_path
