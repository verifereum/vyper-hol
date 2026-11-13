Theory widenedAssignPtrIndexBody
Ancestors widenedAssignPtrIndexLoop widenedAssignPtrIndexControl
  typedMemoryCopy placeTypedCopyRecursivePath emitHelperProps freshWrites
  fragGasPathPtr fragExec venomState ptrDiscipline finite_map words list
  exprLoweringProps context compileEnv emitHelper

Theorem widened_assign_index_body_counted:
  !cenv ctx D PG fn dtv stv dty sty f N counter src dst
    sa a b c d e z b6 ste so doff sp dp inc.
    emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] a = (so,b) /\
    emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b = (doff,c) /\
    emit_op ADD [src;so] c = (sp,d) /\
    emit_op ADD [dst;doff] d = (dp,e) /\
    compile_store_memory_typed cenv dp dty sp sty e = ((),z) /\
    emit_op ADD [Var counter; Lit 1w] z = (inc,b6) /\
    emit_inst ASSIGN [inc] [counter] b6 = ((),ste) /\
    ci_mono sa a /\ ~not_fresh_at sa counter /\
    (!j H tm u aw bw.
      j < N /\ eval_operand dp u = SOME aw /\ eval_operand sp u = SOME bw /\
      op_taint tm dp = {} /\ op_taint tm sp = {} /\
      (0 < type_memory_size dtv ==> ?x. dp = Var x /\
        ptr_covers H tm x u (type_memory_size dtv)) /\
      (0 < type_memory_size stv ==> ?x. sp = Var x /\
        ptr_covers H tm x u (type_memory_size stv)) /\
      w2n aw + type_memory_size dtv < dimword (:256) /\
      w2n bw + type_memory_size stv < dimword (:256) /\
      (w2n aw + type_memory_size dtv <= w2n bw \/
       w2n bw + type_memory_size stv <= w2n aw) /\
      (!m. mem_agree_outside tm.t_mem u.vs_memory m ==>
        val_in_memory stv (f j) (w2n bw) m) /\
      u.vs_current_bb = e.cs_current_bb /\
      u.vs_inst_idx = LENGTH e.cs_current_insts /\ ~u.vs_halted ==>
      ?H' tm' v.
        gas_path_ptr D 0 ctx fn PG H tm u 0 H' tm' (OK v) /\
        v.vs_current_bb = z.cs_current_bb /\
        v.vs_inst_idx = LENGTH z.cs_current_insts /\ ~v.vs_halted /\
        (!m. mem_agree_outside tm'.t_mem v.vs_memory m ==>
          val_in_memory dtv (f j) (w2n aw) m) /\
        typed_copy_state_frame e (w2n aw) (type_memory_size dtv) u v /\
        (!x. not_fresh_at e x ==> lookup_var x v = lookup_var x u /\
          FLOOKUP H' x = FLOOKUP H x /\
          op_taint tm' (Var x) = op_taint tm (Var x)) /\
        tm'.t_stor = tm.t_stor /\ tm'.t_trans = tm.t_trans /\
        tm'.t_imm = tm.t_imm /\
        (!i. ~(w2n aw <= i /\ i < w2n aw + type_memory_size dtv) ==>
          (i IN tm'.t_mem <=> i IN tm.t_mem))) ==>
    !k G tn s sw dw.
      k < N /\ N < dimword (:256) /\ not_fresh_at a counter /\
      FLOOKUP G counter = NONE /\
      (!x. src = Var x \/ dst = Var x ==> not_fresh_at a x) /\
      lookup_var counter s = SOME (n2w k) /\ op_taint tn (Var counter) = {} /\
      eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
      op_taint tn src = {} /\ op_taint tn dst = {} /\
      w2n sw + N * type_memory_size stv < dimword (:256) /\
      w2n dw + N * type_memory_size dtv < dimword (:256) /\
      (w2n dw + N * type_memory_size dtv <= w2n sw \/
       w2n sw + N * type_memory_size stv <= w2n dw) /\
      (0 < type_memory_size stv ==> ?x. src = Var x /\
        ptr_covers G tn x s (N * type_memory_size stv)) /\
      (0 < type_memory_size dtv ==> ?x. dst = Var x /\
        ptr_covers G tn x s (N * type_memory_size dtv)) /\
      (!i. i < N ==> val_wf dtv (f i) /\ val_wf stv (f i)) /\
      (!i m. i < N /\ mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory stv (f i) (w2n sw + i * type_memory_size stv) m) /\
      (!i m. i < k /\ mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory dtv (f i) (w2n dw + i * type_memory_size dtv) m) /\
      fn_has_code a ste fn /\ 
      ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
      s.vs_current_bb = a.cs_current_bb /\
      s.vs_inst_idx = LENGTH a.cs_current_insts ==>
      ?H tm t.
        gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
        t.vs_current_bb = ste.cs_current_bb /\
        t.vs_inst_idx = LENGTH ste.cs_current_insts /\ ~t.vs_halted /\
        lookup_var counter t = SOME (n2w (k+1)) /\
        FLOOKUP H counter = NONE /\ op_taint tm (Var counter) = {} /\
        (!i m. i < N /\ mem_agree_outside tm.t_mem t.vs_memory m ==>
          val_in_memory stv (f i) (w2n sw + i * type_memory_size stv) m) /\
        (!i m. i < SUC k /\ mem_agree_outside tm.t_mem t.vs_memory m ==>
          val_in_memory dtv (f i) (w2n dw + i * type_memory_size dtv) m) /\
        typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t /\
        (!x. not_fresh_at a x /\ x <> counter ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
          op_taint tm (Var x) = op_taint tn (Var x)) /\
        tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\
        tm.t_imm = tn.t_imm /\
        (!i. ~(w2n dw <= i /\ i < w2n dw + N * type_memory_size dtv) ==>
          (i IN tm.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  qpat_x_assum `!j H tm u aw bw. _` (mk_asm "child") >>
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e /\
   ci_mono e z /\ ci_mono z b6 /\ ci_mono b6 ste` by
    metis_tac[typed_copy_emit_op_mono, ci_mono_typed_memory_family,
              ci_mono_emit_inst, pairTheory.SND] >>
  `ci_mono a z` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  `fn_has_code a z fn /\ fn_has_code z ste fn` by
    (irule fn_has_code_split >> simp[ci_mono_def] >>
     metis_tac[ci_mono_def, cs_extends_trans]) >>
  asm "child" assume_tac >>
  drule_all widened_assign_index_child_counted >>
  strip_tac >>
  asm_x "child" kall_tac >>
  `not_fresh_at z counter` by metis_tac[ci_mono_def, not_fresh_at_mono] >>
  `lookup_var counter t = SOME (n2w k) /\ FLOOKUP H counter = NONE /\
   op_taint tm (Var counter) = {}` by metis_tac[] >>
  drule_all widened_assign_index_increment_counted >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG H tm t 0 H' tm' (OK u)` >>
  `u.vs_memory = t.vs_memory` by
    (qpat_assum `u = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!x. not_fresh_at a x ==> not_fresh_at z x` by
    metis_tac[ci_mono_def, not_fresh_at_mono] >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H' tm' (OK u)` by
    (qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
      (mp_then (Pos hd) mp_tac gas_path_ptr_then) >>
     disch_then drule >> simp[]) >>
  qexistsl_tac [`H'`, `tm'`, `u`] >> simp[] >>
  irule typed_copy_state_frame_trans >> qexists_tac `t` >> conj_tac
  >- metis_tac[typed_copy_state_frame_mono] >>
  simp[typed_copy_state_frame_def, typed_copy_frame_def] >>
  conj_tac
  >- (qpat_assum `u = _` (fn th => once_rewrite_tac[th]) >> simp[NoAsms] >>
      simp[venom_state_component_equality]) >>
  metis_tac[ci_mono_def, not_fresh_at_mono]
QED
