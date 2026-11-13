Theory widenedAssignPtrIndexAssembly
Ancestors
  widenedAssignPtrIndexAdmin widenedAssignPtrIndexBody
  widenedAssignPtrIndexControl exprSimPtrTopLevelStorageCopy forPtrRangeEntry
  placeTypedCopyRecursivePath typedMemoryCopy emitHelperProps emitHelper
  compileEnv exprLoweringProps freshWrites fragGasPathPtr fragExec
  venomState venomExecSemantics ptrDiscipline finite_map words list arithmetic

Theorem widened_assign_reserved_operand_frame[local]:
  typed_copy_state_frame sa off len s t /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) ==>
  !op. (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op t = eval_operand op s /\
    op_prov H op = op_prov G op /\ op_taint tm op = op_taint tn op
Proof
  strip_tac >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
     simp[NoAsms, typed_copy_state_frame_def, venom_state_component_equality] >>
     metis_tac[]) >>
  rpt gen_tac >> rpt disch_tac >>
  irule bodyPtrBytestringBuiltinsExternalSliceTheory.reserved_operand_ghost_frame >>
  metis_tac[]
QED

Theorem widened_assign_index_loop_counted:
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  emit_inst JMP [Label hdr] [] st0 = ((),st1) /\
  new_block hdr st1 = (u1,sth) /\
  emit_op LT [Var counter; length] sth = (Var lt,h1) /\
  emit_op ISZERO [Var lt] h1 = (Var done,stj) /\
  emit_inst JNZ [Var done; Label exit; Label blabel] [] stj = ((),st2) /\
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
  (!x. length = Var x \/ src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand length s = SOME (n2w N) /\ N < dimword (:256) /\
  op_taint tn length = {} /\ op_prov G length = NONE /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (0 < type_memory_size stv ==> ?x. src = Var x /\
    ptr_covers G tn x s (N * type_memory_size stv)) /\
  (0 < type_memory_size dtv ==> ?x. dst = Var x /\
    ptr_covers G tn x s (N * type_memory_size dtv)) /\
  (!i. i < N ==> val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (!i m. i < N /\ mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory stv (f i) (w2n sw + i * type_memory_size stv) m) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
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
    u.vs_current_bb = b4.cs_current_bb /\
    u.vs_inst_idx = LENGTH b4.cs_current_insts /\ ~u.vs_halted ==>
    ?H' tm' v.
      gas_path_ptr D 0 ctx fn PG H tm u 0 H' tm' (OK v) /\
      v.vs_current_bb = b5.cs_current_bb /\
      v.vs_inst_idx = LENGTH b5.cs_current_insts /\ ~v.vs_halted /\
      (!m. mem_agree_outside tm'.t_mem v.vs_memory m ==>
        val_in_memory dtv (f j) (w2n aw) m) /\
      typed_copy_state_frame b4 (w2n aw) (type_memory_size dtv) u v /\
      (!x. not_fresh_at b4 x ==> lookup_var x v = lookup_var x u /\
        FLOOKUP H' x = FLOOKUP H x /\
        op_taint tm' (Var x) = op_taint tm (Var x)) /\
      tm'.t_stor = tm.t_stor /\ tm'.t_trans = tm.t_trans /\
      tm'.t_imm = tm.t_imm /\
      (!i. ~(w2n aw <= i /\ i < w2n aw + type_memory_size dtv) ==>
        (i IN tm'.t_mem <=> i IN tm.t_mem))) /\
  fn_has_code sa stx fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    (!i m. i < N /\ mem_agree_outside tm.t_mem t.vs_memory m ==>
      val_in_memory dtv (f i) (w2n dw + i * type_memory_size dtv) m) /\
    typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + N * type_memory_size dtv) ==>
      (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    ~t.vs_halted /\ t.vs_current_bb = stx.cs_current_bb /\
    t.vs_inst_idx = LENGTH stx.cs_current_insts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `cs_extends st0 st1 /\ cs_extends stj st2 /\ cs_extends ste st3` by
    metis_tac[ci_mono_emit_inst, ci_mono_def, pairTheory.SND] >>
  `cs_extends st1 sth /\ cs_extends st2 stb /\ cs_extends st3 stx` by
    metis_tac[ci_mono_new_block, ci_mono_def, pairTheory.SND] >>
  `cs_extends stb stx` by metis_tac[cs_extends_trans] >>
  `cs_extends stj stx` by metis_tac[cs_extends_trans] >>
  `cs_extends sa init /\ cs_extends sa st0 /\ cs_extends sa sth /\
   cs_extends sa stb` by gvs[ci_mono_def] >>
  `fn_has_code init st0 fn /\ fn_has_code st0 st1 fn /\
   fn_has_code sth st2 fn /\ fn_has_code stb ste fn /\
   fn_has_code ste st3 fn` by
    (rpt conj_tac >> irule fn_has_code_mid >>
     (conj_tac >- metis_tac[ci_mono_def, cs_extends_trans]) >>
     qexistsl_tac [`stx`, `sa`] >> simp[] >>
     metis_tac[cs_extends_trans]) >>
  `sth.cs_current_bb = hdr /\ sth.cs_current_insts = [] /\
   stb.cs_current_bb = blabel /\ stb.cs_current_insts = [] /\
   stx.cs_current_bb = exit /\ stx.cs_current_insts = []` by
    gvs[new_block_def] >>
  `s.vs_current_bb = init.cs_current_bb /\
   s.vs_inst_idx = LENGTH init.cs_current_insts` by simp[] >>
  drule_all widened_assign_scalar_init_counted >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `t.vs_memory = s.vs_memory` by
    (qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[NoAsms]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
     FLOOKUP G' x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  `st0.cs_current_bb = init.cs_current_bb` by
    (qpat_x_assum `emit_inst ASSIGN _ _ init = _` mp_tac >>
     simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def, comp_return_def] >>
     disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  `typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t` by
    (irule widened_assign_admin_state_frame >> simp[] >>
     qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >>
     simp[NoAsms, venom_state_component_equality] >> simp[]) >>
  qabbrev_tac `Inv = \j H tm q.
    lookup_var counter q = SOME (n2w j) /\
    FLOOKUP H counter = NONE /\ op_taint tm (Var counter) = {} /\
    (!i m. i < N /\ mem_agree_outside tm.t_mem q.vs_memory m ==>
      val_in_memory stv (f i) (w2n sw + i * type_memory_size stv) m) /\
    (!i m. i < j /\ mem_agree_outside tm.t_mem q.vs_memory m ==>
      val_in_memory dtv (f i) (w2n dw + i * type_memory_size dtv) m) /\
    typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s q /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + N * type_memory_size dtv) ==>
      (i IN tm.t_mem <=> i IN tn.t_mem))` >>
  `!j H tm q H1 tm1 r.
     Inv j H tm q /\
     r.vs_memory = q.vs_memory /\ tm1.t_mem = tm.t_mem /\
     lookup_var counter r = lookup_var counter q /\
     FLOOKUP H1 counter = FLOOKUP H counter /\
     op_taint tm1 (Var counter) = op_taint tm (Var counter) /\
     typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) q r /\
     (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x q /\
       FLOOKUP H1 x = FLOOKUP H x /\
       op_taint tm1 (Var x) = op_taint tm (Var x)) /\
     tm1.t_stor = tm.t_stor /\ tm1.t_trans = tm.t_trans /\
     tm1.t_imm = tm.t_imm ==> Inv j H1 tm1 r` by
    (qpat_assum `Abbrev (Inv = _)` (fn th =>
       simp[NoAsms, CONV_RULE (REWR_CONV markerTheory.Abbrev_def) th]) >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> gvs[] >>
     metis_tac[typed_copy_state_frame_trans]) >>
  pop_assum (mk_asm "admin") >>
  `Inv 0 G' tn' t` by
    (asm_x "admin" kall_tac >>
     qpat_x_assum `Abbrev (Inv = _)` (fn th =>
       pure_rewrite_tac[CONV_RULE (REWR_CONV markerTheory.Abbrev_def) th]) >>
     simp[]) >>
  `st1.cs_blocks = st0.cs_blocks /\ st1.cs_current_bb = st0.cs_current_bb /\
   st1.cs_current_insts = st0.cs_current_insts ++
     [mk_inst st0.cs_next_id JMP [Label hdr] []]` by
    (qpat_x_assum `emit_inst JMP _ _ st0 = _` mp_tac >>
     simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def, comp_return_def] >>
     disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  `?bb. lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx =
      SOME (mk_inst st0.cs_next_id JMP [Label hdr] [])` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> conj_tac
     >- gvs[] >>
     qpat_x_assum `!k. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G' tn' t 0 G' tn' (OK (jump_to hdr t))` by
    (irule for_range_jump_path_ptr >> simp[] >> metis_tac[]) >>
  `!j H tm q lbl. Inv j H tm q ==> Inv j H tm (jump_to lbl q)` by
    (qpat_x_assum `Abbrev (Inv = _)` (fn th =>
       simp[CONV_RULE (REWR_CONV markerTheory.Abbrev_def) th, jump_to_def, lookup_var_def]) >>
     rpt strip_tac >> simp[] >>
     irule typed_copy_state_frame_trans >> qexists_tac `q` >> simp[] >>
     irule widened_assign_admin_state_frame >>
     simp[jump_to_def, lookup_var_def, venom_state_component_equality]) >>
  `Inv 0 G' tn' (jump_to hdr t)` by metis_tac[] >>
  `!j H tm q. j <= N /\ Inv j H tm q /\ ~q.vs_halted /\
      q.vs_current_bb = hdr /\ q.vs_inst_idx = 0 ==>
    ?r H1 tm1. gas_path_ptr D 0 ctx fn PG H tm q 0 H1 tm1 (OK r) /\
      Inv j H1 tm1 r /\ ~r.vs_halted /\ r.vs_inst_idx = 0 /\
      r.vs_current_bb = (if j = N then exit else blabel)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `Inv j H tm q` (fn ith =>
       qpat_assum `Abbrev (Inv = _)` (fn th =>
         strip_assume_tac (BETA_RULE (PURE_REWRITE_RULE
           [CONV_RULE (REWR_CONV markerTheory.Abbrev_def) th] ith)))) >>
     `!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s /\
       FLOOKUP H x = FLOOKUP G x /\
       op_taint tm (Var x) = op_taint tn (Var x)` by simp[] >>
     `eval_operand length q = SOME (n2w N) /\
      op_prov H length = NONE /\ op_taint tm length = {}` by
       (`eval_operand length q = eval_operand length s /\
         op_prov H length = op_prov G length /\
         op_taint tm length = op_taint tn length` by
          (irule widened_assign_reserved_operand_frame >>
           qexistsl_tac [`N * type_memory_size dtv`, `w2n dw`, `sa`] >>
           simp[] >> metis_tac[]) >> simp[]) >>
     `lookup_var counter q = SOME (n2w j) /\
      FLOOKUP H counter = NONE /\ op_taint tm (Var counter) = {}` by
       simp[] >>
     `eval_operand (Var counter) q = SOME (n2w j) /\
      op_prov H (Var counter) = NONE /\
      q.vs_current_bb = sth.cs_current_bb /\
      q.vs_inst_idx = LENGTH sth.cs_current_insts` by
       simp[eval_operand_def, op_prov_def] >>
     drule_all widened_assign_index_header_counted >>
     disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
     `!x. not_fresh_at sa x ==> not_fresh_at sth x` by
       metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
     `typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) q t'` by
       (irule widened_assign_admin_state_frame >> simp[] >> metis_tac[]) >>
     `t'.vs_memory = q.vs_memory` by
       (qpat_assum `t' = _` (fn th => once_rewrite_tac[th]) >> simp[NoAsms]) >>
     `Inv j G'' tn'' t'` by
       (asm "admin" irule >>
        qexistsl_tac [`H`, `q`, `tm`] >>
        asm_x "admin" kall_tac >> simp[] >> metis_tac[]) >>
     `t'.vs_current_bb = (if j = N then exit else blabel)` by
       (`j < dimword (:256)` by decide_tac >>
        qpat_x_assum `t'.vs_current_bb = _` mp_tac >>
        simp[wordsTheory.w2n_n2w] >>
        Cases_on `j = N`
        >- simp[] >>
        `j < N` by decide_tac >> simp[]) >>
     qpat_x_assum `Abbrev (Inv = _)` kall_tac >>
     qexistsl_tac [`t'`, `G''`, `tn''`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!j H tm q. j < N /\ Inv j H tm q /\ ~q.vs_halted /\
      q.vs_current_bb = blabel /\ q.vs_inst_idx = 0 ==>
    ?r H1 tm1. gas_path_ptr D 0 ctx fn PG H tm q 0 H1 tm1 (OK r) /\
      Inv (SUC j) H1 tm1 r /\ ~r.vs_halted /\
      r.vs_current_bb = hdr /\ r.vs_inst_idx = 0` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `Inv j H tm q` (fn ith =>
       qpat_assum `Abbrev (Inv = _)` (fn th =>
         strip_assume_tac (BETA_RULE (PURE_REWRITE_RULE
           [CONV_RULE (REWR_CONV markerTheory.Abbrev_def) th] ith)))) >>
     `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
       eval_operand op q = eval_operand op s /\
       op_prov H op = op_prov G op /\ op_taint tm op = op_taint tn op` by
       (rpt gen_tac >> disch_tac >>
        irule widened_assign_reserved_operand_frame >>
        qexistsl_tac [`N * type_memory_size dtv`, `w2n dw`, `sa`] >> simp[]) >>
     `eval_operand src q = SOME sw /\ eval_operand dst q = SOME dw /\
      op_taint tm src = {} /\ op_taint tm dst = {}` by metis_tac[] >>
     `(0 < type_memory_size stv ==> ?x. src = Var x /\
        ptr_covers H tm x q (N * type_memory_size stv)) /\
      (0 < type_memory_size dtv ==> ?x. dst = Var x /\
        ptr_covers H tm x q (N * type_memory_size dtv))` by
       metis_tac[decoderGhostFramePtrTheory.ptr_covers_frame] >>
     `!x. src = Var x \/ dst = Var x ==> not_fresh_at stb x` by
       metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
     qpat_assum `w2n sw + _ <= w2n dw \/ _`
       (assume_tac o ONCE_REWRITE_RULE [DISJ_COMM]) >>
     `(!i. i < N ==> val_wf dtv (f i) /\ val_wf stv (f i)) /\
      q.vs_current_bb = stb.cs_current_bb /\
      q.vs_inst_idx = LENGTH stb.cs_current_insts` by simp[] >>
     drule_all widened_assign_index_body_counted >>
     strip_tac >>
     `!x. not_fresh_at sa x ==> lookup_var x t' = lookup_var x s /\
       FLOOKUP H' x = FLOOKUP G x /\
       op_taint tm' (Var x) = op_taint tn (Var x)` by
       (rpt strip_tac >>
        `not_fresh_at stb x /\ x <> counter` by
          metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
        metis_tac[]) >>
     `typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t'` by
       (irule typed_copy_state_frame_trans >> qexists_tac `q` >> simp[]) >>
     `Inv (SUC j) H' tm' t'` by
       (asm_x "admin" kall_tac >>
        qpat_x_assum `Abbrev (Inv = _)` (fn th =>
          pure_rewrite_tac[CONV_RULE (REWR_CONV markerTheory.Abbrev_def) th]) >>
        simp[ADD1] >> metis_tac[]) >>
     `st3.cs_blocks = ste.cs_blocks /\ st3.cs_current_bb = ste.cs_current_bb /\
      st3.cs_current_insts = ste.cs_current_insts ++
        [mk_inst ste.cs_next_id JMP [Label hdr] []]` by
       (qpat_x_assum `emit_inst JMP _ _ ste = _` mp_tac >>
        simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def, comp_return_def] >>
        disch_then (SUBST1_TAC o SYM) >> simp[]) >>
     `?bb. lookup_block t'.vs_current_bb fn.fn_blocks = SOME bb /\
       get_instruction bb t'.vs_inst_idx =
         SOME (mk_inst ste.cs_next_id JMP [Label hdr] [])` by
       (drule_all fn_has_code_same_block >> strip_tac >>
        qexists_tac `bb'` >> conj_tac >- gvs[] >>
        qpat_x_assum `!k. _` (qspec_then `0` mp_tac) >> simp[]) >>
     `gas_path_ptr D 0 ctx fn PG H' tm' t' 0 H' tm' (OK (jump_to hdr t'))` by
       (irule for_range_jump_path_ptr >> simp[] >> metis_tac[]) >>
     `gas_path_ptr D 0 ctx fn PG H tm q 0 H' tm' (OK (jump_to hdr t'))` by
       (qpat_assum `gas_path_ptr _ _ _ _ _ H tm q _ _ _ _`
          (mp_then (Pos hd) mp_tac gas_path_ptr_then) >>
        disch_then drule >> simp[]) >>
     qexistsl_tac [`jump_to hdr t'`, `H'`, `tm'`] >>
     qpat_x_assum `Abbrev (Inv = _)` kall_tac >>
     simp[jump_to_def] >> metis_tac[]) >>
  `?u Hf tmf. gas_path_ptr D 0 ctx fn PG G' tn' (jump_to hdr t) 0 Hf tmf (OK u) /\
     Inv N Hf tmf u /\ ~u.vs_halted /\
     u.vs_current_bb = exit /\ u.vs_inst_idx = 0` by
    (irule toplevel_copy_iterate_path >>
     qpat_x_assum `Abbrev (Inv = _)` kall_tac >>
     simp[jump_to_def] >> conj_tac
     >- (qexists_tac `blabel` >>
         qpat_x_assum `!j H tm q. j <= N /\ _ ==> _` mp_tac >>
         qpat_x_assum `!j H tm q. j < N /\ _ ==> _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[ADD1]) >>
     qexistsl_tac [`0`, `N`] >>
     qpat_assum `Inv 0 G' tn' (jump_to hdr t)`
       (mp_tac o REWRITE_RULE [jump_to_def]) >>
     simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G' tn' t 0 Hf tmf (OK u)` by
    (qpat_assum `gas_path_ptr _ _ _ _ _ G' tn' t _ _ _ _`
       (mp_then (Pos hd) mp_tac gas_path_ptr_then) >>
     disch_then drule >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Hf tmf (OK u)` by
    (qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
       (mp_then (Pos hd) mp_tac gas_path_ptr_then) >>
     disch_then drule >> simp[]) >>
  qpat_assum `Inv N Hf tmf u` (fn ith =>
    qpat_assum `Abbrev (Inv = _)` (fn th =>
      strip_assume_tac (BETA_RULE (PURE_REWRITE_RULE
        [CONV_RULE (REWR_CONV markerTheory.Abbrev_def) th] ith)))) >>
  qexistsl_tac [`Hf`, `tmf`, `u`] >>
  qpat_x_assum `Abbrev (Inv = _)` kall_tac >>
  simp[]
QED
