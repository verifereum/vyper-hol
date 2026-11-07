(* Pure compiler boundaries for the post-CALL consumers. *)
Theory rawCallFinishCodePtr
Ancestors
  rawCallResultProofPtr loweringShapeRules exprLoweringProps emitHelperProps
  fragExec compileEnv
Libs monadsyntax

Theorem raw_call_emit_code:
  emit_op opc ops sa = (op,sc) /\ fn_has_code sa sc func ==>
  ?out bb. op = Var out /\ ~not_fresh_at sa out /\ not_fresh_at sc out /\
    lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id opc ops [out]) /\
    sc.cs_current_bb = sa.cs_current_bb /\
    LENGTH sc.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\ ci_mono sa sc
Proof
  strip_tac >> drule emit_op_facts >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qexistsl_tac [`out`, `bb`] >> simp[] >>
  conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  metis_tac[ci_mono_emit_op, pairTheory.SND]
QED

(* Label generation does not emit code, allocate variables, or move the PC. *)
Theorem raw_call_labels_boundary:
  fresh_label first sc = (bad,s1) /\ fresh_label second s1 = (good,sa) ==>
  sa.cs_current_bb = sc.cs_current_bb /\ sa.cs_current_insts = sc.cs_current_insts /\
  sa.cs_next_var = sc.cs_next_var /\ sa.cs_next_id = sc.cs_next_id /\
  ci_mono sc sa /\
  (not_fresh_at sa x <=> not_fresh_at sc x) /\
  (local_ptrs_reserved cenv sa <=> local_ptrs_reserved cenv sc)
Proof
  strip_tac >> drule fresh_label_props >> strip_tac >>
  drule_all fresh_label_props >> strip_tac >>
  simp[not_fresh_at_def, local_ptrs_reserved_def] >>
  gvs[fresh_label_def, ci_mono_def, cs_extends_def]
QED

Theorem raw_call_failure_code_mono:
  ci_mono sa (SND ((do rds <- emit_op RETURNDATASIZE [];
    buf <- compile_alloc_buffer 0;
    emit_void RETURNDATACOPY [buf.buf_operand;Lit 0w;rds];
    emit_inst REVERT [buf.buf_operand;rds] [] od) sa))
Proof
  rpt (FIRST [ho_match_mp_tac ci_mono_bind, ho_match_mp_tac ci_mono_ignore_bind] >> rpt strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_emit_inst, ci_mono_compile_alloc_buffer]
QED

Theorem raw_call_return_code_mono:
  ci_mono sa (SND ((if n > 0 then
    if rev then
      do z <- emit_op RETURNDATASIZE [];
         cmp <- emit_op LT [z;Lit (n2w n)];
         cap <- compile_select cmp z (Lit (n2w n));
         emit_void MSTORE [ov;cap]; return ov od
    else
      do z <- emit_op RETURNDATASIZE [];
         cmp <- emit_op LT [z;Lit (n2w n)];
         cap <- compile_select cmp z (Lit (n2w n));
         emit_void MSTORE [ov;cap];
         buf <- compile_alloc_buffer (64 + ((n+31) DIV 32)*32);
         emit_void MSTORE [buf.buf_operand;ok];
         dst <- emit_op ADD [buf.buf_operand;Lit 32w];
         emit_void MCOPY [dst;ov;Lit (n2w (32+((n+31) DIV 32)*32))];
         return buf.buf_operand od
    else return (if rev then Lit 0w else ok)) sa))
Proof
  Cases_on `n > 0` >> Cases_on `rev` >> simp[builtinSimpleTheory.compile_select_def] >>
  rpt (FIRST [ho_match_mp_tac ci_mono_bind, ho_match_mp_tac ci_mono_ignore_bind] >> rpt strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
    ci_mono_compile_alloc_buffer]
QED

Theorem raw_call_reverting_code_groups:
  compile_raw_call_finish addr dp dl gas value ct n T ov op sa = (result,sb) /\
  fn_has_code sa sb func ==>
  ?ok sc bad s1 good sj se fb sf sk pb sn.
    (case ct of
       DelegateCall => emit_op DELEGATECALL [gas;addr;dp;dl;op;Lit (n2w n)]
     | StaticCall => emit_op STATICCALL [gas;addr;dp;dl;op;Lit (n2w n)]
     | RegularCall => emit_op CALL [gas;addr;value;dp;dl;op;Lit (n2w n)]) sa = (ok,sc) /\
    fresh_label "call_failed" sc = (bad,s1) /\ fresh_label "call_ok" s1 = (good,sj) /\
    emit_inst JNZ [ok;Label good;Label bad] [] sj = ((),se) /\
    new_block bad se = (fb,sf) /\
    (do rds <- emit_op RETURNDATASIZE [];
        buf <- compile_alloc_buffer 0;
        emit_void RETURNDATACOPY [buf.buf_operand;Lit 0w;rds];
        emit_inst REVERT [buf.buf_operand;rds] [] od) sf = ((),sk) /\
    new_block good sk = (pb,sn) /\
    (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [ov;cap]; return ov od
     else return (Lit 0w)) sn = (result,sb) /\
    sj.cs_current_bb = sc.cs_current_bb /\ sj.cs_current_insts = sc.cs_current_insts /\
    sj.cs_next_var = sc.cs_next_var /\ sj.cs_next_id = sc.cs_next_id /\
    ci_mono sa sc /\ ci_mono sc sj /\ ci_mono sj se /\ ci_mono se sf /\
    ci_mono sf sk /\ ci_mono sk sn /\ ci_mono sn sb /\
    fn_has_code sa sc func /\ fn_has_code sj se func /\
    fn_has_code sf sk func /\ fn_has_code sn sb func
Proof
  strip_tac >> drule raw_call_reverting_finish_steps >> strip_tac >>
  rename1 `fresh_label "call_failed" sc = (bad,s1)` >>
  `ci_mono sa sc` by
    (Cases_on `ct` >> gvs[] >> metis_tac[ci_mono_emit_op, pairTheory.SND]) >>
  `ci_mono sc s2` by metis_tac[raw_call_labels_boundary] >>
  `ci_mono s2 s3 /\ ci_mono s3 s4 /\ ci_mono s8 s9` by
    metis_tac[ci_mono_emit_inst, ci_mono_new_block, pairTheory.SND] >>
  `(do rds <- emit_op RETURNDATASIZE [];
        buf <- compile_alloc_buffer 0;
        emit_void RETURNDATACOPY [buf.buf_operand;Lit 0w;rds];
        emit_inst REVERT [buf.buf_operand;rds] [] od) s4 = ((),s8)` by
    simp[comp_bind_def, comp_ignore_bind_def] >>
  `ci_mono s4 s8` by metis_tac[raw_call_failure_code_mono, pairTheory.SND] >>
  `ci_mono s9 sb` by
    (mp_tac (raw_call_return_code_mono |> Q.INST [`sa` |-> `s9`, `rev` |-> `T`]) >>
     gvs[]) >>
  qexistsl_tac [`ok`, `sc`, `bad`, `s1`, `pass`, `s2`, `s3`, `fblock`, `s4`, `s8`, `pblock`, `s9`] >>
  simp[] >>
  `s2.cs_current_bb = sc.cs_current_bb /\ s2.cs_current_insts = sc.cs_current_insts /\
   s2.cs_next_var = sc.cs_next_var /\ s2.cs_next_id = sc.cs_next_id` by
    metis_tac[raw_call_labels_boundary] >>
  simp[] >>
  gvs[ci_mono_def] >>
  metis_tac[fn_has_code_mid, cs_extends_trans, cs_extends_refl]
QED

Theorem raw_call_nonrevert_code_groups:
  compile_raw_call_finish addr dp dl gas value ct n F ov op sa = (result,sb) /\
  fn_has_code sa sb func ==>
  ?ok sc. (case ct of
      DelegateCall => emit_op DELEGATECALL [gas;addr;dp;dl;op;Lit (n2w n)]
    | StaticCall => emit_op STATICCALL [gas;addr;dp;dl;op;Lit (n2w n)]
    | RegularCall => emit_op CALL [gas;addr;value;dp;dl;op;Lit (n2w n)]) sa = (ok,sc) /\
    (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [ov;cap];
          buf <- compile_alloc_buffer (64+((n+31) DIV 32)*32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;ov;Lit (n2w (32+((n+31) DIV 32)*32))];
          return buf.buf_operand od
     else return ok) sc = (result,sb) /\
    ci_mono sa sc /\ ci_mono sc sb /\ fn_has_code sa sc func /\ fn_has_code sc sb func
Proof
  strip_tac >> drule raw_call_nonrevert_finish_code >> strip_tac >>
  `ci_mono sa sc` by
    (Cases_on `ct` >> gvs[] >> metis_tac[ci_mono_emit_op, pairTheory.SND]) >>
  `ci_mono sc sb` by
    (mp_tac (raw_call_return_code_mono |> Q.INST [`sa` |-> `sc`, `rev` |-> `F`]) >> gvs[]) >>
  qexistsl_tac [`ok`, `sc`] >> simp[] >>
  gvs[ci_mono_def] >> metis_tac[fn_has_code_split]
QED

Theorem raw_call_finish_call_code:
  compile_raw_call_finish addr dp dl gas value ct n rev ov op sa = (result,sb) /\
  ct <> DelegateCall /\ fn_has_code sa sb func ==>
  ?out sc bb.
    (if ct = StaticCall then emit_op STATICCALL [gas;addr;dp;dl;op;Lit (n2w n)]
     else emit_op CALL [gas;addr;value;dp;dl;op;Lit (n2w n)]) sa = (Var out,sc) /\
    fn_has_code sa sc func /\ ci_mono sa sc /\
    ~not_fresh_at sa out /\ not_fresh_at sc out /\
    sc.cs_current_bb = sa.cs_current_bb /\
    LENGTH sc.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
    lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) = SOME
      (mk_inst sa.cs_next_id (if ct = StaticCall then STATICCALL else CALL)
        (if ct = StaticCall then [gas;addr;dp;dl;op;Lit (n2w n)]
         else [gas;addr;value;dp;dl;op;Lit (n2w n)]) [out])
Proof
  strip_tac >> Cases_on `rev`
  >- (drule_all raw_call_reverting_code_groups >> strip_tac >>
      Cases_on `ct` >> gvs[] >> drule_all raw_call_emit_code >>
      strip_tac >> qexistsl_tac [`out`, `bb`] >> simp[]) >>
  drule_all raw_call_nonrevert_code_groups >> strip_tac >>
  Cases_on `ct` >> gvs[] >> drule_all raw_call_emit_code >>
  strip_tac >> qexistsl_tac [`out`, `bb`] >> simp[]
QED
