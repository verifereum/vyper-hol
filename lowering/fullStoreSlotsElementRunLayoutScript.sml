(* Compiler-range supplement for the emitted element-loop interface. *)
Theory fullStoreSlotsElementRunLayout
Ancestors
  placeStoreSlots fragExec exprLoweringProps emitHelperProps loweringShapeRules
  freshWrites context emitHelper compileEnv list rich_list arithmetic pair
  loweringStateRelDefs

Theorem store_slots_elements_run_layout:
  fn_has_code sa sb func /\
  ci_mono sa sc /\ ci_mono sc sd /\ ci_mono sd sb /\
  fresh_label "dyn_cond" sa = (hdr,a) /\
  fresh_label "dyn_body" a = (blabel,b) /\
  fresh_label "dyn_exit" b = (exit,c) /\
  fresh_var c = (cv,init) /\
  emit_inst ASSIGN [Lit 0w] [cv] init = ((),p) /\
  emit_inst JMP [Label hdr] [] p = ((),q) /\
  new_block hdr q = (q.cs_current_bb,h) /\
  emit_op LT [Var cv;cnt] h = (Var lv,h1) /\
  emit_op ISZERO [Var lv] h1 = (Var dv,h2) /\
  emit_inst JNZ [Var dv;Label exit;Label blabel] [] h2 = ((),hj) /\
  new_block blabel hj = (hj.cs_current_bb,body_start) /\
  emit_op MUL [Var cv;Lit (n2w ms)] body_start = (so,b1) /\
  emit_op ADD [src;so] b1 = (sp,b2) /\
  emit_op MUL [Var cv;Lit (n2w slots)] b2 = (doff,b3) /\
  emit_op ADD [dst;doff] b3 = (dp,sc) /\
  emit_op ADD [Var cv;Lit 1w] sd = (Var iv,tail1) /\
  emit_inst ASSIGN [Var iv] [cv] tail1 = ((),tail2) /\
  emit_inst JMP [Label hdr] [] tail2 = ((),tail3) /\
  new_block exit tail3 = (tail3.cs_current_bb,sb) ==>
  fn_has_code init q func /\ fn_has_code h hj func /\
  fn_has_code body_start tail3 func /\
  init.cs_current_bb = sa.cs_current_bb /\
  LENGTH init.cs_current_insts = LENGTH sa.cs_current_insts /\
  h.cs_current_bb = hdr /\ h.cs_current_insts = [] /\
  body_start.cs_current_bb = blabel /\ body_start.cs_current_insts = [] /\
  sb.cs_current_bb = exit /\ sb.cs_current_insts = [] /\
  ci_mono sa body_start /\ ci_mono body_start sc /\
  not_fresh_at body_start cv /\ cv <> lv /\ cv <> dv /\
  (!x. not_fresh_at sa x ==> not_fresh_at body_start x /\
    x <> cv /\ x <> lv /\ x <> dv /\ x <> iv)
Proof
  strip_tac >>
  `cs_extends sa init /\ cs_extends init q /\ cs_extends h hj /\
   cs_extends body_start sc /\ cs_extends sd tail3` by
    (gvs[fresh_label_def,fresh_var_def,emit_inst_def,emit_op_def,
      fresh_id_def,emit_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,
      cs_extends_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[IS_PREFIX_APPEND]) >>
  imp_res_tac cs_extends_new_block >>
  `fn_has_code init q func /\ fn_has_code h hj func /\
   fn_has_code body_start tail3 func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_mid,cs_extends_trans]) >>
  `cs_extends sa body_start` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `sc.cs_next_var <= sd.cs_next_var` by fs[ci_mono_def] >>
  rpt (qpat_x_assum `ci_mono _ _` kall_tac) >>
  simp[ci_mono_def] >>
  rpt (qpat_x_assum `fn_has_code _ _ _` kall_tac) >>
  rpt (qpat_x_assum `cs_extends _ _` kall_tac) >>
  gvs[fresh_label_def,fresh_var_def,emit_inst_def,emit_op_def,
    fresh_id_def,emit_def,new_block_def,comp_bind_def,comp_ignore_bind_def,
    comp_return_def] >>
  fs[not_fresh_at_def] >>
  rpt conj_tac >> rpt strip_tac >>
  simp[GSYM APPEND_ASSOC,IS_PREFIX_APPEND] >>
  metis_tac[fresh_var_distinct,LESS_EQ_TRANS,LESS_LESS_EQ_TRANS]
QED
