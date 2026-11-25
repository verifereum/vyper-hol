(* Compiler and execution cuts for the non-word MakeArray slot suffix. *)
Theory bodyMakeSlotNonwordMods
Ancestors
  bodyMakeElementsContractMods bodyMakeElementStoreMods bodyStructFieldsSourceMods
  bodyIfExpArmUnwrapMods bodyAttributeAddFrameMods bodyFullMakeArrayInputs
  bodyIfExpTypedImmFrameMods gasOutcomeFullPostMods bodyFullIfExpReach
  externalEntryShape exprSimUnwrap exprLoweringProps fragExec compileEnv
  bodyPtrMakeArrayEmission bodyFullAttributeAdd fragGasSeqPtr ptrDiscipline
  venomState finite_map words bodyPtrDefs

val _ = Parse.hide "base";

Theorem make_slot_nonword_code_cuts[local]:
  make_elements_once_mods ce e q off dty sa = ((),sb) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  fn_has_code sa sb func ==>
  ?dst sn src sc.
    emit_op ADD [Var q; Lit (n2w off)] sm = (dst,sn) /\
    unwrap_value ce vv sn = (src,sc) /\
    compile_store_memory ce src dst dty (lowered_value_type ce e) sc = ((),sb) /\
    fn_has_code sm sn func /\ fn_has_code sn sc func /\ fn_has_code sc sb func /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    ci_mono sm sn /\ ci_mono sn sc /\ ci_mono sc sb
Proof
  strip_tac >>
  Cases_on `emit_op ADD [Var q; Lit (n2w off)] sm` >>
  rename1 `emit_op ADD [Var q; Lit (n2w off)] sm = (dst,sn)` >>
  Cases_on `unwrap_value ce vv sn` >>
  rename1 `unwrap_value ce vv sn = (src,sc)` >>
  fs[make_elements_once_mods_def,comp_bind_def] >>
  drule_then strip_assume_tac compile_expr_extends >>
  drule_then assume_tac unwrap_value_extends >>
  `cs_extends sm sn` by
    (mp_tac (CONJUNCT1 (CONJUNCT2 cs_appends_emit_helpers)) >>
     simp[cs_appends_def] >> metis_tac[]) >>
  `cs_extends sc sb` by
    (qspecl_then [`ce`,`src`,`dst`,`dty`,`lowered_value_type ce e`,`sc`] mp_tac
       compile_store_memory_labels >> simp[]) >>
  `cs_extends sn sb` by metis_tac[cs_extends_trans] >>
  `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sm sb func` by metis_tac[fn_has_code_split] >>
  `fn_has_code sm sn func /\ fn_has_code sn sb func` by metis_tac[fn_has_code_split] >>
  `fn_has_code sn sc func /\ fn_has_code sc sb func` by metis_tac[fn_has_code_split] >>
  `ci_mono sm sn` by (qspecl_then [`ADD`,`[Var q; Lit (n2w off)]`,`sm`] mp_tac ci_mono_emit_op >> simp[]) >>
  `ci_mono sn sc` by (qspecl_then [`ce`,`vv`,`sn`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  `ci_mono sc sb` by
    (qspecl_then [`ce`,`src`,`dst`,`dty`,`lowered_value_type ce e`,`sc`] mp_tac
       ci_mono_compile_store_memory >> simp[]) >>
  simp[]
QED

(* The address calculation is independent of the operand returned by the
   expression.  Keep the pre-unwrap operand and the new address separate. *)
Theorem make_slot_nonword_add[local]:
  emit_op ADD [Var q; Lit (n2w off)] sm = (dst,sn) /\
  fn_has_code sm sn func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  lookup_var q s = SOME (n2w base) /\ ptr_covers G tn q s cap /\
  base + cap < dimword (:256) /\ off + n <= cap ==>
  ?out z Gf tf.
    dst = Var out /\ not_fresh_at sn out /\
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
    z = s with <|vs_vars := z.vs_vars; vs_inst_idx := z.vs_inst_idx|> /\
    z.vs_inst_idx = LENGTH sn.cs_current_insts /\
    z.vs_current_bb = sn.cs_current_bb /\ alloca_history func z /\
    lookup_var out z = SOME (n2w (base+off)) /\ ptr_covers Gf tf out z n /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sm p ==> lookup_var p z = lookup_var p s /\
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all_then strip_assume_tac emit_op_fetch_boundary >>
  qabbrev_tac `i = mk_inst sm.cs_next_id ADD [Var q; Lit (n2w off)] [tmp]` >>
  qabbrev_tac `u = update_var tmp (n2w (base+off)) s` >>
  qabbrev_tac `z = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `Gf = step_prov PG G i u` >>
  qabbrev_tac `tf = step_taint i s u tn` >>
  `op_taint tn (Var q) = {}` by fs[ptr_covers_def] >>
  `(!D lo explicit. allocas_from lo s ==>
     gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
   FLOOKUP Gf tmp = op_prov G (Var q) /\ op_taint tf (Var tmp) = {} /\
   tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
   (!p. p <> tmp ==> FLOOKUP Gf p = FLOOKUP G p /\
       op_taint tf (Var p) = op_taint tn (Var p))` by
    (`eval_operand (Var q) s = SOME (n2w base)` by simp[eval_operand_def] >>
     `u = update_var tmp (n2w base + n2w off) s` by simp[Abbr `u`,word_add_n2w] >>
     map_every (fn pat => qpat_assum pat
       (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]))
       [`Abbrev (i = _)`,`Abbrev (z = _)`,`Abbrev (Gf = _)`,`Abbrev (tf = _)`] >>
     drule_all attribute_add_full_frame >>
     qpat_assum `dst = Var tmp` (fn th => pure_once_rewrite_tac[th]) >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `lookup_var tmp z = SOME (n2w (base+off))` by
    simp[Abbr `z`,Abbr `u`,update_var_def,lookup_var_def,FLOOKUP_UPDATE] >>
  `ptr_covers Gf tf tmp z n` by
    (qpat_x_assum `ptr_covers G tn q s cap` (mp_tac o REWRITE_RULE[ptr_covers_def]) >>
     `base < dimword (:256) /\ base+off < dimword (:256)` by decide_tac >>
     simp[ptr_covers_def,op_prov_def] >>
     disch_then (qx_choosel_then [`b`,`sz`] strip_assume_tac) >>
     qexistsl [`b`,`sz`] >> simp[] >> decide_tac) >>
  `alloca_history func z` by
    (qpat_x_assum `alloca_history func s`
       (strip_assume_tac o REWRITE_RULE[allocaHistoryTheory.alloca_history_def]) >>
     simp[allocaHistoryTheory.alloca_history_def,Abbr `z`,Abbr `u`,update_var_def] >>
     rpt strip_tac >>
     `k < s.vs_inst_idx \/ k = s.vs_inst_idx` by decide_tac
     >- (first_x_assum irule >> conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl [`bb'`,`k`] >> metis_tac[]) >>
     gvs[Abbr `i`,venomInstTheory.mk_inst_def]) >>
  qexistsl [`tmp`,`z`,`Gf`,`tf`] >>
  simp[Abbr `z`,Abbr `u`,update_var_def] >>
  conj_tac
  >- (drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  rpt strip_tac >>
  `p <> STRING #"%" (toString sm.cs_next_var)` by metis_tac[] >>
  simp[lookup_var_def,FLOOKUP_UPDATE,EQ_SYM_EQ]
QED
