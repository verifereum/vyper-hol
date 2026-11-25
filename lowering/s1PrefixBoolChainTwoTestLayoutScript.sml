(* The ordinary conditional and the fused two-test chain use different
   compiler states, even when they start with the very same state. *)
Theory s1PrefixBoolChainTwoTestLayout
Ancestors
  boolChainCodeLayout exprSimIfExp exprLoweringProps emitHelperProps
  fragExec compileEnv exprLowering vyperAST gasShadow

Theorem two_test_operands[local]:
  bool_chain_operands p (2 - 1)
    (IfExp (BaseT BoolT) c
      (if p then a else Literal (BaseT BoolT) (BoolL T))
      (if p then Literal (BaseT BoolT) (BoolL F) else a)) = [c;a]
Proof
  `2 - 1 = SUC 0` by EVAL_TAC >>
  pop_assum (PURE_ONCE_REWRITE_TAC o single) >>
  Cases_on `p` >> simp[Once bool_chain_operands_def] >>
  simp[bool_chain_operands_def]
QED

Theorem two_test_arm_extends[local]:
  compile_ifexp_arm ce t u vv s = (op,s') ==> cs_extends s s'
Proof
  strip_tac >>
  qspecl_then [`ce`,`t`,`u`,`vv`,`s`] mp_tac ci_mono_compile_ifexp_arm >>
  simp[ci_mono_def]
QED

Theorem two_test_ordinary_alloc_fields[local]:
  fresh_var sc = (r,sr) /\ fresh_label "then" sr = (tl,sl) /\
  fresh_label "else" sl = (el,sm) /\ fresh_label "exit" sm = (xl,sj) ==>
  sj.cs_current_bb = sc.cs_current_bb /\
  sj.cs_current_insts = sc.cs_current_insts /\ sj.cs_blocks = sc.cs_blocks /\
  sj.cs_next_id = sc.cs_next_id /\ sj.cs_next_var = sc.cs_next_var + 1
Proof
  strip_tac >> imp_res_tac fresh_label_props >>
  qpat_x_assum `fresh_var sc = _` mp_tac >> simp[fresh_var_def] >>
  strip_tac >> gvs[]
QED

(* The ordinary layout compiles the then-arm first, even for an Or chain
   (where the nonliteral arm is the else-arm). The fused layout instead
   emits the short-circuit block before the continuing operand. Each code
   containment implication uses only its own whole interval. *)
Theorem bool_chain_two_test_layouts:
  e = IfExp (BaseT BoolT) c
        (if p then a else Literal (BaseT BoolT) (BoolL T))
        (if p then Literal (BaseT BoolT) (BoolL F) else a) ==>
  (compile_expr ce ty e sa = (ov,ob) ==>
   ?cop oc r orv tl ol el om ox ojn oafter ot otv ot1 top ot2 ot3 ot4
      oe oev oe1 eop oe2 oe3 oe4.
     lower_value compile_expr ce (BaseT BoolT) c sa = (cop,oc) /\
     fresh_var oc = (r,orv) /\ fresh_label "then" orv = (tl,ol) /\
     fresh_label "else" ol = (el,om) /\ fresh_label "exit" om = (ox,ojn) /\
     emit_inst JNZ [cop; Label tl; Label el] [] ojn = ((),oafter) /\
     new_block tl oafter = (oafter.cs_current_bb,ot) /\
     compile_expr ce ty (if p then a else Literal (BaseT BoolT) (BoolL T))
       ot = (otv,ot1) /\
     compile_ifexp_arm ce (BaseT BoolT)
       (lowered_value_type ce (if p then a else Literal (BaseT BoolT) (BoolL T)))
       otv ot1 = (top,ot2) /\
     emit_inst ASSIGN [top] [r] ot2 = ((),ot3) /\
     emit_inst JMP [Label ox] [] ot3 = ((),ot4) /\
     new_block el ot4 = (ot4.cs_current_bb,oe) /\
     compile_expr ce ty (if p then Literal (BaseT BoolT) (BoolL F) else a)
       oe = (oev,oe1) /\
     compile_ifexp_arm ce (BaseT BoolT)
       (lowered_value_type ce (if p then Literal (BaseT BoolT) (BoolL F) else a))
       oev oe1 = (eop,oe2) /\
     emit_inst ASSIGN [eop] [r] oe2 = ((),oe3) /\
     emit_inst JMP [Label ox] [] oe3 = ((),oe4) /\
     new_block ox oe4 = (oe4.cs_current_bb,ob) /\
     ov = StackValue (BaseT BoolT) (Var r) /\
     ojn.cs_current_bb = oc.cs_current_bb /\ ojn.cs_current_insts = oc.cs_current_insts /\
     ojn.cs_blocks = oc.cs_blocks /\ ojn.cs_next_id = oc.cs_next_id /\
     ojn.cs_next_var = oc.cs_next_var + 1 /\
     ot.cs_current_bb = tl /\ oe.cs_current_bb = el /\
     ot.cs_current_insts = [] /\ oe.cs_current_insts = [] /\
     (!fn. fn_has_code sa ob fn ==>
        fn_has_code sa oc fn /\ fn_has_code ojn oafter fn /\
        fn_has_code ot ot1 fn /\ fn_has_code oe oe1 fn)) /\
  (compile_expr ce ty (Builtin (BaseT BoolT) (BoolChain p 2) [e]) sa = (nv,nb) ==>
   ?nr nrv nx ng nc ncop nj na ns nl nshort nassign njump ncont nop ndone nend.
     fresh_var sa = (nr,nrv) /\ fresh_label "bool_exit" nrv = (nx,ng) /\
     lower_value compile_expr ce (BaseT BoolT) c ng = (ncop,nc) /\
     (if p then
        comp_bind (fresh_label "and_next") (\nl.
          comp_bind (fresh_label "and_false") (\ns. comp_return (nl,ns)))
      else
        comp_bind (fresh_label "or_true") (\ns.
          comp_bind (fresh_label "or_next") (\nl. comp_return (nl,ns)))) nc = ((nl,ns),nj) /\
     emit_inst JNZ [ncop; Label (if p then nl else ns); Label (if p then ns else nl)]
       [] nj = ((),na) /\
     new_block ns na = (na.cs_current_bb,nshort) /\
     emit_inst ASSIGN [Lit (if p then 0w else 1w)] [nr] nshort = ((),nassign) /\
     emit_inst JMP [Label nx] [] nassign = ((),njump) /\
     new_block nl njump = (njump.cs_current_bb,ncont) /\
     lower_value compile_expr ce (BaseT BoolT) a ncont = (nop,ndone) /\
     emit_inst ASSIGN [nop] [nr] ndone = ((),nend) /\
     (?nf old. emit_inst JMP [Label nx] [] nend = ((),nf) /\
               new_block nx nf = (old,nb)) /\
     nv = StackValue (BaseT BoolT) (Var nr) /\
     ng.cs_current_bb = sa.cs_current_bb /\ ng.cs_current_insts = sa.cs_current_insts /\
     ng.cs_blocks = sa.cs_blocks /\ ng.cs_next_id = sa.cs_next_id /\
     ng.cs_next_var = sa.cs_next_var + 1 /\
     nj.cs_current_bb = nc.cs_current_bb /\ nj.cs_current_insts = nc.cs_current_insts /\
     nj.cs_blocks = nc.cs_blocks /\ nj.cs_next_id = nc.cs_next_id /\
     nj.cs_next_var = nc.cs_next_var /\
     ncont.cs_current_bb = nl /\ ncont.cs_current_insts = [] /\
     (!fn. fn_has_code sa nb fn ==>
        fn_has_code ng nc fn /\ fn_has_code nj na fn /\ fn_has_code ncont ndone fn))
Proof
  disch_tac >> asm_rewrite_tac[] >> conj_tac
  >- (
    disch_tac >> drule_then
      (qx_choosel_then
        [`cop`,`oc`,`r`,`orv`,`tl`,`ol`,`el`,`om`,`ox`,`ojn`,`oafter`,`old1`,`ot`,
         `otv`,`ot1`,`top`,`ot2`,`ot3`,`ot4`,`old2`,`oe`,`oev`,`oe1`,`eop`,`oe2`,
         `oe3`,`oe4`,`old3`] strip_assume_tac) compile_expr_ifexp >>
    imp_res_tac two_test_ordinary_alloc_fields >> imp_res_tac new_block_props >>
    imp_res_tac cs_extends_fresh_var >> imp_res_tac cs_extends_fresh_label >>
    imp_res_tac cs_extends_emit_inst >> imp_res_tac cs_extends_new_block >>
    imp_res_tac (CONJUNCT1 compile_expr_grows) >>
    imp_res_tac (CONJUNCT2 compile_expr_grows) >> imp_res_tac two_test_arm_extends >>
    map_every (fn (tm,mid) => tm by (irule cs_extends_trans >> qexists mid >> simp[]))
      [(`cs_extends sa orv`,`oc`), (`cs_extends sa ol`,`orv`),
       (`cs_extends sa om`,`ol`), (`cs_extends sa ojn`,`om`),
       (`cs_extends sa oafter`,`ojn`), (`cs_extends sa ot`,`oafter`),
       (`cs_extends sa ot1`,`ot`), (`cs_extends sa ot2`,`ot1`),
       (`cs_extends sa ot3`,`ot2`), (`cs_extends sa ot4`,`ot3`),
       (`cs_extends sa oe`,`ot4`), (`cs_extends oe3 ob`,`oe4`),
       (`cs_extends oe2 ob`,`oe3`), (`cs_extends oe1 ob`,`oe2`),
       (`cs_extends oe ob`,`oe1`), (`cs_extends ot4 ob`,`oe`),
       (`cs_extends ot3 ob`,`ot4`), (`cs_extends ot2 ob`,`ot3`),
       (`cs_extends ot1 ob`,`ot2`), (`cs_extends ot ob`,`ot1`),
       (`cs_extends oafter ob`,`ot`), (`cs_extends ojn ob`,`oafter`),
       (`cs_extends om ob`,`ojn`), (`cs_extends ol ob`,`om`),
       (`cs_extends orv ob`,`ol`), (`cs_extends oc ob`,`orv`)] >>
    qexistsl_tac
      [`cop`,`oc`,`r`,`orv`,`tl`,`ol`,`el`,`om`,`ox`,`ojn`,`oafter`,`ot`,`otv`,`ot1`,
       `top`,`ot2`,`ot3`,`ot4`,`oe`,`oev`,`oe1`,`eop`,`oe2`,`oe3`,`oe4`] >>
    fs[is_word_type_def] >> rpt strip_tac >> irule fn_has_code_mid >>
    simp[] >> qexistsl_tac [`ob`,`sa`] >> simp[cs_extends_refl]) >>
  disch_tac >> drule_then
    (qx_choosel_then [`r`,`sr`,`xl`,`sg`,`sf`,`old`] strip_assume_tac)
    bool_chain_root_layout >>
  qpat_x_assum `compile_bool_chain_ops compile_expr _ _ _ _ (bool_chain_operands _ _ _) _ = _`
    (assume_tac o REWRITE_RULE[two_test_operands]) >>
  drule_then
    (qx_choosel_then [`op`,`sc`,`sj`,`sn`,`ls`,`ln`,`ss`,`sd`,`se`,`st`] strip_assume_tac)
    bool_chain_test_layout_alloc >>
  drule_then (qx_choosel_then [`op2`,`sc2`,`sd2`] strip_assume_tac)
    bool_chain_singleton_layout >>
  qexistsl_tac [`r`,`sr`,`xl`,`sg`,`sc`,`op`,`sj`,`sn`,`ls`,`ln`,`ss`,`sd`,`se`,
                `st`,`op2`,`sc2`,`sd2`] >> simp[] >>
  rpt strip_tac >> res_tac
QED

(* Re-key the two root equations using the ordinary layout theorem with
   c' = gas_shadow_expr c, a' = gas_shadow_expr a. *)
Theorem bool_chain_two_test_shadow_syntax:
  e = IfExp (BaseT BoolT) c
        (if p then a else Literal (BaseT BoolT) (BoolL T))
        (if p then Literal (BaseT BoolT) (BoolL F) else a) ==>
  gas_shadow_expr e =
    IfExp (BaseT BoolT) (gas_shadow_expr c)
      (if p then gas_shadow_expr a else Literal (BaseT BoolT) (BoolL T))
      (if p then Literal (BaseT BoolT) (BoolL F) else gas_shadow_expr a) /\
  gas_shadow_expr (Builtin (BaseT BoolT) (BoolChain p 2) [e]) =
    Builtin (BaseT BoolT) (BoolChain p 2) [gas_shadow_expr e]
Proof
  Cases_on `p` >> simp[gas_shadow_expr_def, gas_shadow_builtin_def]
QED
