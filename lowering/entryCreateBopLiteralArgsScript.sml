Theory entryCreateBopLiteralArgs
Ancestors
  entryCreateExprList exprSimBopInLiteralWord exprSimUnopProps
  bodyFullWordArgs entryCreateIntervalLayout
  exprSimFullBundleProps s1PrefixDefs gasShadowCompileStmtHelpers
  gasShadow gasShadowState exprSimWordArgs exprBodyPreProps fragExec
  exprLoweringProps entryCreateFocusSpec exprSimHypsDefs
  compileEnv vyperContext vyperAST vyperInterpreter vyperState list pair

(* Match the two lowerings at the end of the list, not at equal raw and
   shadow PCs. Only the operand list is shared by the shadow compiler. *)
Theorem literal_member_compile_split[local]:
  (bop = In \/ bop = NotIn) /\ is_ArrayT aty /\
  gas_shadow_state a ha /\
  lower_value compile_expr ce ty
    (Builtin ann (Bop bop) [e1; Builtin aty (MakeArray t n) elems]) a = (op,b) /\
  lower_value compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr
      (Builtin ann (Bop bop) [e1; Builtin aty (MakeArray t n) elems])) ha = (op,hb) ==>
  ?needle xs m hm.
    lower_word_args ce expr_type (e1::elems) a = (needle::xs,m) /\
    lower_word_args (gas_shadow_env T ce) expr_type
      (MAP gas_shadow_expr (e1::elems)) ha = (needle::xs,hm) /\
    gas_shadow_state m hm /\
    (if bop = In then compile_list_membership_in needle xs
     else compile_list_membership_notin needle xs) m = (op,b) /\
    (if bop = In then compile_list_membership_in needle xs
     else compile_list_membership_notin needle xs) hm = (op,hb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?needle xs m.
     lower_word_args ce expr_type (e1::elems) a = (needle::xs,m) /\
     (if bop = In then compile_list_membership_in needle xs
      else compile_list_membership_notin needle xs) m = (op,b)` by
    (irule literal_lower_value >> simp[] >> metis_tac[]) >>
  `?hneedle hxs hm.
     lower_word_args (gas_shadow_env T ce) expr_type
       (MAP gas_shadow_expr (e1::elems)) ha = (hneedle::hxs,hm) /\
     (if bop = In then compile_list_membership_in hneedle hxs
      else compile_list_membership_notin hneedle hxs) hm = (op,hb)` by
    (simp[MAP] >> irule literal_lower_value >> simp[] >>
     qexistsl_tac [`aty`,`ann`,`n`,`t`,`ty`] >>
     qpat_assum `lower_value _ (gas_shadow_env T ce) _ _ ha = _`
       (mp_tac o REWRITE_RULE [gas_shadow_expr_def,gas_shadow_builtin_def,MAP]) >> simp[]) >>
  `gas_shadow_compiles (lower_word_args ce expr_type (e1::elems))
     (lower_word_args (gas_shadow_env T ce) expr_type
       (MAP gas_shadow_expr (e1::elems)))` by
    simp[gas_shadow_compiles_lower_word_args] >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (mp_tac o SPECL [``a:compile_state``,``ha:compile_state``] o
      REWRITE_RULE [gas_shadow_compiles_def]) >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem literal_member_args_pre:
  body_inv tops C ce cx /\ shadow_body_inv tops C shC /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
  expr_body_pre ce cx env
    (Builtin ann (Bop bop) [e1; Builtin aty (MakeArray t n) elems]) es /\
  create_layout a b /\
  expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx ty
    (Builtin ann (Bop bop) [e1; Builtin aty (MakeArray t n) elems]) es
    (st0,a,b,ha,hb,op,s,G,tn) ==>
  ?needle xs m hm.
    create_word_args_pre (DF,lo,d,C,shC,PG,f,shf) tops ce env cx expr_type
      (e1::elems) (es,st0,a,m,ha,hm,needle::xs,s,G,tn) /\
    cs_extends a m /\ cs_extends m b /\ cs_extends ha hm /\ cs_extends hm hb /\
    a.cs_next_id <= m.cs_next_id /\
    create_layout a m /\ create_layout m b /\
    fn_has_code m b f /\ fn_has_code hm hb shf /\
    (if bop = In then compile_list_membership_in needle xs
     else compile_list_membership_notin needle xs) m = (op,b) /\
    (if bop = In then compile_list_membership_in needle xs
     else compile_list_membership_notin needle xs) hm = (op,hb) /\
    LENGTH xs = LENGTH elems /\
    EVERY (\x. (!z. x = Var z ==> not_fresh_at m z) /\ (!l. x <> Label l))
      (needle::xs)
Proof
  simp[expr_sim_full_pre_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_body_typing >> strip_tac >>
  `is_ArrayT aty` by simp[vyperASTTheory.is_ArrayT_def] >>
  drule_all literal_member_compile_split >> strip_tac >>
  `wb_args_shape ce expr_type (e1::elems)` by
    (irule literal_args_shape >> metis_tac[]) >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `cs_extends m b /\ cs_extends hm hb` by
    (Cases_on `bop = In` >> fs[] >>
     metis_tac[literal_membership_straight,straight_fresh_cs_extends]) >>
  `cs_extends ha hm` by
    metis_tac[ci_mono_lower_word_args,ci_mono_def,SND] >>
  `fn_has_code a m f /\ fn_has_code m b f /\
   fn_has_code ha hm shf /\ fn_has_code hm hb shf` by
    metis_tac[fn_has_code_split] >>
  `create_layout a m /\ create_layout m b` by
    metis_tac[create_layout_subinterval,cs_extends_refl] >>
  `!e ee. MEM e (e1::elems) /\ expr_sim_inv ce cx env ee ==>
          expr_body_pre ce cx env e ee /\ is_word_type (expr_type e)` by
    (rpt strip_tac
     >- (irule literal_body_operand_pre >> metis_tac[]) >>
     fs[EVERY_MEM, MEM] >> metis_tac[]) >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  qexistsl_tac [`needle`,`xs`,`m`,`hm`] >>
  fs[create_word_args_pre_def,expr_sim_full_code_def,create_operand_at_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

(* The induction's reachability guard permits separate successful eval and
   read witnesses. Thread this guard across the consumed prefix; do not ask
   the callback to simulate the MakeArray expression itself. *)
Theorem literal_member_guarded_arg_sites:
  expr_body_pre ce cx env
    (Builtin ann (Bop bop) [e1; Builtin aty (MakeArray t n) elems]) es /\
  (bop = In \/ bop = NotIn) /\
  (!ee st x y hx hy op' u K nn.
    expr_sim_inv ce cx env ee /\ expr_body_pre ce cx env e1 ee /\
    body_const_cells_agree [(NONE,tops)] cx env ee /\
    is_word_type (expr_type e1) /\ create_layout x y /\
    expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx (expr_type e1) e1 ee
      (st,x,y,hx,hy,op',u,K,nn) ==> P e1 ee st x y hx hy op' u K nn) /\
  ((?s0 tv s1 s2 v s3. eval_expr cx e1 s0 = (INL tv,s1) /\
                       read_result cx tv s2 = (INL v,s3)) ==>
   builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
   !front h back ee st x y hx hy op' u K nn.
    elems = front ++ h::back /\
    EVERY (\e. ?s0 tv s1 s2 v s3. eval_expr cx e s0 = (INL tv,s1) /\
                                      read_result cx tv s2 = (INL v,s3)) front /\
    expr_sim_inv ce cx env ee /\ expr_body_pre ce cx env h ee /\
    body_const_cells_agree [(NONE,tops)] cx env ee /\
    is_word_type (expr_type h) /\ create_layout x y /\
    expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx (expr_type h) h ee
      (st,x,y,hx,hy,op',u,K,nn) ==> P h ee st x y hx hy op' u K nn) ==>
  !front h back ee st x y hx hy op' u K nn.
    e1::elems = front ++ h::back /\
    EVERY (\e. ?s0 tv s1 s2 v s3. eval_expr cx e s0 = (INL tv,s1) /\
                                      read_result cx tv s2 = (INL v,s3)) front /\
    expr_sim_inv ce cx env ee /\ expr_body_pre ce cx env h ee /\
    body_const_cells_agree [(NONE,tops)] cx env ee /\
    is_word_type (expr_type h) /\ create_layout x y /\
    expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx (expr_type h) h ee
      (st,x,y,hx,hy,op',u,K,nn) ==> P h ee st x y hx hy op' u K nn
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `builtin_args_length_ok (MakeArray t n) (LENGTH elems)` by
    (drule_all literal_body_typing >> simp[builtin_args_length_ok_def]) >>
  Cases >> simp[] >> rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[]
QED
