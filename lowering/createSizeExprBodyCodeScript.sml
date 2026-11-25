(* Caller-control certificates for the open expression compiler equation. *)
Theory createSizeExprBodyCode
Ancestors
  createSizeCutCode createSizeCutOpens createSizeBuiltinBodyCode exprOperandVar exprLowering exprCallBounds context
  compileEnv emitHelper builtinMath vyperAST arithmetic
  finite_map pair list pred_set venomInst externalEntryShape
  exprBopLowering compilerFirstEmission

Theorem cut_result_snd[local]:
  p = (x,b) ==> SND p = b
Proof
  simp[]
QED

(* Recover the action from the result equation for the goal's end state. *)
val cut_result_tac = first_assum (fn th =>
  CHANGED_TAC (CONV_TAC (RAND_CONV (REWR_CONV (GSYM (MATCH_MP cut_result_snd th))))));

(* Use only the compiler action at the head of the goal. Unfolding all
   recursive definitions in the simplifier would duplicate continuations. *)
fun cut_step ths = FIRST
  [first_assum MATCH_ACCEPT_TAC,
   match_mp_tac create_cut_code_bind >> conj_tac >> BETA_TAC,
   match_mp_tac create_cut_code_ignore_bind >> conj_tac >> BETA_TAC,
   CHANGED_TAC (CONV_TAC (RAND_CONV (RAND_CONV
     (REWR_CONV compilerFirstEmissionTheory.state_pair_let_bind)))),
   match_mp_tac create_cut_code_emit_op >> simp[create_cut_targets_def],
   match_mp_tac create_cut_code_emit_void >> simp[create_cut_targets_def],
   match_mp_tac create_cut_code_emit_inst >> simp[create_cut_targets_def],
   match_mp_tac create_cut_code_emit_multi_op >> simp[create_cut_targets_def],
   CHANGED_TAC (simp_tac std_ss [LET_THM, SND, FST, UNCURRY_DEF]),
   FIRST (map (fn th => CHANGED_TAC (pure_once_rewrite_tac [th])) ths),
   CHANGED_TAC (simp[create_cut_code_refl]),
   BasicProvers.TOP_CASE_TAC,
   IF_CASES_TAC];

Theorem cut_code_name[local]:
  !a. create_cut_code exits a (SND (compile_name_vv ce ty id a))
Proof
  gen_tac >> PURE_REWRITE_TAC [compile_name_vv_def] >> rpt (cut_step [])
QED

Theorem cut_code_literal[local]:
  !l ty a. create_cut_code {} a (SND (compile_literal_vv ty l a))
Proof
  Cases >> rpt gen_tac
  >- (Cases_on `b` >> simp[compile_literal_vv_def]) >>
  rpt (FIRST [MATCH_ACCEPT_TAC create_bytelike_literal_cut_code,
              cut_step [compile_literal_vv_def]])
QED

Theorem cut_code_ptr_word[local]:
  (!ctor imm loc op a. create_cut_code exits a (SND (compile_ptr_load ctor imm loc op a))) /\
  (!ctor imm loc op v a. create_cut_code exits a (SND (compile_ptr_store ctor imm loc op v a)))
Proof
  conj_tac >> rpt gen_tac >> Cases_on `loc` >>
  rpt (cut_step [compile_ptr_load_def, compile_ptr_store_def,
                 compile_imm_load_word_def, compile_imm_store_word_def])
QED

Theorem cut_code_lower_value[local]:
  (!c ty e a. create_cut_code exits a (SND (f c ty e a))) /\
  (!c vv a. create_cut_code exits a (SND (unwrap_value c vv a))) ==>
  !c ty e a. create_cut_code exits a (SND (lower_value f c ty e a))
Proof
  strip_tac >> rpt gen_tac >> PURE_REWRITE_TAC [lower_value_def] >> rpt (cut_step [])
QED

Theorem cut_code_array_subscript[local]:
  (!op a. create_cut_code exits a (SND (loader op a))) ==>
  !a. create_cut_code exits a
    (SND (compile_array_subscript p idx dyn cnt ws sz is_signed loader a))
Proof
  strip_tac >> gen_tac >> PURE_REWRITE_TAC [compile_array_subscript_def] >>
  rpt (cut_step [])
QED

val access_defs = [compile_tuple_subscript_def, compile_mapping_subscript_def,
                   compile_keccak256_key_def];
val word_access = map MATCH_ACCEPT_TAC (CONJUNCTS cut_code_ptr_word);

Theorem cut_code_subscript[local]:
  (!c ty e a. create_cut_code {} a (SND (f c ty e a))) /\
  (!c vv a. create_cut_code {} a (SND (unwrap_value c vv a))) /\
  (!c vv a. create_cut_code {} a (SND (compile_snapshot_vv c T vv a))) ==>
  !a. create_cut_code {} a (SND (compile_subscript f c rt ty base_e idx a))
Proof
  rpt strip_tac >> imp_res_tac cut_code_lower_value >>
  PURE_REWRITE_TAC [compile_subscript_def] >>
  rpt (FIRST ([match_mp_tac cut_code_array_subscript >> gen_tac] @
      word_access @ [MATCH_ACCEPT_TAC create_alloc_buffer_cut_code, cut_step access_defs]))
QED

Theorem cut_code_get_target_ptr[local]:
  (!c ty e a. create_cut_code {} a (SND (f c ty e a))) /\
  (!c vv a. create_cut_code {} a (SND (unwrap_value c vv a))) ==>
  !tgt a. create_cut_code {} a (SND (compile_get_target_ptr f c tgt a))
Proof
  strip_tac >> imp_res_tac cut_code_lower_value >>
  measureInduct_on `base_assignment_target_size tgt` >> Cases_on `tgt` >> gen_tac >>
  simp_tac std_ss [Once compile_get_target_ptr_def] >>
  rpt (FIRST ([match_mp_tac cut_code_array_subscript >> gen_tac] @
      word_access @ [MATCH_ACCEPT_TAC create_alloc_buffer_cut_code, cut_step access_defs]))
QED

Theorem cut_code_struct_lit[local]:
  (!c ty e a. create_cut_code {} a (SND (f c ty e a))) /\
  (!c vv a. create_cut_code {} a (SND (unwrap_value c vv a))) /\
  (!c src dst dty sty a. create_cut_code {} a (SND (compile_store_memory c src dst dty sty a))) ==>
  !fields buf off a. create_cut_code {} a (SND (compile_struct_lit f c ty fields buf off a))
Proof
  strip_tac >> Induct >- simp[compile_struct_lit_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> simp_tac std_ss [Once compile_struct_lit_def] >>
  rpt (cut_step [])
QED

Theorem cut_code_mod_names[local]:
  (!c vv a. create_cut_code {} a (SND (unwrap_value c vv a))) ==>
  (!a. create_cut_code {} a (SND (compile_addmod_names c rt aty id bty jd mty md a))) /\
  (!a. create_cut_code {} a (SND (compile_mulmod_names c rt aty id bty jd mty md a))) /\
  (!a. create_cut_code {} a (SND (compile_powmod256_names c rt aty id bty jd a)))
Proof
  strip_tac >> conj_tac >- (gen_tac >>
    PURE_REWRITE_TAC [compile_addmod_names_def] >>
    rpt (FIRST [MATCH_ACCEPT_TAC cut_code_name,
         cut_step [exprBopLoweringTheory.as_stack_val_pair, compile_addmod_def]])) >>
  conj_tac >> gen_tac >>
  PURE_REWRITE_TAC [compile_mulmod_names_def, compile_powmod256_names_def] >>
  rpt (FIRST [MATCH_ACCEPT_TAC cut_code_name,
       cut_step [exprBopLoweringTheory.as_stack_val_pair, compile_mulmod_def, compile_pow_mod256_def]])
QED

Theorem cut_code_invalid[local]:
  create_cut_code exits a (SND (invalid_expr_call ty a))
Proof
  PURE_REWRITE_TAC [invalid_expr_call_def] >> rpt (cut_step [])
QED

Theorem cut_code_guarded_callbacks[local]:
  ((!c ty e a. expr_size e + cenv_defaults_size c < bound ==>
     create_cut_code {} a (SND (f c ty e a))) ==>
   !c ty e a. create_cut_code {} a (SND (expr_child_callback bound f c ty e a))) /\
  ((!c rt ty bi args a. list_size expr_size args + cenv_defaults_size c < bound ==>
     create_cut_code {} a (SND (g c rt ty bi args a))) ==>
   !c rt ty bi args a.
     create_cut_code {} a (SND (builtin_child_callback bound g c rt ty bi args a))) /\
  ((!c vt ty tb rt args a. list_size expr_size args + cenv_defaults_size c < bound ==>
     create_cut_code {} a (SND (h c vt ty tb rt args a))) ==>
   !c vt ty tb rt args a.
     create_cut_code {} a (SND (type_child_callback bound h c vt ty tb rt args a)))
Proof
  rpt conj_tac >> strip_tac >> rpt gen_tac >>
  PURE_REWRITE_TAC [expr_child_callback_def, builtin_child_callback_def,
                    type_child_callback_def] >>
  IF_CASES_TAC >> simp[cut_code_invalid]
QED
Theorem cut_code_ifexp_arm[local]:
  (!c vv a. create_cut_code {} a (SND (unwrap_value c vv a))) /\
  (!c src dst dty sty a. create_cut_code {} a (SND (compile_store_memory c src dst dty sty a))) ==>
  !a. create_cut_code {} a (SND (compile_ifexp_arm c rt aty vv a))
Proof
  strip_tac >> gen_tac >> PURE_REWRITE_TAC [compile_ifexp_arm_def] >>
  rpt (FIRST [MATCH_ACCEPT_TAC create_alloc_buffer_cut_code, cut_step []])
QED

(* Each branch is an opaque closed action; its own block openings need not
   be enumerated to discharge the three diamond destinations. *)
Theorem cut_code_diamond[local]:
  emit_inst JNZ [cond; Label l; Label r] [] a = (u,b) /\
  new_block l b = (x,c) /\ create_cut_code {} c d /\
  emit_inst JMP [Label j] [] d = (v,e) /\
  new_block r e = (y,f) /\ create_cut_code {} f g /\
  emit_inst JMP [Label j] [] g = (w,h) /\
  new_block j h = (z,i) ==>
  create_cut_code {} a i
Proof
  strip_tac >>
  `create_cut_code {l;r;j} a b /\ create_cut_code {l;r;j} d e /\
   create_cut_code {l;r;j} g h` by
    (rpt conj_tac >>
     cut_result_tac >> irule create_cut_code_emit_inst >> simp[create_cut_targets_def] >> metis_tac[]) >>
  `create_cut_code {l;r;j} b c /\ create_cut_code {l;r;j} e f /\
   create_cut_code {l;r;j} h i` by
    metis_tac[create_cut_code_new_block, SND] >>
  `create_cut_code {l;r;j} c d /\ create_cut_code {l;r;j} f g` by
    (rpt conj_tac >> irule create_cut_code_weaken >> qexists_tac `{}` >> simp[]) >>
  `create_cut_code {l;r;j} a i` by
    metis_tac[create_cut_code_join] >>
  irule create_cut_code_close >> qexists_tac `{l;r;j}` >> simp[] >>
  `cs_extends a b /\ cs_extends a e /\ cs_extends a h /\ cs_extends c i /\
   cs_extends f i` by
    (fs[create_cut_code_def] >> metis_tac[cs_extends_trans]) >>
  imp_res_tac added_labels_new_block >>
  `MEM l (added_labels a i) /\ MEM r (added_labels a i) /\
   MEM j (added_labels a i)` suffices_by simp[] >>
  `!p q. create_cut_code {l;r;j} p q ==> cs_extends p q` by
    simp[create_cut_code_def] >>
  `cs_extends b i /\ cs_extends e i /\ cs_extends h i` by
    metis_tac[cs_extends_trans] >>
  `added_labels b i = [l] ++ added_labels c i /\
   added_labels e i = [r] ++ added_labels f i` by
    metis_tac[added_labels_trans] >>
  rpt conj_tac >> metis_tac[added_labels_trans, MEM_APPEND, MEM]
QED


Theorem create_expr_body_cut_code:
  bound = expr_size e + cenv_defaults_size c /\
  (!ce t child a. expr_size child + cenv_defaults_size ce < bound ==>
    create_cut_code {} a (SND (f ce t child a))) /\
  (!ce rt t bi args a. list_size expr_size args + cenv_defaults_size ce < bound ==>
    create_cut_code {} a (SND (g ce rt t bi args a))) /\
  (!ce vt t tb rt args a. list_size expr_size args + cenv_defaults_size ce < bound ==>
    create_cut_code {} a (SND (h ce vt t tb rt args a))) /\
  (!ce vv a. create_cut_code {} a (SND (unwrap_value ce vv a))) /\
  (!ce src dst dty sty a.
    create_cut_code {} a (SND (compile_store_memory ce src dst dty sty a))) /\
  (!ce vv a. create_cut_code {} a (SND (compile_snapshot_vv ce T vv a))) /\
  (!ann target args default a. e = Call ann target args default /\
    (!ck hs rof ks. target <> CreateTarget ck hs rof ks) ==>
    create_cut_code {} a
      (SND (compile_call (expr_child_callback bound f) c (expr_type e) ty
              target args default a))) /\
  (!ann ck hs rof ks args default a. e = Call ann (CreateTarget ck hs rof ks) args default ==>
    create_cut_code {} a
      (SND (compile_create_call (expr_child_callback bound f) c ck hs rof args a))) ==>
  create_cut_code {} a
    (SND (compile_expr_body (expr_child_callback bound f)
       (builtin_child_callback bound g) (type_child_callback bound h) c ty e a))
Proof
  strip_tac >> imp_res_tac cut_code_guarded_callbacks >>
  Cases_on `e`
  >~ [`IfExp _ _ _ _`] >- suspend "ifexp"
  >~ [`Builtin _ _ _`] >- suspend "builtin"
  >>
  PURE_REWRITE_TAC [compile_expr_body_def, LET_THM] >> BETA_TAC >>
  CONV_TAC (RAND_CONV (RAND_CONV BasicProvers.CASE_SIMP_CONV))
  >> TRY (qmatch_goalsub_abbrev_tac `compile_call _ _ _ _ _ _ _ _` >>
          unabbrev_all_tac >> suspend "call" >> NO_TAC)
  >~ [`compile_subscript _ _ _ _ _ _ _`] >-
    (irule cut_code_subscript >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC)
  >~ [`compile_struct_lit _ _ _ _ _ _ _`] >- suspend "structlit"
  >~ [`compile_get_target_ptr _ _ _ _`] >- suspend "pop" >>
  rpt (FIRST [MATCH_ACCEPT_TAC cut_code_literal, MATCH_ACCEPT_TAC cut_code_name,
              cut_step [compile_attribute_def]])
QED

Resume create_expr_body_cut_code[builtin]:
  qspec_then `\r:vyper_value # compile_state. create_cut_code {} a (SND r)`
    (ho_match_mp_tac o BETA_RULE) compiler_expr_builtin_pred >>
  rpt conj_tac >> rpt gen_tac >>
  FIRST (first_assum MATCH_ACCEPT_TAC ::
    map (fn th => irule (DISCH_ALL th) >> first_assum MATCH_ACCEPT_TAC)
      (CONJUNCTS (UNDISCH cut_code_mod_names)))
QED

Resume create_expr_body_cut_code[call]:
  qmatch_goalsub_abbrev_tac `compile_call _ _ _ _ target _ _ _` >>
  unabbrev_all_tac >> rename1 `Call ann target args default` >>
  Cases_on `?ck hs rof ks. target = CreateTarget ck hs rof ks`
  >- (pop_assum strip_assume_tac >>
      qpat_x_assum `target = CreateTarget _ _ _ _` SUBST_ALL_TAC >>
      simp_tac std_ss [compile_call_def, exprBopLoweringTheory.as_stack_val_pair, SND] >>
      qpat_assum `!ann ck hs rof ks args default a. _ ==> create_cut_code _ _ _`
        (irule o SPEC_ALL) >> metis_tac[]) >>
  qpat_assum `!ann target args default a. _ ==> create_cut_code _ _ _`
    (irule o SPEC_ALL) >> metis_tac[]
QED

Resume create_expr_body_cut_code[structlit]:
  rpt (FIRST [MATCH_ACCEPT_TAC create_alloc_buffer_cut_code,
     irule cut_code_struct_lit >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC,
     cut_step []])
QED

Resume create_expr_body_cut_code[pop]:
  CONV_TAC (RAND_CONV (RAND_CONV
    (REWR_CONV compilerFirstEmissionTheory.state_pair_let_bind))) >>
  match_mp_tac create_cut_code_bind >> conj_tac
  >- (irule cut_code_get_target_ptr >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  simp_tac std_ss [ELIM_UNCURRY] >> BETA_TAC >>
  rpt (FIRST (word_access @ [cut_step [compile_dynarray_pop_def]]))
QED

Resume create_expr_body_cut_code[ifexp]:
  simp_tac std_ss [compile_expr_body_def, LET_THM,
                    TypeBase.case_def_of ``:expr``] >>
  ntac 17 (pairarg_tac >> pop_assum (fn th => pure_rewrite_tac [th] >> assume_tac th) >>
           simp_tac std_ss [UNCURRY_DEF]) >>
  IF_CASES_TAC >> simp_tac std_ss [SND] >>
  `create_cut_code {} a st1` by
    (cut_result_tac >> irule cut_code_lower_value >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `create_cut_code {} st1 st2 /\ create_cut_code {} st2 st3 /\
   create_cut_code {} st3 st4 /\ create_cut_code {} st4 st5` by
     (rpt conj_tac >> cut_result_tac >> simp_tac std_ss
       [create_cut_code_fresh_var, create_cut_code_fresh_label]) >>
  `create_cut_code {} st7 st7a /\ create_cut_code {} st11 st11a` by
     (rpt conj_tac >> cut_result_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `create_cut_code {} st7a st8 /\ create_cut_code {} st11a st12` by
     (rpt conj_tac >> cut_result_tac >> irule cut_code_ifexp_arm >>
      rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `create_cut_code {} st8 st9 /\ create_cut_code {} st12 st13` by
     (rpt conj_tac >> cut_result_tac >> irule create_cut_code_emit_inst >>
      simp[create_cut_targets_def]) >>
  `create_cut_code {} st7 st9 /\ create_cut_code {} st11 st13` by
     metis_tac[create_cut_code_join] >>
  `create_cut_code {} st5 st15` by
     (drule_all cut_code_diamond >> simp_tac std_ss []) >>
  metis_tac[create_cut_code_join]
QED

Finalise create_expr_body_cut_code

Theorem pair_result_snd[local]:
  p = (x,b) ==> SND p = b
Proof
  simp[]
QED

val result_snd_tac = first_assum (fn th =>
  CHANGED_TAC (CONV_TAC (RAND_CONV (REWR_CONV (GSYM (MATCH_MP pair_result_snd th))))));

Theorem ifexp_selected_closed_suffixes:
  create_cut_code {} st sc /\
  emit_inst JNZ [cond; Label l; Label r] [] sc = (u,b) /\
  new_block l b = (x,se) /\
  create_cut_code {} se sea /\
  emit_inst ASSIGN [then_op] [result_var] sea = (v,sx) /\
  emit_inst JMP [Label j] [] sx = (w,sj) /\
  new_block r sj = (y,fe) /\
  create_cut_code {} fe fea /\
  emit_inst ASSIGN [else_op] [result_var] fea = (p,fg) /\
  emit_inst JMP [Label j] [] fg = (q,fh) /\
  new_block j fh = (z,st') ==>
  create_cut_code {} st sc /\
  create_cut_code {} sc st' /\
  create_cut_code {} se sea /\
  create_cut_code {} se st' /\
  create_cut_code {} sea sx /\
  create_cut_code {} sea st' /\
  create_cut_code {} sx st'
Proof
  rpt strip_tac >>
  `create_cut_code {l;r;j} sc b /\
   create_cut_code {l;r;j} sx sj /\
   create_cut_code {l;r;j} fea fg /\
   create_cut_code {l;r;j} fg fh` by
    (rpt conj_tac >> result_snd_tac >>
     match_mp_tac create_cut_code_emit_inst >> simp[create_cut_targets_def] >> metis_tac[added_labels_trans]) >>
  `create_cut_code {l;r;j} b se /\
   create_cut_code {l;r;j} sj fe /\
   create_cut_code {l;r;j} fh st'` by
    (rpt conj_tac >> metis_tac[create_cut_code_new_block, SND]) >>
  `create_cut_code {l;r;j} se sea /\
   create_cut_code {l;r;j} fe fea` by
    (rpt conj_tac >> irule create_cut_code_weaken >> qexists_tac `{}` >> simp[]) >>
  `create_cut_code {l;r;j} sea sx` by
    (result_snd_tac >> match_mp_tac create_cut_code_emit_inst >> simp[create_cut_targets_def]) >>
  `create_cut_code {l;r;j} sc st'` by
    metis_tac[create_cut_code_join] >>
  `create_cut_code {l;r;j} se st' /\
   create_cut_code {l;r;j} sea st' /\
   create_cut_code {l;r;j} sx st'` by
    metis_tac[create_cut_code_join] >>
  `create_cut_code {l;r;j} st sc` by
    (irule create_cut_code_weaken >> qexists_tac `{}` >> simp[]) >>
  `create_cut_code {l;r;j} st st'` by
    metis_tac[create_cut_code_join] >>
  `added_labels b se = [l]` by
    first_assum (fn th => ACCEPT_TAC (MATCH_MP added_labels_new_block th)) >>
  `added_labels sj fe = [r]` by
    first_assum (fn th => ACCEPT_TAC (MATCH_MP added_labels_new_block th)) >>
  `added_labels fh st' = [j]` by
    first_assum (fn th => ACCEPT_TAC (MATCH_MP added_labels_new_block th)) >>
  `cs_extends sc b /\ cs_extends b se /\ cs_extends se sea /\
   cs_extends sea sx /\ cs_extends sx sj /\ cs_extends sj fe /\
   cs_extends fe fea /\ cs_extends fea fg /\ cs_extends fg fh /\
   cs_extends fh st'` by
    (fs[create_cut_code_def] >> metis_tac[cs_extends_trans]) >>
  `cs_extends sc se` by
    (irule cs_extends_trans >> qexists_tac `b` >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `cs_extends se sx` by
    (irule cs_extends_trans >> qexists_tac `sea` >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `cs_extends sx fe` by
    (irule cs_extends_trans >> qexists_tac `sj` >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `cs_extends fg st'` by
    (irule cs_extends_trans >> qexists_tac `fh` >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `cs_extends se st' /\ cs_extends sx st'` by
    (fs[create_cut_code_def] >> metis_tac[added_labels_trans]) >>
  `cs_extends sc sx` by
    (irule cs_extends_trans >> qexists_tac `se` >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `cs_extends sj fea` by
    (irule cs_extends_trans >> qexists_tac `fe` >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `cs_extends sj fg` by
    (irule cs_extends_trans >> qexists_tac `fea` >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `cs_extends sx fg` by
    (irule cs_extends_trans >> qexists_tac `sj` >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `cs_extends sc fg` by
    (irule cs_extends_trans >> qexists_tac `sx` >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `cs_extends fea st'` by
    (irule cs_extends_trans >> qexists_tac `fg` >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `cs_extends fe st'` by
    (irule cs_extends_trans >> qexists_tac `fea` >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `added_labels sc se = added_labels sc b ++ added_labels b se` by
    metis_tac[added_labels_trans] >>
  `MEM l (added_labels sc se)` by
    metis_tac[MEM_APPEND, MEM] >>
  `added_labels sc st' = added_labels sc se ++ added_labels se st'` by
    metis_tac[added_labels_trans] >>
  `MEM l (added_labels sc st')` by
    metis_tac[MEM_APPEND, MEM] >>
  `added_labels sx fe = added_labels sx sj ++ added_labels sj fe` by
    metis_tac[added_labels_trans] >>
  `MEM r (added_labels sx fe)` by
    metis_tac[MEM_APPEND, MEM] >>
  `added_labels sx st' = added_labels sx fe ++ added_labels fe st'` by
    (irule added_labels_trans >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `MEM r (added_labels sx st')` by
    metis_tac[MEM_APPEND, MEM] >>
  `added_labels sc sx = added_labels sc se ++ added_labels se sx` by
    metis_tac[added_labels_trans] >>
  `added_labels sc st' = added_labels sc sx ++ added_labels sx st'` by
    metis_tac[added_labels_trans] >>
  `MEM r (added_labels sc st')` by
    metis_tac[MEM_APPEND, MEM] >>
  `cs_extends sx fg` by metis_tac[cs_extends_trans] >>
  `added_labels fg st' = added_labels fg fh ++ added_labels fh st'` by
    metis_tac[added_labels_trans] >>
  `MEM j (added_labels fg st')` by
    metis_tac[MEM_APPEND, MEM] >>
  `added_labels sc fg = added_labels sc sx ++ added_labels sx fg` by
    metis_tac[added_labels_trans] >>
  `added_labels sc st' = added_labels sc fg ++ added_labels fg st'` by
    metis_tac[added_labels_trans] >>
  `MEM j (added_labels sc st')` by
    metis_tac[MEM_APPEND, MEM] >>
  `added_labels sx fg = added_labels sx sj ++ added_labels sj fg` by
    metis_tac[added_labels_trans] >>
  `added_labels sx st' = added_labels sx fg ++ added_labels fg st'` by
    metis_tac[added_labels_trans] >>
  `MEM j (added_labels sx st')` by
    metis_tac[MEM_APPEND, MEM] >>
  `added_labels sea st' = added_labels sea sx ++ added_labels sx st'` by
    metis_tac[added_labels_trans] >>
  `MEM r (added_labels sea st') /\ MEM j (added_labels sea st')` by
    (rpt conj_tac >> metis_tac[MEM_APPEND, MEM]) >>
  `cs_extends sea st'` by
    (fs[create_cut_code_def] >> metis_tac[]) >>
  `added_labels se st' = added_labels se sea ++ added_labels sea st'` by
    (irule added_labels_trans >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `MEM r (added_labels se st') /\ MEM j (added_labels se st')` by
    (rpt conj_tac >> metis_tac[MEM_APPEND, MEM]) >>
  `create_cut_code {} sc st'` by
    (irule create_cut_code_close >> qexists_tac `{l;r;j}` >> simp[]) >>
  `create_cut_code {} sea sx` by
    (result_snd_tac >> match_mp_tac create_cut_code_emit_inst >> simp[create_cut_targets_def]) >>
  `create_cut_code {r;j} sea sx` by
    (result_snd_tac >> match_mp_tac create_cut_code_emit_inst >> simp[create_cut_targets_def]) >>
  `create_cut_code {r;j} sx sj` by
    (result_snd_tac >> match_mp_tac create_cut_code_emit_inst >> simp[create_cut_targets_def] >> metis_tac[]) >>
  `create_cut_code {r;j} fea fg` by
    (result_snd_tac >> match_mp_tac create_cut_code_emit_inst >> simp[create_cut_targets_def]) >>
  `create_cut_code {r;j} fg fh` by
    (result_snd_tac >> match_mp_tac create_cut_code_emit_inst >> simp[create_cut_targets_def] >> metis_tac[]) >>
  `create_cut_code {r;j} se sea /\ create_cut_code {r;j} fe fea` by
    (rpt conj_tac >> irule create_cut_code_weaken >> qexists_tac `{}` >> simp[]) >>
  `create_cut_code {r;j} sj fe /\ create_cut_code {r;j} fh st'` by
    (rpt conj_tac >> metis_tac[create_cut_code_new_block, SND]) >>
  `create_cut_code {r;j} se st'` by metis_tac[create_cut_code_join] >>
  `create_cut_code {r;j} sea st'` by metis_tac[create_cut_code_join] >>
  `create_cut_code {r;j} sx st'` by metis_tac[create_cut_code_join] >>
  `create_cut_code {} se st'` by
    (irule create_cut_code_close >> qexists_tac `{r;j}` >> simp[]) >>
  `create_cut_code {} sea st'` by
    (irule create_cut_code_close >> qexists_tac `{r;j}` >> simp[]) >>
  `create_cut_code {} sx st'` by
    (irule create_cut_code_close >> qexists_tac `{r;j}` >> simp[]) >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
