Theory bodyExtRequestCompilerCutsMods
Ancestors
  bodyFullExtCallPacking exprSimSend exprLowering exprLoweringProps externalEntryShape
  gasShadowCompile gasShadowState gasShadowCompileHelpers gasShadowCompileStmtHelpers
  gasShadowCompilePure entryReachBodyFirstEmissionExprSupport
  entryReachBodyFirstEmissionExpr compileEnv fragExec list pair
Libs
  pairLib

Theorem request_compile_layout[local]:
  compile_expr ce ty
    (Call ann (ExtCall stat skip (name,ats,rt) opts) (addr::tail) dr) sa = (vv,sb) ==>
  ?ao av vo go def gas s1 s2 s3 s5 result.
    lower_value compile_expr ce (BaseT AddressT) addr sa = (ao,s1) /\
    compile_ext_call_args compile_expr ce (DROP (LENGTH ats) tail)
      (MAP (lowered_value_type ce) (TAKE (LENGTH ats) tail))
      (TAKE (LENGTH ats) tail) s1 = (av,s2) /\
    compile_ext_call_kwargs compile_expr ce rt opts
      (DROP (LENGTH ats) tail) s2 = ((vo,go,def),s3) /\
    (case go of SOME g => (g,s3) | NONE => emit_op GAS [] s3) = (gas,s5) /\
    compile_external_call_kwargs ce ao av
      (MAP (lowered_value_type ce) (TAKE (LENGTH ats) tail))
      (abi_size_bound ce.ce_struct_fields
        (TupleT (MAP (lowered_value_type ce) (TAKE (LENGTH ats) tail))))
      (ce.ce_method_id name ats)
      (abi_size_bound ce.ce_struct_fields
        (if needs_external_call_wrap rt then TupleT [rt] else rt))
      (abi_static_size ce.ce_struct_fields
        (if needs_external_call_wrap rt then TupleT [rt] else rt))
      (type_memory_bytes ce rt) stat
      (case vo of SOME v => v | NONE => Lit 0w) gas skip
      (IS_SOME def) (case def of SOME (d,dt) => d | NONE => Lit 0w)
      rt (case def of SOME (d,dt) => dt | NONE => rt)
      (type_to_abi_dec_info ce.ce_struct_fields ce
        (if needs_external_call_wrap rt then TupleT [rt] else rt))
      s5 = (result,sb) /\
    vv = (if rt = NoneT then StackValue ann result
          else LocatedValue ann (mk_ptr result LocMemory))
Proof
  simp[compile_expr_call, compile_call_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[AllCaseEqs()] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem request_call_shadow_syntax[local]:
  gas_shadow_expr (Call ann (ExtCall stat skip sig opts) (addr::tail) dr) =
  Call ann (ExtCall stat skip sig opts) (gas_shadow_expr addr::MAP gas_shadow_expr tail)
    (OPTION_MAP gas_shadow_expr dr)
Proof
  simp[Once gasShadowTheory.gas_shadow_expr_def]
QED

Theorem request_address_pair[local]:
  gas_shadow_state a ah /\
  lower_value compile_expr ce ty e a = (o1,b) /\
  lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) ah = (oh,bh) ==>
  oh = o1 /\ gas_shadow_state b bh
Proof
  strip_tac >>
  mp_tac (Q.INST [`sd` |-> `T`, `cenv` |-> `ce`] gas_shadow_stmt_lower_value_env) >>
  simp[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`a`,`ah`] mp_tac) >> simp[]
QED

Theorem request_positional_pair[local]:
  gas_shadow_state a ah /\
  compile_ext_call_args compile_expr ce kws tys xs a = (av,b) /\
  compile_ext_call_args compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr kws)
    tys (MAP gas_shadow_expr xs) ah = (avh,bh) ==>
  avh = av /\ gas_shadow_state b bh
Proof
  strip_tac >>
  mp_tac (Q.INST [`sd` |-> `T`, `sh` |-> `T`, `cenv` |-> `ce`]
    (MATCH_MP gas_shadow_compiles_ext_call_args (cj 1 gas_shadow_compile_expr_env))) >>
  disch_then (qspecl_then [`xs`,`kws`,`tys`] mp_tac) >>
  simp[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`a`,`ah`] mp_tac) >> simp[]
QED

Theorem request_keyword_pair[local]:
  gas_shadow_state a ah /\
  compile_ext_call_kwargs compile_expr ce rt opts kws a = (args,b) /\
  compile_ext_call_kwargs compile_expr (gas_shadow_env T ce) rt opts
    (MAP gas_shadow_expr kws) ah = (argsh,bh) ==>
  argsh = args /\ gas_shadow_state b bh
Proof
  strip_tac >>
  mp_tac (Q.INST [`return_type` |-> `rt`, `sd` |-> `T`, `sh` |-> `T`, `cenv` |-> `ce`]
    (MATCH_MP gas_shadow_compiles_ext_call_kwargs_env (cj 1 gas_shadow_compile_expr_env))) >>
  simp[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`opts`,`kws`,`a`,`ah`] mp_tac) >> simp[]
QED

Theorem request_keyword_mono[local]:
  !ks es ce rt a. ci_mono a (SND (compile_ext_call_kwargs compile_expr ce rt ks es a))
Proof
  Induct >> Cases_on `es` >> rpt strip_tac >>
  simp[compile_ext_call_kwargs_def, ci_mono_comp_return] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_compile_ext_call_kwarg, cj 1 compile_expr_ci_mono] >>
  rpt strip_tac >> simp[UNCURRY] >>
  ho_match_mp_tac ci_mono_bind >> simp[UNCURRY, ci_mono_comp_return]
QED

Theorem request_optional_gas_mono[local]:
  ci_mono a (SND (case go of SOME g => (g,a) | NONE => emit_op GAS [] a))
Proof
  Cases_on `go` >> simp[ci_mono_refl, ci_mono_emit_op]
QED

Theorem request_code_slices[local]:
  cs_extends a b /\ cs_extends b c /\ cs_extends c d /\
  cs_extends d e /\ cs_extends e f /\ cs_extends f g /\ fn_has_code a g fn ==>
  fn_has_code a b fn /\ fn_has_code b c fn /\ fn_has_code c d fn /\
  fn_has_code d e fn /\ fn_has_code e f fn /\ fn_has_code f g fn
Proof
  strip_tac >>
  `cs_extends a c /\ cs_extends a d /\ cs_extends a e /\ cs_extends a f` by
    metis_tac[cs_extends_trans] >>
  `cs_extends b g /\ cs_extends c g /\ cs_extends d g /\ cs_extends e g` by
    metis_tac[cs_extends_trans] >>
  rpt conj_tac >> irule fn_has_code_mid >> simp[] >>
  qexistsl [`g`,`a`] >> simp[cs_extends_refl]
QED

Theorem request_head_code_slices[local]:
  cs_extends a b /\ cs_extends b c /\ cs_extends c d /\
  cs_extends d e /\ cs_extends e f /\ fn_has_code a f fn ==>
  fn_has_code a b fn /\ fn_has_code b c fn /\ fn_has_code c d fn /\
  fn_has_code d e fn /\ fn_has_code e f fn
Proof
  mp_tac (Q.INST [`g` |-> `f`] request_code_slices) >>
  simp[cs_extends_refl]
QED

Theorem request_pack_extends[local]:
  compile_external_call_kwargs ce ao av tys abi mid cap minsz retbytes stat
    value gas skip hasdef def rt dt adec a = (r,b) ==> cs_extends a b
Proof
  metis_tac[compile_external_call_kwargs_labels, SND]
QED

Theorem request_head_cuts[local]:
  compile_expr ce ty
    (Call ann (ExtCall stat skip (name,ats,rt) opts) (addr::tail) dr) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr
    (Call ann (ExtCall stat skip (name,ats,rt) opts) (addr::tail) dr)) sha = (vv,shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb fn /\ fn_has_code sha shb shfn ==>
  let xs = TAKE (LENGTH ats) tail;
      kws = DROP (LENGTH ats) tail;
      tys = MAP (lowered_value_type ce) xs;
      rty = if needs_external_call_wrap rt then TupleT [rt] else rt
  in
  ?ao av vo go def gas s1 s2 s3 s5 h1 h2 h3 hg h5 result.
    lower_value compile_expr ce (BaseT AddressT) addr sa = (ao,s1) /\
    lower_value compile_expr (gas_shadow_env T ce) (BaseT AddressT)
      (gas_shadow_expr addr) sha = (ao,h1) /\
    compile_ext_call_args compile_expr ce kws tys xs s1 = (av,s2) /\
    compile_ext_call_args compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr kws)
      tys (MAP gas_shadow_expr xs) h1 = (av,h2) /\
    compile_ext_call_kwargs compile_expr ce rt opts kws s2 = ((vo,go,def),s3) /\
    compile_ext_call_kwargs compile_expr (gas_shadow_env T ce) rt opts
      (MAP gas_shadow_expr kws) h2 = ((vo,go,def),h3) /\
    (case go of SOME g => (g,s3) | NONE => emit_op GAS [] s3) = (gas,s5) /\
    (case go of SOME g => (g,h3) | NONE => emit_op GAS [] h3) = (hg,h5) /\
    gas_shadow_state s1 h1 /\ gas_shadow_state s2 h2 /\ gas_shadow_state s3 h3 /\
    ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s5 /\
    cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\ cs_extends s3 s5 /\
    cs_extends sha h1 /\ cs_extends h1 h2 /\ cs_extends h2 h3 /\ cs_extends h3 h5 /\
    fn_has_code sa s1 fn /\ fn_has_code s1 s2 fn /\ fn_has_code s2 s3 fn /\
    fn_has_code s3 s5 fn /\ fn_has_code s5 sb fn /\
    fn_has_code sha h1 shfn /\ fn_has_code h1 h2 shfn /\
    fn_has_code h2 h3 shfn /\ fn_has_code h3 h5 shfn /\ fn_has_code h5 shb shfn /\
    compile_external_call_kwargs ce ao av tys
      (abi_size_bound ce.ce_struct_fields (TupleT tys)) (ce.ce_method_id name ats)
      (abi_size_bound ce.ce_struct_fields rty) (abi_static_size ce.ce_struct_fields rty)
      (type_memory_bytes ce rt) stat (case vo of SOME v => v | NONE => Lit 0w) gas skip
      (IS_SOME def) (case def of SOME (d,dt) => d | NONE => Lit 0w)
      rt (case def of SOME (d,dt) => dt | NONE => rt)
      (type_to_abi_dec_info ce.ce_struct_fields ce rty) s5 = (result,sb) /\
    vv = (if rt = NoneT then StackValue ann result
          else LocatedValue ann (mk_ptr result LocMemory))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qpat_assum `compile_expr _ _ (vyperAST$Call _ _ _ _) _ = _`
    (strip_assume_tac o MATCH_MP request_compile_layout) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o REWRITE_RULE
       [GSYM MAP_DROP, GSYM MAP_TAKE, MAP_MAP_o, combinTheory.o_DEF,
        gas_shadow_lowered_value_type, gasShadowCompileBaseTheory.lowered_value_type_gas_shadow_env,
        ETA_AX] o
     MATCH_MP request_compile_layout o REWRITE_RULE [request_call_shadow_syntax]) >>
  rename1 `lower_value _ _ _ _ sha = (ha,h1)` >>
  drule_all request_address_pair >> disch_then strip_assume_tac >>
  qpat_x_assum `ha = ao` SUBST_ALL_TAC >>
  rename1 `compile_ext_call_args _ _ _ _ _ h1 = (hav,h2)` >>
  drule_all request_positional_pair >> disch_then strip_assume_tac >>
  qpat_x_assum `hav = av` SUBST_ALL_TAC >>
  rename1 `compile_ext_call_kwargs _ _ _ _ _ h2 = ((hv,hgo,hdf),h3)` >>
  drule_all request_keyword_pair >> simp_tac bool_ss [PAIR_EQ] >> strip_tac >>
  qpat_x_assum `hv = vo` SUBST_ALL_TAC >>
  qpat_x_assum `hgo = go` SUBST_ALL_TAC >>
  qpat_x_assum `hdf = def` SUBST_ALL_TAC >>
  rename1 `(case go of NONE => emit_op GAS [] h3 | SOME g => (g,h3)) = (hg,h5)` >>
  `ci_mono sa s1 /\ ci_mono sha h1` by
    metis_tac[ci_mono_lower_value_compile_expr, SND] >>
  `ci_mono s1 s2 /\ ci_mono h1 h2` by
    metis_tac[ci_mono_compile_ext_call_args, cj 1 compile_expr_ci_mono, SND] >>
  `ci_mono s2 s3 /\ ci_mono h2 h3` by metis_tac[request_keyword_mono, SND] >>
  `ci_mono s3 s5 /\ ci_mono h3 h5` by metis_tac[request_optional_gas_mono, SND] >>
  `cs_extends s5 sb /\ cs_extends h5 shb` by metis_tac[request_pack_extends] >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\ cs_extends s3 s5 /\
   cs_extends sha h1 /\ cs_extends h1 h2 /\ cs_extends h2 h3 /\ cs_extends h3 h5` by
    fs[ci_mono_def] >>
  `fn_has_code sa s1 fn /\ fn_has_code s1 s2 fn /\ fn_has_code s2 s3 fn /\
   fn_has_code s3 s5 fn /\ fn_has_code s5 sb fn` by
    (irule request_head_code_slices >> simp[]) >>
  `fn_has_code sha h1 shfn /\ fn_has_code h1 h2 shfn /\ fn_has_code h2 h3 shfn /\
   fn_has_code h3 h5 shfn /\ fn_has_code h5 shb shfn` by
    (irule request_head_code_slices >> simp[]) >>
  qexistsl [`ao`,`av`,`vo`,`go`,`def`,`gas`,`s1`,`s2`,`s3`,`s5`,`h1`,`h2`,`h3`,`hg`,`h5`,`result`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* The shadow GAS instruction has the same output operand, but its state is
   kept separate; the request worker checks the generated instruction site. *)
Theorem request_optional_gas_pair[local]:
  gas_shadow_state a ah /\
  (case go of SOME g => (g,a) | NONE => emit_op GAS [] a) = (gas,b) /\
  (case go of SOME g => (g,ah) | NONE => emit_op GAS [] ah) = (hg,bh) ==>
  hg = gas /\ gas_shadow_state b bh
Proof
  Cases_on `go`
  >- (simp_tac bool_ss [optionTheory.option_case_def] >> strip_tac >>
      `gas_shadow_compiles (emit_op GAS []) (emit_op GAS [])` by
        (irule gas_shadow_compiles_emit_op >> simp[]) >>
      pop_assum (qspecl_then [`a`,`ah`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
      simp[]) >>
  simp_tac bool_ss [optionTheory.option_case_def, PAIR_EQ] >> strip_tac >> gvs[]
QED

(* The label-preservation rules give extension for the composite fragments
   without expanding their emitters or their ABI encoder/decoder. *)
Theorem request_buffer_cuts[local]:
  compile_external_call_kwargs ce ao av tys abi mid cap minsz retbytes stat
    value gas skip hasdef def rt dt adec a = (result,b) /\ fn_has_code a b fn ==>
  ?ba b1 b2 len b3 off sp sr u.
    compile_alloc_buffer ((if abi > cap then abi else cap) + 32) a = (ba,b1) /\
    emit_void MSTORE [ba.buf_operand;Lit (n2w mid)] b1 = ((),b2) /\
    (if av = [] then comp_return (Lit 4w) else
      comp_bind (emit_op ADD [ba.buf_operand;Lit 32w]) (\dst.
       comp_bind (compile_abi_encode_values_to_buf ce dst (ZIP (av,tys))) (\alen.
       emit_op ADD [alen;Lit 4w]))) b2 = (len,b3) /\
    emit_op ADD [ba.buf_operand;Lit 28w] b3 = (off,sp) /\
    comp_ignore_bind
      (if rt = NoneT /\ ~skip then compile_extcodesize_check ao else comp_return ())
      (comp_bind
        (if stat then emit_op STATICCALL [gas;ao;off;len;ba.buf_operand;Lit (n2w cap)]
         else emit_op CALL [gas;ao;value;off;len;ba.buf_operand;Lit (n2w cap)])
        (\success. comp_bind (fresh_label "extcall_fail") (\fail.
         comp_bind (fresh_label "extcall_cont") (\cont.
         comp_ignore_bind (emit_inst JNZ [success;Label cont;Label fail] [])
         (comp_ignore_bind (new_block fail)
         (comp_bind (emit_op RETURNDATASIZE []) (\rds.
          comp_bind (compile_alloc_buffer 0) (\fb.
          comp_ignore_bind (emit_void RETURNDATACOPY [fb.buf_operand;Lit 0w;rds])
          (comp_ignore_bind (emit_inst REVERT [fb.buf_operand;rds] [])
                            (new_block cont)))))))))) sp = (u,sr) /\
    (if rt = NoneT then comp_return (Lit 0w)
     else if hasdef then
       comp_bind (compile_alloc_buffer retbytes) (\r.
         compile_default_return_path ce rt dt ba.buf_operand r.buf_operand
           def ao skip minsz cap adec)
     else comp_bind (compile_alloc_buffer retbytes) (\r.
       comp_bind (compile_return_value_decode minsz cap) (\hi.
        comp_ignore_bind (compile_abi_decode_to_buf r.buf_operand (Lit 0w)
                           MLOAD ba.buf_operand hi adec)
                         (comp_return r.buf_operand)))) sr = (result,b) /\
    cs_extends a b1 /\ cs_extends b1 b2 /\ cs_extends b2 b3 /\
    cs_extends b3 sp /\ cs_extends sp sr /\ cs_extends sr b /\
    fn_has_code a b1 fn /\ fn_has_code b1 b2 fn /\ fn_has_code b2 b3 fn /\
    fn_has_code b3 sp fn /\ fn_has_code sp sr fn /\ fn_has_code sr b fn
Proof
  strip_tac >> drule extcall_request_buffer_layout >> strip_tac >>
  rename1 `compile_alloc_buffer _ a = (ba,b1)` >>
  rename1 `emit_void _ _ b1 = ((),b2)` >>
  rename1 `(if av = [] then _ else _) b2 = (len,b3)` >>
  `cs_extends a b1 /\ cs_extends b1 b2 /\ cs_extends b3 sp` by
    metis_tac[compile_alloc_buffer_labels, emit_void_labels, emit_op_labels, SND] >>
  `cs_extends b2 b3` by
    (qpat_assum `(if av = [] then _ else _) b2 = _` mp_tac >>
     qmatch_goalsub_abbrev_tac `f b2 = (len,b3)` >>
     `!s. cs_extends s (SND (f s)) /\ EVERY (isPREFIX "@") (added_labels s (SND (f s)))` by
       (gen_tac >> simp[Abbr `f`] >> IF_CASES_TAC
        >- simp[comp_return_labels] >>
        irule comp_bind_labels >> simp[emit_op_labels] >>
        gen_tac >> irule comp_bind_labels >>
        simp[compile_abi_encode_values_to_buf_labels,emit_op_labels]) >>
     first_x_assum (qspec_then `b2` mp_tac) >> simp[]) >>
  `cs_extends sp sr` by
    (qpat_assum `comp_ignore_bind _ _ sp = _` mp_tac >>
     qmatch_goalsub_abbrev_tac `f sp = (u,sr)` >>
     `!s. cs_extends s (SND (f s)) /\ EVERY (isPREFIX "@") (added_labels s (SND (f s)))` by
       (Cases_on `stat` >> gen_tac >> simp[Abbr `f`] >>
        irule comp_ignore_bind_labels >>
        (conj_tac >- (IF_CASES_TAC >> simp[comp_return_labels,compile_extcodesize_check_labels])) >>
        rpt (FIRST [irule fresh_label_bind_labels >> rpt gen_tac >> disch_tac,
                    irule comp_bind_labels >> conj_tac >> rpt gen_tac,
                    irule comp_ignore_bind_labels >> conj_tac >> rpt gen_tac] >> BETA_TAC >>
             simp[emit_inst_labels,emit_op_labels,emit_void_labels,compile_alloc_buffer_labels]) >>
        irule new_block_action_labels >> simp[]) >>
     first_x_assum (qspec_then `sp` mp_tac) >> simp[]) >>
  `cs_extends sr b` by
    (qpat_assum `(if rt = NoneT then _ else _) sr = _` mp_tac >>
     qmatch_goalsub_abbrev_tac `f sr = (result,b)` >>
     `!s. cs_extends s (SND (f s)) /\ EVERY (isPREFIX "@") (added_labels s (SND (f s)))` by
       (gen_tac >> simp[Abbr `f`] >> IF_CASES_TAC >- simp[comp_return_labels] >>
        IF_CASES_TAC >> irule comp_bind_labels >> simp[compile_alloc_buffer_labels] >>
        gen_tac >> simp[compile_default_return_path_labels] >>
        irule comp_bind_labels >> simp[compile_return_value_decode_labels] >>
        gen_tac >> irule comp_ignore_bind_labels >>
        simp[compile_abi_decode_labels,comp_return_labels]) >>
     first_x_assum (qspec_then `sr` mp_tac) >> simp[]) >>
  `fn_has_code a b1 fn /\ fn_has_code b1 b2 fn /\ fn_has_code b2 b3 fn /\
   fn_has_code b3 sp fn /\ fn_has_code sp sr fn /\ fn_has_code sr b fn` by
    (irule request_code_slices >> simp[]) >>
  qexistsl [`ba`,`b1`,`b2`,`len`,`b3`,`off`,`sp`,`sr`,`u`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Compiler-only interface to the address, positional, keyword, implicit gas,
   and packing runs. The last two real slices are passed to the return worker. *)
Theorem ext_request_compiler_cuts:
  compile_expr ce ty
    (Call ann (ExtCall stat skip (name,ats,rt) opts) (addr::tail) dr) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr
    (Call ann (ExtCall stat skip (name,ats,rt) opts) (addr::tail) dr)) sha = (vv,shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb fn /\ fn_has_code sha shb shfn ==>
  let xs = TAKE (LENGTH ats) tail;
      kws = DROP (LENGTH ats) tail;
      tys = MAP (lowered_value_type ce) xs;
      abi = abi_size_bound ce.ce_struct_fields (TupleT tys);
      rty = if needs_external_call_wrap rt then TupleT [rt] else rt;
      cap = abi_size_bound ce.ce_struct_fields rty;
      minsz = abi_static_size ce.ce_struct_fields rty;
      retbytes = type_memory_bytes ce rt;
      adec = type_to_abi_dec_info ce.ce_struct_fields ce rty
  in
  ?ao av vo go def gas s1 s2 s3 s5 h1 h2 h3 h5 result ba b1 b2 len b3 off sp sr u.
    let value = case vo of SOME v => v | NONE => Lit 0w;
        hasdef = IS_SOME def;
        defop = case def of SOME (d,dt) => d | NONE => Lit 0w;
        deft = case def of SOME (d,dt) => dt | NONE => rt
    in
    lower_value compile_expr ce (BaseT AddressT) addr sa = (ao,s1) /\
    lower_value compile_expr (gas_shadow_env T ce) (BaseT AddressT)
      (gas_shadow_expr addr) sha = (ao,h1) /\
    compile_ext_call_args compile_expr ce kws tys xs s1 = (av,s2) /\
    compile_ext_call_args compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr kws)
      tys (MAP gas_shadow_expr xs) h1 = (av,h2) /\
    compile_ext_call_kwargs compile_expr ce rt opts kws s2 = ((vo,go,def),s3) /\
    compile_ext_call_kwargs compile_expr (gas_shadow_env T ce) rt opts
      (MAP gas_shadow_expr kws) h2 = ((vo,go,def),h3) /\
    (case go of SOME g => (g,s3) | NONE => emit_op GAS [] s3) = (gas,s5) /\
    (case go of SOME g => (g,h3) | NONE => emit_op GAS [] h3) = (gas,h5) /\
    gas_shadow_state s1 h1 /\ gas_shadow_state s2 h2 /\
    gas_shadow_state s3 h3 /\ gas_shadow_state s5 h5 /\
    ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s5 /\
    cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\ cs_extends s3 s5 /\
    cs_extends sha h1 /\ cs_extends h1 h2 /\ cs_extends h2 h3 /\ cs_extends h3 h5 /\
    fn_has_code sa s1 fn /\ fn_has_code s1 s2 fn /\ fn_has_code s2 s3 fn /\
    fn_has_code s3 s5 fn /\ fn_has_code s5 sb fn /\
    fn_has_code sha h1 shfn /\ fn_has_code h1 h2 shfn /\
    fn_has_code h2 h3 shfn /\ fn_has_code h3 h5 shfn /\ fn_has_code h5 shb shfn /\
    compile_alloc_buffer ((if abi > cap then abi else cap) + 32) s5 = (ba,b1) /\
    emit_void MSTORE [ba.buf_operand;Lit (n2w (ce.ce_method_id name ats))] b1 = ((),b2) /\
    (if av = [] then comp_return (Lit 4w) else
      comp_bind (emit_op ADD [ba.buf_operand;Lit 32w]) (\dst.
       comp_bind (compile_abi_encode_values_to_buf ce dst (ZIP (av,tys))) (\alen.
       emit_op ADD [alen;Lit 4w]))) b2 = (len,b3) /\
    emit_op ADD [ba.buf_operand;Lit 28w] b3 = (off,sp) /\
    comp_ignore_bind
      (if rt = NoneT /\ ~skip then compile_extcodesize_check ao else comp_return ())
      (comp_bind
        (if stat then emit_op STATICCALL [gas;ao;off;len;ba.buf_operand;Lit (n2w cap)]
         else emit_op CALL [gas;ao;value;off;len;ba.buf_operand;Lit (n2w cap)])
        (\success. comp_bind (fresh_label "extcall_fail") (\fail.
         comp_bind (fresh_label "extcall_cont") (\cont.
         comp_ignore_bind (emit_inst JNZ [success;Label cont;Label fail] [])
         (comp_ignore_bind (new_block fail)
         (comp_bind (emit_op RETURNDATASIZE []) (\rds.
          comp_bind (compile_alloc_buffer 0) (\fb.
          comp_ignore_bind (emit_void RETURNDATACOPY [fb.buf_operand;Lit 0w;rds])
          (comp_ignore_bind (emit_inst REVERT [fb.buf_operand;rds] [])
                            (new_block cont)))))))))) sp = (u,sr) /\
    (if rt = NoneT then comp_return (Lit 0w)
     else if hasdef then
       comp_bind (compile_alloc_buffer retbytes) (\r.
         compile_default_return_path ce rt deft ba.buf_operand r.buf_operand
           defop ao skip minsz cap adec)
     else comp_bind (compile_alloc_buffer retbytes) (\r.
       comp_bind (compile_return_value_decode minsz cap) (\hi.
        comp_ignore_bind (compile_abi_decode_to_buf r.buf_operand (Lit 0w)
                           MLOAD ba.buf_operand hi adec)
                         (comp_return r.buf_operand)))) sr = (result,sb) /\
    vv = (if rt = NoneT then StackValue ann result
          else LocatedValue ann (mk_ptr result LocMemory)) /\
    cs_extends s5 b1 /\ cs_extends b1 b2 /\ cs_extends b2 b3 /\
    cs_extends b3 sp /\ cs_extends sp sr /\ cs_extends sr sb /\
    fn_has_code s5 b1 fn /\ fn_has_code b1 b2 fn /\ fn_has_code b2 b3 fn /\
    fn_has_code b3 sp fn /\ fn_has_code sp sr fn /\ fn_has_code sr sb fn
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all request_head_cuts >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all request_optional_gas_pair >> strip_tac >>
  qpat_x_assum `hg = gas` SUBST_ALL_TAC >>
  drule_all request_buffer_cuts >> strip_tac >>
  rename1 `compile_alloc_buffer _ s5 = (ba,b1)` >>
  rename1 `emit_void _ _ b1 = ((),b2)` >>
  rename1 `(if av = [] then _ else _) b2 = (len,b3)` >>
  qexistsl [`ao`,`av`,`vo`,`go`,`def`,`gas`,`s1`,`s2`,`s3`,`s5`,`h1`,`h2`,`h3`,`h5`,`result`,
            `ba`,`b1`,`b2`,`len`,`b3`,`off`,`sp`,`sr`,`u`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
