(* The evaluator visits constructor arguments before the amount/salt/offset
   suffix. The compiler has corresponding, paired cuts for both raw modes. *)
Theory bodyCreateBlueprintLayoutMods
Ancestors
  exprBodyPreProps exprSimHypsDefs vyperTypeSystem vyperAST vyperCreate
  exprLowering exprLoweringProps exprSimSend builtinCreate compileEnv fragExec
  gasShadow gasShadowState gasShadowCompile gasShadowCompileHelpers
  gasShadowCompileStmtHelpers gasShadowCompileBuiltinCreate
  blueprintLiteralOffsetProps externalEntryShape list pair
Libs
  pairLib

Theorem blueprint_layout_mods:
  expr_body_pre_mods mods ce cx env
    (Call ann (CreateTarget (CreateFromBlueprint raw) salted rof ks) args dflt) es ==>
  ann = BaseT AddressT /\
  ?target amount salts offset ctor.
    args = target :: amount :: (salts ++ offset :: ctor) /\
    create_operand_order (CreateFromBlueprint raw) salted args =
      target :: (ctor ++ amount :: (salts ++ [offset])) /\
    expr_type target = BaseT AddressT /\
    expr_type amount = BaseT (UintT 256) /\
    expr_type offset = BaseT (UintT 256) /\
    (if salted then
       ?salt. salts = [salt] /\ expr_type salt = BaseT (BytesT (Fixed 32))
     else salts = []) /\
    LENGTH salts = (if salted then 1 else 0) /\
    (raw ==> ?e n. ctor = [e] /\ expr_type e = BaseT (BytesT (Dynamic n)))
Proof
  disch_then (mp_tac o MATCH_MP expr_body_pre_mods_well_typed) >>
  Cases_on `salted` >>
  simp[well_typed_expr_def, create_arg_types_ok_def, MAP_EQ_CONS] >>
  strip_tac >> gvs[]
  >- (rename1 `expr_type salt = BaseT (BytesT (Fixed 32))` >>
      qexists_tac `[salt]` >> simp[create_operand_order_def] >>
      metis_tac[MAP_EQ_CONS, MAP_EQ_NIL]) >>
  simp[create_operand_order_def] >> metis_tac[MAP_EQ_CONS, MAP_EQ_NIL]
QED

Theorem blueprint_lower_call[local]:
  lower_value compile_expr ce ty
    (Call ann (CreateTarget (CreateFromBlueprint raw) salted rof ks) args dflt) =
  compile_create_call compile_expr ce (CreateFromBlueprint raw) salted rof args
Proof
  simp[FUN_EQ_THM, lower_value_def, compile_expr_call, compile_call_def,
       unwrap_value_def, as_stack_val_def, comp_bind_def, comp_return_def] >>
  qx_gen_tac `a` >>
  Cases_on `compile_create_call compile_expr ce (CreateFromBlueprint raw) salted rof args a` >>
  simp[as_stack_val_def, unwrap_value_def, comp_return_def]
QED

Theorem blueprint_compile_parts_mods[local]:
  LENGTH salts = (if salted then 1 else 0) /\
  lower_value compile_expr ce ty
    (Call ann (CreateTarget (CreateFromBlueprint raw) salted rof ks)
      (target::amount::(salts ++ offset::ctor)) dflt) sa = (result,sb) ==>
  ?x y sop p n off sz a b c d f k.
    lower_value compile_expr ce (expr_type target) target sa = (x,a) /\
    compile_create_blueprint_args compile_expr ce raw
      (amount::(salts ++ [offset])) ctor a = ((p,n),b) /\
    lower_value compile_expr ce (expr_type amount) amount b = (y,c) /\
    compile_create_salt compile_expr ce (if salted then SOME (HD salts) else NONE)
      c = (sop,d) /\
    (case expr_int_literal (origin_fold_value offset) of
       SOME i => comp_return (Lit (i2w i))
     | NONE => lower_value compile_expr ce (expr_type offset) offset) d = (off,f) /\
    compile_create_blueprint_check (IS_SOME (expr_int_literal (origin_fold_value offset)))
      x off f = (sz,k) /\
    compile_create_blueprint_append x y sop off sz p n rof k = (result,sb)
Proof
  rewrite_tac[blueprint_lower_call, GSYM blueprint_offset_form] >>
  Cases_on `salted` >>
  simp[LENGTH_EQ_NUM_compute, compile_create_call_def, comp_bind_def] >>
  strip_tac >> gvs[compile_create_call_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[comp_bind_def]) >>
  rpt (goal_assum (drule_at Any))
QED

(* Transport a single normal cut; no second expansion of the shadow compiler. *)
Theorem blueprint_transport_cut[local]:
  gas_shadow_compiles f g /\ gas_shadow_state a ha /\ f a = (v,b) ==>
  ?hb. g ha = (v,hb) /\ gas_shadow_state b hb
Proof
  simp[gas_shadow_compiles_def] >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  Cases_on `g ha` >> gvs[]
QED

Theorem blueprint_shadow_args[local]:
  gas_shadow_compiles
    (compile_create_blueprint_args compile_expr ce raw later ctor)
    (compile_create_blueprint_args compile_expr (gas_shadow_env T ce) raw
       (MAP gas_shadow_expr later) (MAP gas_shadow_expr ctor))
Proof
  irule (SRULE [] (Q.INST [`sh` |-> `T`] gas_shadow_compiles_create_blueprint_args)) >>
  simp[cj 1 gas_shadow_compile_expr_env]
QED

Theorem blueprint_shadow_salt[local]:
  gas_shadow_compiles (compile_create_salt compile_expr ce salt)
    (compile_create_salt compile_expr (gas_shadow_env T ce)
       (OPTION_MAP gas_shadow_expr salt))
Proof
  irule (SRULE [] (Q.INST [`sh` |-> `T`] gas_shadow_compiles_create_salt)) >>
  simp[cj 1 gas_shadow_compile_expr_env]
QED

Theorem blueprint_shadow_offset[local]:
  gas_shadow_compiles
    (case lit of SOME i => comp_return (Lit (i2w i))
                | NONE => lower_value compile_expr ce (expr_type offset) offset)
    (case lit of SOME i => comp_return (Lit (i2w i))
                | NONE => lower_value compile_expr (gas_shadow_env T ce)
                             (expr_type offset) (gas_shadow_expr offset))
Proof
  Cases_on `lit` >> simp[gas_shadow_compiles_return, gas_shadow_stmt_lower_value_env]
QED

Theorem blueprint_compile_cuts_mods:
  gas_shadow_state sa sh /\
  lower_value compile_expr ce ty
    (Call ann (CreateTarget (CreateFromBlueprint raw) salted rof ks)
      (target::amount::(salts ++ offset::ctor)) dflt) sa = (result,sb) /\
  lower_value compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (Call ann (CreateTarget (CreateFromBlueprint raw) salted rof ks)
      (target::amount::(salts ++ offset::ctor)) dflt)) sh = (result,shb) /\
  LENGTH salts = (if salted then 1 else 0) ==>
  ?x y sop p n off sz a b c d f k ha hb hc hd hf hk.
    lower_value compile_expr ce (expr_type target) target sa = (x,a) /\
    compile_create_blueprint_args compile_expr ce raw
      (amount::(salts ++ [offset])) ctor a = ((p,n),b) /\
    lower_value compile_expr ce (expr_type amount) amount b = (y,c) /\
    compile_create_salt compile_expr ce (if salted then SOME (HD salts) else NONE)
      c = (sop,d) /\
    (case expr_int_literal (origin_fold_value offset) of
       SOME i => comp_return (Lit (i2w i))
     | NONE => lower_value compile_expr ce (expr_type offset) offset) d = (off,f) /\
    compile_create_blueprint_check (IS_SOME (expr_int_literal (origin_fold_value offset)))
      x off f = (sz,k) /\
    compile_create_blueprint_append x y sop off sz p n rof k = (result,sb) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type target)
      (gas_shadow_expr target) sh = (x,ha) /\
    compile_create_blueprint_args compile_expr (gas_shadow_env T ce) raw
      (MAP gas_shadow_expr (amount::(salts ++ [offset])))
      (MAP gas_shadow_expr ctor) ha = ((p,n),hb) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type amount)
      (gas_shadow_expr amount) hb = (y,hc) /\
    compile_create_salt compile_expr (gas_shadow_env T ce)
      (OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)) hc = (sop,hd) /\
    (case expr_int_literal (origin_fold_value offset) of
       SOME i => comp_return (Lit (i2w i))
     | NONE => lower_value compile_expr (gas_shadow_env T ce) (expr_type offset)
                  (gas_shadow_expr offset)) hd = (off,hf) /\
    compile_create_blueprint_check (IS_SOME (expr_int_literal (origin_fold_value offset)))
      x off hf = (sz,hk) /\
    compile_create_blueprint_append x y sop off sz p n rof hk = (result,shb) /\
    gas_shadow_state a ha /\ gas_shadow_state b hb /\ gas_shadow_state c hc /\
    gas_shadow_state d hd /\ gas_shadow_state f hf /\ gas_shadow_state k hk
Proof
  strip_tac >> drule_all_then strip_assume_tac blueprint_compile_parts_mods >>
  qpat_assum `lower_value _ _ _ target sa = _`
    (mp_then Any (drule_all_then (qx_choose_then `ha` strip_assume_tac))
      (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] blueprint_transport_cut)
        (Q.INST [`sd` |-> `T`] gas_shadow_stmt_lower_value_env))) >>
  drule_all_then (qx_choose_then `hb` strip_assume_tac)
    (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] blueprint_transport_cut)
      blueprint_shadow_args) >>
  qpat_assum `lower_value _ _ _ amount _ = _`
    (mp_then Any (drule_all_then (qx_choose_then `hc` strip_assume_tac))
      (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] blueprint_transport_cut)
        (Q.INST [`sd` |-> `T`] gas_shadow_stmt_lower_value_env))) >>
  drule_all_then (qx_choose_then `hd` strip_assume_tac)
    (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] blueprint_transport_cut)
      blueprint_shadow_salt) >>
  drule_all_then (qx_choose_then `hf` strip_assume_tac)
    (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] blueprint_transport_cut)
      blueprint_shadow_offset) >>
  drule_all_then (qx_choose_then `hk` strip_assume_tac)
    (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] blueprint_transport_cut)
      gas_shadow_compiles_create_blueprint_check) >>
  drule_all_then (qx_choose_then `hend` strip_assume_tac)
    (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] blueprint_transport_cut)
      gas_shadow_compiles_create_blueprint_append) >>
  `hend = shb` by
    (qpat_x_assum `lower_value _ _ _ (gas_shadow_expr (Call _ _ _ _)) _ = _` mp_tac >>
     simp[Once gas_shadow_expr_def, MAP_APPEND, blueprint_lower_call] >>
     Cases_on `salted` >> gvs[LENGTH_EQ_NUM_compute] >>
     gvs[compile_create_call_def, comp_bind_def, blueprint_offset_form,
         gas_shadow_origin_fold_value, gasShadowCompilePureTheory.gas_shadow_expr_int_literal,
         gas_shadow_expr_type]) >>
  qexistsl_tac [`x`,`y`,`sop`,`p`,`n`,`off`,`sz`,`a`,`b`,`c`,`d`,`f`,`k`,
                `ha`,`hb`,`hc`,`hd`,`hf`,`hk`] >>
  simp[] >> gvs[]
QED

(* Apply to the normal or the shadow chain. Keep the check and append
   intervals separate, as well as their union for the preparation proof. *)
Theorem blueprint_cut_code_mods:
  lower_value compile_expr ce ty target sa = (x,a) /\
  compile_create_blueprint_args compile_expr ce raw later ctor a = ((p,n),b) /\
  lower_value compile_expr ce ty' amount b = (y,c) /\
  compile_create_salt compile_expr ce salt c = (sop,d) /\
  (case lit of SOME i => comp_return (Lit (i2w i))
             | NONE => lower_value compile_expr ce ty'' offset) d = (off,f) /\
  compile_create_blueprint_check (IS_SOME lit) x off f = (sz,k) /\
  compile_create_blueprint_append x y sop off sz p n rof k = (result,sb) /\
  fn_has_code sa sb func ==>
  ci_mono sa a /\ ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d f /\
  fn_has_code sa a func /\ fn_has_code a b func /\ fn_has_code b c func /\
  fn_has_code c d func /\ fn_has_code d f func /\ fn_has_code f k func /\
  fn_has_code k sb func /\ fn_has_code f sb func
Proof
  strip_tac >>
  `ci_mono sa a /\ ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d f` by
    (rpt conj_tac
     >- metis_tac[ci_mono_lower_value_compile_expr, SND]
     >- metis_tac[ci_mono_compile_create_blueprint_args, compile_expr_ci_mono, SND]
     >- metis_tac[ci_mono_lower_value_compile_expr, SND]
     >- metis_tac[ci_mono_compile_create_salt, compile_expr_ci_mono, SND] >>
     Cases_on `lit` >> gvs[comp_return_def, ci_mono_refl] >>
     metis_tac[ci_mono_lower_value_compile_expr, SND]) >>
  asm_rewrite_tac[] >>
  `cs_extends f k` by
    metis_tac[externalEntryShapeTheory.compile_create_blueprint_check_labels, SND] >>
  `cs_extends k sb` by
    metis_tac[externalEntryShapeTheory.compile_create_blueprint_append_labels, SND] >>
  fs[ci_mono_def] >>
  ntac 3 (imp_res_tac cs_extends_trans) >>
  qpat_assum `fn_has_code sa sb func` (fn whole =>
    rpt conj_tac >> irule fn_has_code_mid >> irule_at Any whole >> simp[cs_extends_refl])
QED

(* The literal-mode bit below is the evaluator's own test on the original
   arguments. The compile cuts retain the compiler's folded offset separately. *)
Theorem blueprint_read_operand_order_mods:
  LENGTH salts = (if salted then 1 else 0) ==>
  bind (eval_expr cx (Call ann (CreateTarget (CreateFromBlueprint raw) salted rof ks)
          (target::amount::(salts ++ offset::ctor)) dflt)) (read_result cx) =
  bind (eval_exprs cx (target :: (ctor ++ amount :: (salts ++ [offset]))))
    (\values. bind (eval_create_operands cx (CreateFromBlueprint raw) salted rof
      (MAP expr_type (target::amount::(salts ++ offset::ctor)))
      (blueprint_literal_offset cx salted (target::amount::(salts ++ offset::ctor))) values)
      (read_result cx))
Proof
  Cases_on `salted` >>
  simp[LENGTH_EQ_NUM_compute, Once vyperInterpreterTheory.evaluate_def,
       vyperStateTheory.bind_assoc, create_operand_order_def] >>
  strip_tac >> gvs[]
QED
