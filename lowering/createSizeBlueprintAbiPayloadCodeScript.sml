(* Pair the ABI payload's compiler intervals without reselecting its rows. *)
Theory createSizeBlueprintAbiPayloadCode
Ancestors
  createSizeRawPairedCode createSizeItinerary exprSimFullBundleProps
  exprLowering externalEntryShape fragExec compileEnv
  gasShadow gasShadowState gasShadowCompile gasShadowCompileHelpers gasShadowCompileBase
  gasShadowCompileContext gasShadowCompilePure
  list pair

Theorem blueprint_abi_shadow_actions[local]:
  xs <> [] /\
  compile_create_ctor_args compile_expr ce xs ca = (vals,k) /\
  compile_alloc_buffer (abi_size_bound ce.ce_struct_fields
    (TupleT (MAP (lowered_value_type ce) xs))) k = (buf,m) /\
  compile_abi_encode_values_to_buf ce buf.buf_operand
    (ZIP (vals,MAP (lowered_value_type ce) xs)) m = (len,b) /\
  gas_shadow_state ca hca /\
  compile_create_blueprint_args compile_expr ce F (MAP gas_shadow_expr later)
    (MAP gas_shadow_expr xs) hca = ((buf.buf_operand,len),hb) ==>
  ?hk hm.
    compile_create_ctor_args compile_expr ce (MAP gas_shadow_expr xs) hca = (vals,hk) /\
    compile_alloc_buffer (abi_size_bound ce.ce_struct_fields
      (TupleT (MAP (lowered_value_type ce) xs))) hk = (buf,hm) /\
    compile_abi_encode_values_to_buf ce buf.buf_operand
      (ZIP (vals,MAP (lowered_value_type ce) xs)) hm = (len,hb) /\
    gas_shadow_state k hk /\ gas_shadow_state m hm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `gas_shadow_compiles (compile_create_ctor_args compile_expr ce xs)
     (compile_create_ctor_args compile_expr ce (MAP gas_shadow_expr xs))` by
    (irule (SRULE [gas_shadow_env_F]
      (Q.INST [`sd` |-> `F`, `sh` |-> `T`] gas_shadow_compiles_create_ctor_args)) >>
     simp[gas_shadow_compile_expr]) >>
  Cases_on `compile_create_ctor_args compile_expr ce (MAP gas_shadow_expr xs) hca` >>
  rename1 `compile_create_ctor_args _ _ _ hca = (hvals,hk)` >>
  fs[gas_shadow_compiles_def] >> first_x_assum drule >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `compile_alloc_buffer cap k = (buf,m)` >>
  Cases_on `compile_alloc_buffer cap hk` >>
  rename1 `compile_alloc_buffer cap hk = (hbuf,hm)` >>
  mp_tac (Q.INST [`nbytes` |-> `cap`] gas_shadow_compiles_alloc_buffer) >>
  simp[gas_shadow_compiles_def] >> disch_then drule >> simp[] >> strip_tac >>
  `MAP (lowered_value_type ce) (MAP gas_shadow_expr xs) =
   MAP (lowered_value_type ce) xs` by
    simp[MAP_MAP_o,combinTheory.o_DEF,SF ETA_ss] >>
  gvs[compile_create_blueprint_args_def,comp_bind_def,comp_return_def] >>
  pairarg_tac >> gvs[]
QED

Theorem blueprint_abi_action_code[local]:
  compile_create_ctor_args compile_expr ce xs ca = (vals,k) /\
  compile_alloc_buffer cap k = (buf,m) /\
  compile_abi_encode_values_to_buf ce buf.buf_operand rows m = (len,b) /\
  fn_has_code ca b fn ==>
  fn_has_code ca k fn /\ fn_has_code k m fn /\ fn_has_code m b fn
Proof
  strip_tac >>
  `cs_extends ca k` by
    (qspecl_then [`compile_expr`,`ce`,`xs`,`ca`] mp_tac compile_create_ctor_args_labels >>
     simp[compile_expr_labels]) >>
  `cs_extends k m` by
    (qspecl_then [`cap`,`k`,`\s. T`] mp_tac compile_alloc_buffer_labels >> simp[]) >>
  `cs_extends m b` by
    (qspecl_then [`ce`,`buf.buf_operand`,`rows`,`m`] mp_tac
       compile_abi_encode_values_to_buf_labels >> simp[]) >>
  `cs_extends k b` by metis_tac[cs_extends_trans] >>
  `fn_has_code ca k fn /\ fn_has_code k b fn` by metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]
QED

Theorem create_blueprint_abi_payload_paired_code:
  xs <> [] /\
  compile_create_ctor_args compile_expr ce xs ca = (vals,k) /\
  create_itinerary_ctor_rows ce xs vals ca k cs mid vvs /\
  compile_alloc_buffer (abi_size_bound ce.ce_struct_fields
    (TupleT (MAP (lowered_value_type ce) xs))) k = (buf,m) /\
  compile_abi_encode_values_to_buf ce buf.buf_operand
    (ZIP (vals,MAP (lowered_value_type ce) xs)) m = (len,b) /\
  compile_create_blueprint_args compile_expr ce F (MAP gas_shadow_expr later)
    (MAP gas_shadow_expr xs) hca = ((buf.buf_operand,len),hb) /\
  expr_sim_full_code (ctx,sctx,fnc,sfn) (ca,b,hca,hb) ==>
  ?hk hm hcs hmid.
    compile_create_ctor_args compile_expr ce (MAP gas_shadow_expr xs) hca = (vals,hk) /\
    compile_alloc_buffer (abi_size_bound ce.ce_struct_fields
      (TupleT (MAP (lowered_value_type ce) xs))) hk = (buf,hm) /\
    compile_abi_encode_values_to_buf ce buf.buf_operand
      (ZIP (vals,MAP (lowered_value_type ce) xs)) hm = (len,hb) /\
    expr_sim_full_code (ctx,sctx,fnc,sfn) (ca,k,hca,hk) /\
    expr_sim_full_code (ctx,sctx,fnc,sfn) (k,m,hk,hm) /\
    expr_sim_full_code (ctx,sctx,fnc,sfn) (m,b,hm,hb) /\
    LENGTH hcs = SUC (LENGTH xs) /\ HD hcs = hca /\ LAST hcs = hk /\
    LENGTH hmid = LENGTH xs /\
    !i. i < LENGTH xs ==>
      compile_expr ce (expr_type (EL i xs)) (gas_shadow_expr (EL i xs)) (EL i hcs) =
        (EL i vvs,EL i hmid) /\
      compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) xs))
        (ext_call_arg_value (lowered_value_type ce (EL i xs)) (EL i vvs)) (EL i hmid) =
        (EL i vals,EL (SUC i) hcs) /\
      expr_sim_full_code (ctx,sctx,fnc,sfn) (EL i cs,EL i mid,EL i hcs,EL i hmid) /\
      expr_sim_full_code (ctx,sctx,fnc,sfn) (EL i mid,EL (SUC i) cs,EL i hmid,EL (SUC i) hcs) /\
      expr_sim_full_code (ctx,sctx,fnc,sfn) (EL i cs,EL (SUC i) cs,EL i hcs,EL (SUC i) hcs)
Proof
  disch_then (strip_assume_tac o REWRITE_RULE [expr_sim_full_code_def]) >>
  drule_all blueprint_abi_shadow_actions >> strip_tac >>
  `fn_has_code ca k fnc /\ fn_has_code k m fnc /\ fn_has_code m b fnc` by
    (irule blueprint_abi_action_code >> rpt (goal_assum (drule_at Any))) >>
  `fn_has_code hca hk sfn /\ fn_has_code hk hm sfn /\ fn_has_code hm hb sfn` by
    (irule blueprint_abi_action_code >> rpt (goal_assum (drule_at Any))) >>
  drule_all raw_shadow_ctor_code >> strip_tac >>
  qexistsl_tac [`hk`,`hm`,`hcs`,`hmid`] >> simp[expr_sim_full_code_def]
QED
