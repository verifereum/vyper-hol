Theory immutableDeployEmptyFixture
Ancestors
  immutableDeployEmptyProbe exprSimAggregates exprSimHypsDefs compileVyper supportedProgram
  stmtSimDefs exprLoweringProps compileEnv valueEncoding

Theorem empty_struct_vv_sim:
  !ctx func cenv cx env ann nsid ty es.
    expr_body_pre cenv cx env (StructLit ann nsid []) es ==>
    expr_vv_sim ctx func cenv cx ty (StructLit ann nsid []) es
Proof
  rpt strip_tac >>
  qspecl_then [`F`, `ctx`, `func`, `cenv`, `cx`, `ann`, `nsid`, `[]`]
    mp_tac compile_struct_lit_vv_case >>
  simp[exprs_case_def, expr_vv_case_def] >>
  disch_then drule >> simp[]
QED

Definition empty_immutable_tops_def:
  empty_immutable_tops =
    [StructDecl "Empty" [];
     VariableDecl Private Immutable "dst" (StructT (NONE,"Empty")) NONE;
     VariableDecl Private Immutable "neighbor" (BaseT (UintT 256)) NONE;
     FunctionDecl Deploy Payable F F "__init__" [] [] NoneT []]
End

Theorem empty_immutable_program_supported:
  supported_program empty_immutable_tops
Proof
  EVAL_TAC
QED

Theorem empty_immutable_destination_supported:
  supported_immutable_type empty_immutable_tops (NONE,"dst") =
    SOME (StructT (NONE,"Empty"))
Proof
  EVAL_TAC
QED

Theorem empty_immutable_layout_probe:
  add_immutable_locations (get_struct_fields (make_struct_fields_map empty_immutable_tops))
    empty_immutable_tops 0 FEMPTY =
    FEMPTY |+ ((NONE,"dst"),ImmutableLoc 0) |+
              ((NONE,"neighbor"),ImmutableLoc 0) /\
  compute_immutables_len (get_struct_fields (make_struct_fields_map empty_immutable_tops))
    empty_immutable_tops = 32
Proof
  EVAL_TAC
QED

Theorem empty_immutable_constructor_probe:
  classify_functions empty_immutable_tops =
    ([],[],NONE,SOME (Payable,F,F,"__init__",[],[],NoneT,[])) /\
  ctor_named_init (SOME (Payable,F,F,"__init__",[],[],NoneT,[])) /\
  fn_allocs_ok empty_immutable_tops
    (Payable,F,F,"__init__",[],[],NoneT,[])
Proof
  EVAL_TAC
QED

Theorem empty_immutable_deploy_boundary:
  lower_vyper_deploy_unit empty_immutable_tops policy [] =
    run_deploy_lowering T policy [] 32 [] 0 []
      ((build_compile_env empty_immutable_tops Deploy Payable "__init__"
          [] NoneT [] F) with
        <|ce_is_ctor := T; ce_raw_return := F;
          ce_target := policy.rpol_target|>)
      [] T F 0 F "__deploy"
Proof
  simp[lower_vyper_deploy_unit_def, empty_immutable_constructor_probe,
       empty_immutable_layout_probe, package_constructor_def,
       set_constructor_package_target_def, update_cenv_nonreentrant_def,
       build_positional_args_def] >>
  EVAL_TAC
QED

(* Normal completion fixes the returned environment, so an unchanged source
   integer immutable still constrains the staged memory, not just ISTORE's map. *)
Theorem normal_stmt_post_immutable_int_word:
  stmt_post ctx func cx lctx ce ce' sa sb s0 (INL ()) ee t /\
  ce'.ce_is_ctor /\
  FLOOKUP ce'.ce_module_vars (ce'.ce_module,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
             NONE => FEMPTY
           | SOME imms => get_source_immutables ce'.ce_module imms) name =
    SOME (tv,IntV n) ==>
  mem_word_at off t.vs_memory = val_to_w256 (IntV n)
Proof
  simp[stmt_post_def] >> rpt strip_tac >> gvs[] >>
  fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `immutables_rel _ _ _ _ _ _` mp_tac >>
  simp[immutables_rel_def] >>
  disch_then drule >> simp[val_in_memory_def]
QED

(* The declaration separation clause permits this layout at a frontier of 32.
   No allocation for the immutable buffer is required: its base is absolute 0. *)
Theorem empty_immutable_decl_sep_probe:
  get_tenv cx = FEMPTY |+ ((NONE,"Empty"),StructArgs []) ==>
  immutable_decl_sep
    (build_compile_env empty_immutable_tops Deploy Payable "__init__"
       [] NoneT [] F) cx [] FEMPTY FEMPTY 32
Proof
  strip_tac >>
  simp[immutable_decl_sep_def, build_compile_env_def,
       empty_immutable_tops_def] >>
  EVAL_TAC >> rpt gen_tac >>
  Cases_on `name = "dst"` >> Cases_on `name = "neighbor"` >>
  gvs[] >> rpt strip_tac >>
  gvs[empty_struct_evaluated_probe, vyperValueTheory.evaluate_type_def,
      valueEncodingTheory.type_memory_size_def]
QED

Theorem empty_immutable_alloca_sep_probe:
  get_tenv cx = FEMPTY |+ ((NONE,"Empty"),StructArgs []) ==>
  immutable_alloca_sep func
    (build_compile_env empty_immutable_tops Deploy Payable "__init__"
       [] NoneT [] F) cx
    (es with <|scopes := []; immutables := [(cx.txn.target,
       [(NONE,FEMPTY |+ ("dst",(StructTV [],StructV [])) |+
                       ("neighbor",(BaseTV (UintT 256),IntV 1)))])]|>)
    (s with <|vs_vars := FEMPTY; vs_allocas := FEMPTY; vs_alloca_next := 32|>)
Proof
  strip_tac >> simp[immutable_alloca_sep_def, empty_immutable_decl_sep_probe] >>
  simp[build_compile_env_def, empty_immutable_tops_def,
       vyperStateTheory.get_source_immutables_def, local_region_def,
       vyperStateTheory.lookup_scopes_def] >>
  EVAL_TAC >> rpt gen_tac >>
  Cases_on `name = "dst"` >> Cases_on `name = "neighbor"` >>
  gvs[] >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

