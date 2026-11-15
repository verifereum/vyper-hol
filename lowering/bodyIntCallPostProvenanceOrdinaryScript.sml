(* Restricted ordinary simulation: only effect-free expressions. *)
Theory bodyIntCallPostProvenanceOrdinary
Ancestors
  bodyIntCallPostProvenanceCallbacks bodyIntCallArgType
  exprSimName exprSimLeaves exprSimOperators exprSimPlaces exprSimAggregates
  exprSimAttribute
  exprSimBuiltins exprSimWordBuiltins exprSimCalldataSlice exprSimPrecompiles
  exprSimLen exprSimSlice exprSimECArith exprCallBounds
  exprSimHypsDefs exprSimHyps vyperTypeSystem vyperTypeCallGraph
  exprSimTopLevel exprSimMapDefs exprSimSubscriptMap exprSimFlagWord
  exprSimBopInLiteralWord exprSimBopHeld exprSimSliceSelfCode
  exprCallbackContracts loweringPosts vyperAST list compileEnv

Theorem ordinary_exprs_lift[local]:
  !args. EVERY (\e. expr_sim_case nc ctx fn ce cx e /\
                   expr_vv_case nc ctx fn ce cx e) args ==>
         exprs_case nc ctx fn ce cx args
Proof
  Induct >> simp[exprs_case_def]
QED

Theorem ordinary_builtin_dispatch[local]:
  (!b. bi <> Bop b) /\ (!t n. bi <> MakeArray t n) /\
  exprs_case nc ctx fn ce cx args /\
  slice_extcode_case nc ctx fn ce cx args ==>
  expr_vv_case nc ctx fn ce cx (Builtin ann bi args)
Proof
  strip_tac >> Cases_on `bi`
  >~ [`expr_vv_case _ _ _ _ _ (Builtin _ (Bop _) _)`] >- gvs[]
  >~ [`expr_vv_case _ _ _ _ _ (Builtin _ (MakeArray _ _) _)`] >- gvs[]
  >~ [`Env _`]
  >- (irule expr_vv_case_nil >> conj_tac
      >- rw[expr_body_pre_def, well_typed_expr_def,
            well_typed_builtin_app_def, int_calls_expr_def] >>
      metis_tac[expr_ok_def, compile_env_case_ok])
  >~ [`Floor`] >- (irule word_builtin_case >> simp[])
  >~ [`AsWeiValue _`] >- (irule word_builtin_case >> simp[])
  >~ [`AddMod`] >- (irule word_builtin_case >> simp[])
  >~ [`MulMod`] >- (irule word_builtin_case >> simp[])
  >~ [`PowMod256`] >- (irule word_builtin_case >> simp[])
  >~ [`Len`] >- simp[compile_len_case]
  >~ [`CalldataLen`] >- simp[compile_calldata_len_case]
  >~ [`CalldataSlice _`] >- simp[compile_calldata_slice_call_case]
  >~ [`Not`] >- simp[compile_not_case]
  >~ [`Neg`] >- simp[compile_neg_case]
  >~ [`Abs`] >- simp[compile_abs_case]
  >~ [`Keccak256`] >- simp[compile_keccak256_case]
  >~ [`Sha256`] >- simp[compile_sha256_case]
  >~ [`Concat _`] >- simp[compile_concat_case]
  >~ [`Slice _`] >- (irule compile_slice_case >> simp[])
  >~ [`Uint2Str _`] >- simp[compile_uint2str_case]
  >~ [`Ceil`] >- simp[compile_ceil_case]
  >~ [`BlockHash`] >- simp[compile_blockhash_case]
  >~ [`BlobHash`] >- simp[compile_blobhash_case]
  >~ [`Acc _`] >- simp[compile_acc_case]
  >~ [`MethodId`] >- simp[compile_method_id_case]
  >~ [`ECRecover`] >- simp[compile_ecrecover_call_case]
  >~ [`ECAdd`] >- simp[compile_ecadd_call_case]
  >~ [`ECMul`] >- simp[compile_ecmul_call_case]
QED

Theorem ordinary_type_builtin_dispatch[local]:
  exprs_case nc ctx fn ce cx args /\
  ~EXISTS expr_has_effect args ==>
  expr_vv_case nc ctx fn ce cx (TypeBuiltin ann tb ty args)
Proof
  strip_tac >> Cases_on `tb`
  >~ [`MaxValue`] >- simp[compile_bound_builtin_case]
  >~ [`MinValue`] >- simp[compile_bound_builtin_case]
  >~ [`Epsilon`] >- simp[compile_bound_builtin_case]
  >~ [`Empty`] >- simp[compile_empty_case]
  >~ [`Convert`]
  >- (irule compile_convert_case >> simp[] >> rpt strip_tac >> gvs[])
  >~ [`Extract32`] >- simp[compile_extract32_case]
  >~ [`AbiDecode _`] >- simp[compile_abi_decode_case]
  >~ [`AbiEncode _ _`] >- simp[compile_abi_encode_case]
QED

Theorem ordinary_list_below[local]:
  (!e. expr_size e < bound /\ ~expr_has_effect e ==>
       expr_sim_case nc ctx fn ce cx e /\ expr_vv_case nc ctx fn ce cx e) /\
  (!e. MEM e args ==> expr_size e < bound) /\
  ~EXISTS expr_has_effect args ==>
  exprs_case nc ctx fn ce cx args
Proof
  strip_tac >> irule ordinary_exprs_lift >>
  gvs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED

Theorem ordinary_slice_below[local]:
  (!e. expr_size e < list_size expr_size args /\ ~expr_has_effect e ==>
       expr_sim_case nc ctx fn ce cx e /\ expr_vv_case nc ctx fn ce cx e) /\
  ~EXISTS expr_has_effect args ==>
  slice_extcode_case nc ctx fn ce cx args
Proof
  rw[slice_extcode_case_def] >> gvs[] >>
  `~expr_has_effect a /\ ~expr_has_effect start /\ ~expr_has_effect len`
    by gvs[] >>
  `exprs_case nc ctx fn ce cx [start; len]` by
    (irule ordinary_list_below >> simp[] >>
     qexists_tac `list_size expr_size [Builtin ct (Acc Code) [a]; start; len]` >>
     simp[list_size_def, expr_size_def] >> rpt strip_tac >> gvs[]) >>
  simp[] >> first_x_assum irule >> simp[list_size_def, expr_size_def]
QED

Theorem ordinary_nonword_membership[local]:
  ~is_word_type (expr_type e1) /\ (bop = In \/ bop = NotIn) ==>
  expr_vv_case nc ctx fn ce cx
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems])
Proof
  strip_tac >> rw[expr_vv_case_def, expr_body_pre_def] >>
  qpat_x_assum `well_typed_expr _ (Builtin _ _ _)` mp_tac >>
  simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
  strip_tac >>
  gvs[well_typed_binop_def, GSYM membership_element_word_boundary,
      is_prim_word_type_def]
QED

Theorem ordinary_bop_below[local]:
  (!e. expr_size e < list_size expr_size args /\ ~expr_has_effect e ==>
       expr_sim_case nc ctx fn ce cx e /\ expr_vv_case nc ctx fn ce cx e) /\
  ~EXISTS expr_has_effect args ==>
  expr_sim_case nc ctx fn ce cx (Builtin ann (Bop bop) args) /\
  expr_vv_case nc ctx fn ce cx (Builtin ann (Bop bop) args)
Proof
  strip_tac >> Cases_on `?e1 e2. args = [e1; e2]`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      Cases_on `(bop = In \/ bop = NotIn) /\
                ?a t n elems. e2 = Builtin a (MakeArray t n) elems`
      >- (pop_assum strip_assume_tac >> gvs[] >>
          (Cases_on `is_word_type (expr_type e1)`
          >- (irule compile_bop_in_literal_word_case >> simp[] >>
              irule ordinary_list_below >> simp[] >>
              qexists_tac `list_size expr_size [e1; Builtin a (MakeArray t n) elems]` >>
              conj_tac >- simp[list_size_def, expr_size_def] >>
              rpt strip_tac >> gvs[] >>
              drule expr_list_member_bound >> simp[]) >>
          conj_tac
          >- (irule expr_sim_case_of_vv >> simp[ordinary_nonword_membership]) >>
          simp[ordinary_nonword_membership])) >>
      irule compile_bop_case >> simp[] >>
      `expr_sim_case nc ctx fn ce cx e1 /\ expr_vv_case nc ctx fn ce cx e1`
        by (first_x_assum irule >> simp[list_size_def]) >>
      `expr_sim_case nc ctx fn ce cx e2 /\ expr_vv_case nc ctx fn ce cx e2`
        by (first_x_assum irule >> simp[list_size_def]) >>
      simp[] >> metis_tac[]) >>
  irule compile_bop_args_case >> gvs[]
QED

Theorem ordinary_builtin_below[local]:
  acyclic_struct_metadata ce.ce_struct_fields /\
  (!e. expr_size e < list_size expr_size args /\ ~expr_has_effect e ==>
       expr_sim_case nc ctx fn ce cx e /\ expr_vv_case nc ctx fn ce cx e) /\
  ~EXISTS expr_has_effect args ==>
  expr_sim_case nc ctx fn ce cx (Builtin ann bi args) /\
  expr_vv_case nc ctx fn ce cx (Builtin ann bi args)
Proof
  strip_tac >>
  `exprs_case nc ctx fn ce cx args` by
    (irule ordinary_exprs_lift >>
     gvs[EVERY_MEM, EXISTS_MEM] >> rpt gen_tac >> strip_tac >>
     first_x_assum irule >> simp[expr_list_member_bound]) >>
  Cases_on `?bop. bi = Bop bop`
  >- (gvs[] >> irule ordinary_bop_below >> simp[]) >>
  Cases_on `?t n. bi = MakeArray t n`
  >- (gvs[] >> irule compile_make_array_case >> simp[] >>
      rpt strip_tac >> disj1_tac >> irule effect_free_int_calls >>
      gvs[EVERY_MEM] >> metis_tac[]) >>
  `expr_vv_case nc ctx fn ce cx (Builtin ann bi args)` suffices_by
    simp[expr_sim_case_of_vv] >>
  irule ordinary_builtin_dispatch >> conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >> simp[] >>
  irule ordinary_slice_below >> gvs[]
QED

Theorem ordinary_effect_free_mutual[local]:
  !e ce nc ctx fn cx.
    acyclic_struct_metadata ce.ce_struct_fields /\ ~expr_has_effect e ==>
    (expr_sim_case nc ctx fn ce cx e /\ expr_vv_case nc ctx fn ce cx e) /\
    expr_map_case nc ctx fn ce cx e
Proof
  measureInduct_on `expr_size e` >> rpt gen_tac >> strip_tac >>
  reverse conj_tac
  >- (Cases_on `e`
      >~ [`TopLevelName _ _`] >- simp[compile_toplevel_map_case]
      >~ [`Subscript _ obj idx`]
      >- (irule compile_subscript_map_map_case >> reverse conj_tac
          >- gvs[] >>
          gvs[]) >>
      irule expr_map_case_other >> simp[]) >>
  Cases_on `e` >> gvs[]
  >~ [`Name _ _`]
  >- (irule expr_case_of_ok >> simp[compile_name_case_sim, int_calls_expr_def])
  >~ [`Literal _ _`]
  >- (irule expr_case_of_ok >> simp[compile_literal_case_sim, int_calls_expr_def])
  >~ [`FlagMember _ _ _`]
  >- (irule expr_case_of_ok >> simp[compile_flag_member_case_sim, int_calls_expr_def])
  >~ [`TopLevelName _ _`]
  >- (conj_tac >- (irule expr_sim_case_of_vv >> simp[] >>
                  irule expr_vv_case_nil >> simp[compile_toplevel_name_sim, int_calls_expr_def]) >>
      irule expr_vv_case_nil >> simp[compile_toplevel_name_sim, int_calls_expr_def])
  >~ [`Builtin _ _ args`]
  >- (irule ordinary_builtin_below >> simp[] >> rpt gen_tac >> strip_tac >>
      first_x_assum (irule o cj 1) >> simp[expr_size_def])
  >~ [`TypeBuiltin _ _ _ args`]
  >- (`exprs_case nc ctx fn ce cx args` by
        (irule ordinary_list_below >> simp[] >>
         qexists_tac `list_size expr_size args` >>
         conj_tac >- gvs[] >>
         simp[expr_list_member_bound]) >>
      conj_tac >- (irule expr_sim_case_of_vv >> simp[] >>
                   irule ordinary_type_builtin_dispatch >> simp[]) >>
      irule ordinary_type_builtin_dispatch >> simp[])
  >~ [`IfExp _ _ _ _`]
  >- (irule compile_ifexp_case >>
      simp[effect_free_int_calls, post_value_type_no_calls] >> gvs[] >>
      rpt strip_tac >> gvs[effect_free_int_calls])
  >~ [`Attribute _ _ _`]
  >- (irule compile_attribute_case >> gvs[])
  >~ [`Subscript _ obj idx`]
  >- (conj_tac
      >- (irule expr_sim_case_of_vv >> simp[] >>
          irule compile_subscript_case >> gvs[effect_free_int_calls]) >>
      irule compile_subscript_case >> gvs[effect_free_int_calls])
  >~ [`StructLit ann id fields`]
  >- (irule compile_struct_lit_case >> simp[] >> conj_tac
      >- (rpt strip_tac >> disj1_tac >> irule effect_free_int_calls >>
          gvs[EVERY_MEM, EXISTS_MEM, MEM_MAP] >> metis_tac[]) >>
      irule ordinary_list_below >> simp[EVERY_MAP] >>
      reverse conj_tac >- gvs[EVERY_MEM] >>
      qexists_tac `expr_size (StructLit ann id fields)` >>
      conj_tac >- gvs[expr_size_def] >>
      simp[struct_callback_child_bound])
QED

Theorem ordinary_effect_free_cases:
  !ce e nc ctx fn cx.
    acyclic_struct_metadata ce.ce_struct_fields /\ ~expr_has_effect e ==>
    expr_sim_case nc ctx fn ce cx e /\ expr_vv_case nc ctx fn ce cx e
Proof
  metis_tac[ordinary_effect_free_mutual]
QED

Theorem ordinary_effect_free_exprs:
  !ce args nc ctx fn cx.
    acyclic_struct_metadata ce.ce_struct_fields /\
    EVERY ($~ o expr_has_effect) args ==>
    exprs_case nc ctx fn ce cx args
Proof
  rpt strip_tac >> irule ordinary_exprs_lift >>
  gvs[EVERY_MEM] >> metis_tac[ordinary_effect_free_cases]
QED
