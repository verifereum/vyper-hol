(*
 * The body simulation of S1: expression cases (#636, #638)
 *
 * One lemma for each expression case of evaluate_ind that bodySimMain's
 * body_sim_mutual does not close in a line or two.  An expression with
 * no internal call simulates by compile_expr_sim (body_expr_ok_intro);
 * each case's GAP is the expression with one, and the internal call
 * itself is the call step (#638, body_intcall_case).
 *
 * A case proved here instantiates the shared case lemma of exprSim*
 * (exprSimHyps' expr_sim_case and expr_vv_case) that compile_expr_sim
 * uses too, at nocalls = F, from the operands' body_expr_ok
 * (body_expr_ok_case).
 *
 * TOP-LEVEL:
 *   body_expr_ok_intro — an expression with no internal call simulates by
 *                        compile_expr_sim
 *   body_expr_ok_case, body_expr_ok_of_case — body_expr_ok is the shared
 *                        judgments at nocalls = F in every frame
 *   body_exprs_ok_case — body_exprs_ok is exprs_case at nocalls = F
 *   body_*_case        — one case of the induction each; the call cases
 *                        are in bodySimCallCases
 *)

Theory bodySimExprCases
Ancestors
  bodySimIfExpWidened bodySimStructLitWidened bodySimMakeArrayWidened
  bodySimBopInLiteralWord bodySimBopHeld
  bodySimConvertWidened
  exprSimSource
  exprSimHypsDefs
  list bodySim  exprSimHyps exprSimOperators exprSimAttribute
  exprSimPlaces exprSimMapDefs exprSimSubscriptMap exprSimPopNested bodyPopNestedTargetFrag exprSimPopImmutableTarget targetPlaceSim exprSimAggregates exprSimSend exprSimMain exprSimECArith vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph

(* An expression naming a mapping is a top-level name or a subscript
   (expr_map_case_other); a top-level one has no internal call
   (compile_toplevel_map_case).  So only a subscript's mapping half needs
   its own proof (body_subscript_case). *)
Theorem body_expr_ok_map_other:
  !cx e tops ctx func cenv.
    (!ty e1 e2. e <> Subscript ty e1 e2) ==>
    expr_map_case F ctx func cenv cx e
Proof
  rpt strip_tac >> Cases_on `?ty id. e = TopLevelName ty id`
  >- gvs[compile_toplevel_map_case] >>
  irule expr_map_case_other >> gvs[]
QED

(* With no internal call in it, an expression simulates by
   compile_expr_sim; what is left is the case with one. *)
Theorem body_expr_ok_intro:
  !cx e.
    (!ty e1 e2. e <> Subscript ty e1 e2) /\
    (!tops ctx func cenv env ty es.
       body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
       int_calls_expr e <> [] ==>
       expr_sim ctx func cenv cx ty e es /\
       expr_vv_sim ctx func cenv cx ty e es) ==>
    body_expr_ok cx e
Proof
  (* rw splits the simulation clause into its expr_sim and expr_vv_sim
     goals, so the mapping goal is picked by its conclusion *)
  rw[body_expr_ok_def]
  >~ [`expr_map_sim _ _ _ _ _ _ _`]
  >- (drule body_expr_ok_map_other >>
      simp[expr_map_case_def] >> metis_tac[]) >>
  Cases_on `int_calls_expr e = []` >> gvs[] >>
  metis_tac[compile_expr_sim, compile_expr_vv_sim, expr_sim_pre_body]
QED

Theorem body_expr_ok_case:
  !cx e tops ctx func cenv.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx ==>
    expr_sim_case F ctx func cenv cx e /\ expr_vv_case F ctx func cenv cx e
Proof
  rw[body_expr_ok_def, expr_sim_case_def, expr_vv_case_def] >> metis_tac[]
QED

Theorem body_expr_ok_of_case:
  !cx e.
    (!ty e1 e2. e <> Subscript ty e1 e2) /\
    (!tops ctx func cenv.
       body_inv tops ctx cenv cx ==>
       expr_sim_case F ctx func cenv cx e /\
       expr_vv_case F ctx func cenv cx e) ==>
    body_expr_ok cx e
Proof
  rw[body_expr_ok_def]
  >~ [`expr_map_sim _ _ _ _ _ _ _`]
  >- (drule body_expr_ok_map_other >>
      simp[expr_map_case_def] >> metis_tac[]) >>
  fs[expr_sim_case_def, expr_vv_case_def] >> metis_tac[]
QED

Theorem body_exprs_ok_case:
  !cx es tops ctx func cenv.
    body_exprs_ok cx es /\ body_inv tops ctx cenv cx ==>
    exprs_case F ctx func cenv cx es
Proof
  gen_tac >> Induct >> rw[body_exprs_ok_def, exprs_case_def] >>
  metis_tac[body_expr_ok_case]
QED

(* exprSimOperators' compile_ifexp_case. *)
Theorem body_ifexp_case:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_ok cx e3) /\
    body_expr_ok cx e1 ==>
    body_expr_ok cx (IfExp v5 e1 e2 e3)
Proof
  rpt strip_tac >> irule body_expr_ok_of_case >> conj_tac >~ [`_ <> Subscript _ _ _`] >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `!e. (e = e2 \/ e = e3) ==>
    int_calls_expr e = [] \/ same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)`
  >- (irule compile_ifexp_case >> simp[] >> metis_tac[body_expr_ok_case]) >>
  rw[expr_sim_case_def, expr_vv_case_def] >>
  metis_tac[body_ifexp_widened_call_arm]
QED

(* exprSimAggregates' compile_struct_lit_case. *)
Theorem body_structlit_case:
  !cx v7 src_id_opt id kes.
    (!ks. ks = MAP FST kes ==> body_exprs_ok cx (MAP SND kes)) ==>
    body_expr_ok cx (StructLit v7 (src_id_opt,id) kes)
Proof
  rpt strip_tac >> irule body_expr_ok_of_case >> conj_tac >~ [`_ <> Subscript _ _ _`] >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `!e. MEM e (MAP SND kes) ==>
              int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e`
  >- (irule compile_struct_lit_case >> metis_tac[body_exprs_ok_case]) >>
  rw[expr_sim_case_def, expr_vv_case_def] >>
  metis_tac[body_struct_lit_widened_call_elem]
QED

(* exprSimPlaces' compile_subscript_case, whose array and mapping cases are
   cheated there for compile_expr_sim too. *)
Theorem body_subscript_case:
  !cx v8 e1 e2.
    (!s'' res t. eval_expr cx e1 s'' = (INL res,t) ==> body_expr_ok cx e2) /\
    body_expr_ok cx e1 ==>
    body_expr_ok cx (Subscript v8 e1 e2)
Proof
  rpt strip_tac >> simp[Once body_expr_ok_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `expr_vv_case F ctx func cenv cx (Subscript v8 e1 e2)` by
        (irule exprSimPlacesTheory.compile_subscript_case >> rpt conj_tac
         >- metis_tac[body_expr_ok_case]
         >- metis_tac[body_expr_ok_map_case] >>
         rpt strip_tac >> metis_tac[body_expr_ok_case]) >>
      drule expr_sim_case_of_vv >>
      fs[expr_sim_case_def, expr_vv_case_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `expr_map_case F ctx func cenv cx (Subscript v8 e1 e2)` by
    (irule compile_subscript_map_map_case >> rpt conj_tac >> rpt strip_tac >>
     metis_tac[body_expr_ok_case, body_expr_ok_map_case]) >>
  fs[expr_map_case_def] >> metis_tac[]
QED

(* exprSimAttribute's compile_attribute_case. *)
Theorem body_attribute_case:
  !cx v9 e id. body_expr_ok cx e ==> body_expr_ok cx (Attribute v9 e id)
Proof
  rpt strip_tac >> irule body_expr_ok_of_case >> conj_tac >~ [`_ <> Subscript _ _ _`] >- simp[] >> rpt gen_tac >>
  strip_tac >> irule compile_attribute_case >> metis_tac[body_expr_ok_case]
QED

(* A binary operator: exprSimOperators' compile_bop_case, whose
   == and != on bytestrings and in and not in on arrays go through
   compile_bop_rest_case there for compile_expr_sim too.  It leaves out in and
   not in on an array literal (body_bop_in_literal_case). *)
Theorem body_bop_case:
  !cx ty bop e1 e2.
    ((bop = In \/ bop = NotIn) ==>
     !a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
    body_exprs_ok cx [e1; e2] ==> body_expr_ok cx (Builtin ty (Bop bop) [e1; e2])
Proof
  rw[body_exprs_ok_def] >> irule body_expr_ok_of_case >> conj_tac >~ [`_ <> Subscript _ _ _`] >- simp[] >> rpt gen_tac >>
  strip_tac >> irule compile_bop_case >> rpt conj_tac
  >- (strip_tac >> metis_tac[body_expr_ok_case]) >>
  metis_tac[body_expr_ok_case]
QED

(* A builtin's operands are as many as builtin_args_length_ok allows. *)
Theorem well_typed_builtin_app_length[local]:
  !ty bt ts.
    well_typed_builtin_app ty bt ts ==> builtin_args_length_ok bt (LENGTH ts)
Proof
  Cases_on `bt` >>
  rw[vyperTypeSystemTheory.well_typed_builtin_app_def, builtin_args_length_ok_def]
  >~ [`well_typed_builtin_app _ (MakeArray o' _) _`]
  >- (Cases_on `o'` >> gvs[vyperTypeSystemTheory.well_typed_builtin_app_def]) >>
  gvs[]
QED

(* Array literals: exprSimAggregates' compile_make_array_case, from the
   elements' body_exprs_ok; a count the bound does not admit fails to type
   check. *)
Theorem body_make_array_case:
  !cx ty t n es.
    (builtin_args_length_ok (MakeArray t n) (LENGTH es) ==>
     body_exprs_ok cx es) ==>
    body_expr_ok cx (Builtin ty (MakeArray t n) es)
Proof
  rpt strip_tac >> irule body_expr_ok_of_case >> conj_tac >~ [`_ <> Subscript _ _ _`] >- simp[] >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `builtin_args_length_ok (MakeArray t n) (LENGTH es)`)
  >- (rw[expr_sim_case_def, expr_vv_case_def] >>
      gvs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def] >>
      drule well_typed_builtin_app_length >> simp[]) >>
  Cases_on `!e. MEM e es ==>
              int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e`
  >- (irule compile_make_array_case >> metis_tac[body_exprs_ok_case]) >>
  rw[expr_sim_case_def, expr_vv_case_def] >>
  metis_tac[body_make_array_widened_call_elem]
QED

(* ecadd and ecmul: exprSimECArith's compile_ecadd_call_case and
   compile_ecmul_call_case, from the operands' body_expr_ok.
   Restating the case lemmas of the cases marked GAP (#636) over
   exprSimHyps' shared judgments is not enough for all of them: some take
   more than the judgments of the operands the induction hypotheses give
   (a subscript's place chain, a pop's target, the calls). *)
Theorem body_builtin_residual_case:
  !cx ty bt es.
    (bt = ECAdd \/ bt = ECMul) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_ok cx es) ==>
    body_expr_ok cx (Builtin ty bt es)
Proof
  rpt strip_tac >> (irule body_expr_ok_of_case >> conj_tac >~ [`_ <> Subscript _ _ _`] >- simp[] >> rpt gen_tac >> strip_tac >>
  `expr_vv_case F ctx func cenv cx (Builtin ty bt es)`
    suffices_by metis_tac[expr_sim_case_of_vv] >>
  reverse (Cases_on `builtin_args_length_ok bt (LENGTH es)`)
  >- (rw[expr_vv_case_def] >>
      gvs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def] >>
      drule well_typed_builtin_app_length >> simp[]) >>
  `exprs_case F ctx func cenv cx es` by metis_tac[body_exprs_ok_case] >>
  gvs[compile_ecadd_call_case, compile_ecmul_call_case])
QED

(* The builtins other than the binary operators: exprSimMain's
   compile_builtin_case, from the operands' body_expr_ok (a len's one
   operand's), but for body_make_array_case's and
   body_builtin_residual_case's. *)
Theorem body_builtin_rest_case:
  !cx ty bt es.
    (!bop. bt <> Bop bop) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas ==>
       body_exprs_ok cx es) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_ok cx (HD es)) ==>
    body_expr_ok cx (Builtin ty bt es)
Proof
  rpt strip_tac >> Cases_on `?t n. bt = MakeArray t n`
  >- (gvs[] >> irule body_make_array_case >> strip_tac >>
      first_x_assum irule >> gvs[type_check_def, assert_def]) >>
  Cases_on `bt = ECAdd \/ bt = ECMul`
  >- (irule body_builtin_residual_case >> simp[] >> strip_tac >>
      first_x_assum irule >> gvs[type_check_def, assert_def]) >>
  irule body_expr_ok_of_case >> conj_tac >~ [`_ <> Subscript _ _ _`] >- simp[] >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `builtin_args_length_ok bt (LENGTH es)`)
  >- (rw[expr_sim_case_def, expr_vv_case_def] >>
      gvs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def] >>
      drule well_typed_builtin_app_length >> simp[]) >>
  `exprs_case F ctx func cenv cx es` by
    (Cases_on `bt = Len`
     >- (gvs[builtin_args_length_ok_def, listTheory.LENGTH_EQ_NUM_compute] >>
         `body_expr_ok cx h` by
           (first_x_assum irule >> simp[type_check_def, assert_def]) >>
         simp[exprs_case_def] >> metis_tac[body_expr_ok_case]) >>
     `body_exprs_ok cx es` by
       (Cases_on `bt = Env MsgGas`
        >- gvs[builtin_args_length_ok_def, body_exprs_ok_def] >>
        first_x_assum irule >> simp[type_check_def, assert_def]) >>
     metis_tac[body_exprs_ok_case]) >>
  irule compile_builtin_case >> gvs[]
QED

(* In and not in on an array literal: of words by bodySimBopInLiteralWord,
   from the elements' judgments (bodySimBopHeld's
   body_make_array_children_ok, held for the bodySim child-closure wave);
   of non-words held for #742 (bodySimBopHeld). *)
Theorem body_bop_in_literal_case:
  !cx ty bop e1 a t n elems.
    (bop = In \/ bop = NotIn) /\
    body_exprs_ok cx [e1; Builtin a (MakeArray t n) elems] ==>
    body_expr_ok cx
      (Builtin ty (Bop bop) [e1; Builtin a (MakeArray t n) elems])
Proof
  rpt gen_tac >> Cases_on `is_word_type (expr_type e1)`
  >- (rw[body_exprs_ok_def] >> irule body_bop_in_literal_word_case >>
      rw[] >> irule body_make_array_children_ok >> metis_tac[]) >>
  MATCH_MP_TAC body_bop_in_literal_nonword_case >> first_assum ACCEPT_TAC
QED

Theorem body_builtin_case:
  !cx ty bt es.
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas ==>
       body_exprs_ok cx es) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_ok cx (HD es)) ==>
    body_expr_ok cx (Builtin ty bt es)
Proof
  rpt strip_tac >> reverse (Cases_on `?bop. bt = Bop bop`)
  >- (irule body_builtin_rest_case >> gvs[] >> metis_tac[]) >>
  gvs[] >> Cases_on `?e1 e2. es = [e1; e2]`
  >- (gvs[] >>
      `body_exprs_ok cx [e1; e2]` by
        (first_x_assum irule >>
         simp[type_check_def, assert_def, builtin_args_length_ok_def]) >>
      Cases_on `(bop = In \/ bop = NotIn) /\
                ?a t n elems. e2 = Builtin a (MakeArray t n) elems`
      >- (gvs[] >> irule body_bop_in_literal_case >> simp[]) >>
      irule body_bop_case >> gvs[]) >>
  irule body_expr_ok_of_case >> conj_tac >~ [`_ <> Subscript _ _ _`] >- simp[] >> rpt gen_tac >> strip_tac >>
  irule compile_bop_args_case >> gvs[]
QED

(* pop on a nested target: exprSimPopNested's pop_nested_sim, by the
   target's root, with the target's fragment judgment from
   body_pop_nested_target_frag. *)
Theorem body_pop_nested_case:
  !cx v10 bt.
    (!id. bt <> NameTarget id) /\ (!nid. bt <> TopLevelNameTarget nid) /\
    body_base_target_ok cx bt ==>
    body_expr_ok cx (Pop v10 bt)
Proof
  rpt strip_tac >> irule body_expr_ok_of_case >> conj_tac >~ [`_ <> Subscript _ _ _`] >- simp[] >> rpt gen_tac >> strip_tac >>
  `expr_vv_case F ctx func cenv cx (Pop v10 bt)` by
    (rw[expr_vv_case_def] >>
     irule pop_nested_sim >> conj_tac
     >- (strip_tac >> qexists_tac `F` >> simp[] >>
         irule body_target_idx_case >> metis_tac[]) >>
     qexists_tac `env` >> simp[] >> rpt conj_tac
     >~ [`cenv.ce_is_ctor`]
     >- (strip_tac >> gvs[] >> conj_tac >- gvs[body_inv_def] >>
         `cenv.ce_module = NONE` by gvs[body_inv_def, cenv_module_pins_def] >>
         rpt strip_tac >> irule body_imm_var_type >>
         gvs[expr_body_pre_def] >> metis_tac[]) >>
     strip_tac >> irule body_pop_nested_target_frag >> metis_tac[]) >>
  simp[expr_sim_case_of_vv]
QED

(* pop on a local: exprSimPlaces' compile_pop_name_case; on a module
   variable or immutable, which makes no internal call, compile_expr_sim;
   the rest by body_pop_nested_case. *)
Theorem body_pop_case:
  !cx v10 bt. body_base_target_ok cx bt ==> body_expr_ok cx (Pop v10 bt)
Proof
  rpt strip_tac >> Cases_on `?id. bt = NameTarget id`
  >- (gvs[] >> irule body_expr_ok_of_case >> simp[compile_pop_name_case]) >>
  Cases_on `?nid. bt = TopLevelNameTarget nid`
  >- (gvs[] >> irule body_expr_ok_intro >> conj_tac
      >~ [`_ <> Subscript _ _ _`] >- simp[] >>
      simp[vyperTypeCallGraphTheory.int_calls_expr_def]) >>
  irule body_pop_nested_case >> gvs[]
QED

(* The type builtins: exprSimMain's compile_type_builtin_case. *)
Theorem body_type_builtin_case:
  !cx v11 tb typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_ok cx es) ==>
    body_expr_ok cx (TypeBuiltin v11 tb typ es)
Proof
  rpt strip_tac >> irule body_expr_ok_of_case >> conj_tac >~ [`_ <> Subscript _ _ _`] >- simp[] >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `type_builtin_args_length_ok tb (LENGTH es)`)
  >- (rw[expr_sim_case_def, expr_vv_case_def] >>
      gvs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def] >>
      drule vyperTypeBuiltinsTheory.well_typed_type_builtin_args_length >>
      simp[]) >>
  `body_exprs_ok cx es` by
    (first_x_assum irule >> simp[type_check_def, assert_def]) >>
  Cases_on `tb = Convert /\
            ?e1 a f cargs d. es = [e1] /\ e1 = Call a (IntCall f) cargs d /\
                             lowered_value_type cenv e1 <> expr_type e1`
  >- (gvs[] >> rw[expr_sim_case_def, expr_vv_case_def] >>
      metis_tac[body_convert_widened_call_arg]) >>
  irule compile_type_builtin_case >> metis_tac[body_exprs_ok_case]
QED

(* exprSimSend's compile_send_case; the operands' body_exprs_ok holds when
   their count type checks, which well_typed_expr gives. *)
Theorem body_send_case:
  !cx v12 has_gas es v13.
    (!s'' x t.
       type_check (LENGTH es = if has_gas then 3 else 2) "Send args" s'' =
       (INL x,t) ==>
       body_exprs_ok cx es) ==>
    body_expr_ok cx (Call v12 (Send has_gas) es v13)
Proof
  rpt strip_tac >> irule body_expr_ok_of_case >> conj_tac >~ [`_ <> Subscript _ _ _`] >- simp[] >> rpt gen_tac >> strip_tac >>
  `expr_vv_case F ctx func cenv cx (Call v12 (Send has_gas) es v13)`
    suffices_by simp[expr_sim_case_of_vv] >>
  rw[expr_vv_case_def] >> drule send_pre_types >> strip_tac >>
  `body_exprs_ok cx es` by
    (first_x_assum irule >> simp[type_check_def, assert_def]) >>
  `expr_vv_case F ctx func cenv cx (Call v12 (Send has_gas) es v13)` by
    metis_tac[compile_send_case, body_exprs_ok_case] >>
  fs[expr_vv_case_def] >> metis_tac[]
QED
