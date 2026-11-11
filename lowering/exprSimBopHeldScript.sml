(* Membership on non-word operands is rejected by the source type checker.
   Bytestring equality is proved separately in exprSimBopBytestring. *)

Theory exprSimBopHeld
Ancestors
  exprSimBopBytestring
  exprSimUnopCompose
  exprSimBopTyped
  exprSimUnopProps
  exprSimSource
  exprSimHypsDefs
  exprSimDefs
  allocLimits
  list finite_map
  fragExec  exprSimHyps exprSimOps exprSimBinopFrag
  exprSimUnop exprSimCompare
  exprBopLowering exprWordOperand
  loweringSlice
  exprLowering compileEnv
  vyperAST vyperInterpreter vyperState vyperContext vyperTypeSystem
  vyperTypeCallGraph
  vyperTyping vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness
  vyperStatePreservation



Theorem compile_bop_nonword_membership_case:
  !nocalls ctx func cenv cx ann bop e1 e2.
    (bop = In \/ bop = NotIn) /\ ~is_word_type (expr_type e1) ==>
    expr_sim_case nocalls ctx func cenv cx e1 /\
    expr_vv_case nocalls ctx func cenv cx e1 /\
    ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv, t) /\
                       read_result cx tv s1 = (INL v, t1)) ==>
     expr_sim_case nocalls ctx func cenv cx e2 /\
     expr_vv_case nocalls ctx func cenv cx e2) /\
    ~(word_value_type (expr_type e1) /\ word_value_type (expr_type e2)) /\
    ~((bop = Eq \/ bop = NotEq) /\
      (expr_type e1 = BaseT AddressT \/
       ?m. expr_type e1 = BaseT (BytesT (Fixed m)))) /\
    ((bop = In \/ bop = NotIn) ==>
     !a t n elems. e2 <> Builtin a (MakeArray t n) elems) ==>
    expr_sim_case nocalls ctx func cenv cx (Builtin ann (Bop bop) [e1; e2])
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[expr_sim_case_def, expr_body_pre_def] >>
  rpt strip_tac >>
  qpat_x_assum `well_typed_expr _ (Builtin _ _ _)` mp_tac >>
  simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
  strip_tac >>
  gvs[well_typed_binop_def, GSYM membership_element_word_boundary,
      is_prim_word_type_def]
QED

Theorem compile_bop_in_literal_nonword_sim:
  !cenv ann bop e1 a t n elems.
    ~is_word_type (expr_type e1) ==>
    expr_sim_below cenv
      (list_size expr_size [e1; Builtin a (MakeArray t n) elems]) /\
    (bop = In \/ bop = NotIn) ==>
    expr_ok cenv (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems])
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[expr_ok_def, expr_sim_ok_def, expr_vv_ok_def, expr_sim_pre_def] >>
  rpt strip_tac >>
  qpat_x_assum `well_typed_expr _ (Builtin _ _ _)` mp_tac >>
  simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
  strip_tac >>
  gvs[well_typed_binop_def, GSYM membership_element_word_boundary,
      is_prim_word_type_def]
QED
