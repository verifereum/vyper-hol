(* The cases of bodySimFullMain's induction, one per evaluate_ind case
 * bodySimPtrMainAt's does not close by a short tactic, at the joint
 * judgments of bodySimFull.  A case with an existing joint producer is
 * proved here; every other case is admitted until its leaf lands, and its
 * comment names the separate source, memory and pointer cases it joins.
 *
 * TOP-LEVEL: body_expr_full_ok_leaf and the body_*_case_full cases.
 *)
Theory bodyFullCases
Ancestors bodyFullIntCall bodyFullIntCallArgs bodyFullIntCallCallee bodyIntCallSource
  bodyFullAssign bodyFullAssignTuple bodyFullAugAssign bodyFullAnnAssign
  bodyFullAppend bodyFullIfExp bodyFullAttribute
  bodyFullStmtsCons bodyFullFor bodyFullLog bodyFullRaiseReason
  bodyFullAssertReason bodyFullPreds bodyFullRawRevert bodyFullRawLog bodyFullCtrlCases
  bodyFullStructLit bodyFullPop
  bodyFullSubscript[qualified,ignore_grammar]
  bodyFullSubscriptUnframedArray[qualified,ignore_grammar]
  bodyFullTypeBuiltinEmpty bodyFullTypeBuiltinWords bodyFullTypeBuiltinConvert
  bodyFullTypeBuiltinExtract32 bodyFullTypeBuiltinAbiDecode bodyFullTypeBuiltinAbiEncode
  bodyFullRawCall bodyFullRawCallCalldata exprSimSource
  bodyFullExtCallBodyOfVV bodyFullExtCallRequestStage bodyFullExtCallReadyReturn
  bodyFullExtCallReturn abiDecodeValidJoint abiDecodeRejectJoint gasOutcomeFull
  bodyFullBuiltinWord bodyFullExprGeneric bodyFullSend bodyFullHash
  bodyFullBuiltinEnv
  bodyFullMakeArray
  bodyFullBuiltinConcat bodyFullBuiltinSlice bodyFullBuiltinCalldataSlice
  bodyFullBuiltinUint2Str
  bodyFullBuiltinECRecover bodyFullBuiltinECArithCompose
  bodyFullExprCore exprSimOperators exprLoweringProps compileEnv
  gasShadowCompile gasShadowCompileHelpers bodySimFull stmtSimZero stmtSimPass gasShadow bodySim
  exprSimHyps exprSimAggregateLayout loweringPosts bodyExprPreFacts supportedStmts
  bodyInvCodeProps bodyInvExecutionProps contractInvContextProps exprBodyPreProps
  supportedExprs supportedStmtTraverse supportedExprTraverse
  msgGasFull exprSimHypsDefs gasContext vyperTypeSystem vyperContext vyperTypeCallGraph
  vyperAST vyperInterpreter vyperState vyperValue list
  selfdestructHalt bodyFullHashKeccakFixed gasOutcomeFullCompose gasExemptOrigin
  exprOperandVar exprCallbackContracts builtinSystem emitHelper allocLimits exprLowering exprLoweringProps gasShadowState compileEnv fragExec fragGasEmitCtrl vfmSameFrame ptrSafeRun ptrDiscipline gasEvents gasCount memSafeRun instMemFrontier venomExecSemantics venomInst venomState unitTransformDefs contextCodegenRel codegenRel bodyPtrDefs rich_list
Libs
  pairLib

val _ = Parse.hide "body";

(* Join the four joint expression leaves. *)
Theorem body_expr_full_ok_leaf:
  !cx e.
    (?a id. e = Name a id) \/ (?a nsid. e = TopLevelName a nsid) \/
    (?a nsid mid. e = FlagMember a nsid mid) \/ (?a l. e = Literal a l) ==>
    body_expr_full_ok cx e
Proof
  rpt strip_tac >> gvs[] >>
  simp[name_expr_full_ok, toplevel_name_expr_full_ok,
       flag_member_expr_full_ok, literal_expr_full_ok]
QED

(* Joint annotated declaration, split by the source and destination layouts. *)
Theorem body_annassign_case_full:
  !cx id typ e.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_full_ok cx e) ==>
    body_stmt_full_ok cx (AnnAssign id typ e)
Proof
  rw[body_stmt_full_ok_def] >>
  Cases_on `is_word_type typ`
  >- (irule body_annassign_word_full >> metis_tac[]) >>
  `0 < type_memory_bytes cenv typ` by
    metis_tac[annassign_memory_bytes_pos_ptr] >>
  Cases_on `expr_type e = typ \/ lowered_value_type cenv e = typ \/
            is_bytestring_type typ \/
            has_length_word typ /\ is_empty_value_expr e`
  >- (Cases_on `(lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e))`
      >- (`lowered_value_type cenv e = typ \/ is_bytestring_type typ \/
           has_length_word typ /\ is_empty_value_expr e` by metis_tac[] >>
          irule body_annassign_memory_full >> fs[] >> metis_tac[]) >>
      irule body_annassign_widened_full >> metis_tac[]) >>
  irule body_annassign_other_full >> metis_tac[]
QED

(* The joint Append case, by its storage, local and nested leaves. *)
Theorem body_append_case_full:
  !cx t e.
    (!s'' p t'.
       eval_target_place cx t s'' = (INL p,t') ==> body_expr_full_ok cx e) /\
    body_base_target_full_ok cx t ==>
    body_stmt_full_ok cx (Append t e)
Proof
  rpt strip_tac >> Cases_on `?nid. t = TopLevelNameTarget nid`
  >- (gvs[] >> irule body_append_storage_full >> first_assum ACCEPT_TAC) >>
  Cases_on `?id. t = NameTarget id`
  >- (gvs[] >> irule body_append_local_full >> first_assum ACCEPT_TAC) >>
  irule body_append_nested_full >> simp[] >> metis_tac[]
QED

(* The joint twin of body_assert_case_ptr_at (bodyPtrExitCases): bodyFullCtrlCases. *)
Theorem body_assert_case_full:
  !cx e. body_expr_full_ok cx e ==> body_stmt_full_ok cx (Assert e AssertBare)
Proof
  ACCEPT_TAC bodyFullCtrlCasesTheory.assert_bare_stmt_full_ok
QED

(* The joint twin of body_assert_reason_case_ptr_at (bodyPtrExitCases),
   by its fragment in bodyFullAssertReason. *)
Theorem body_assert_reason_case_full:
  !cx e se.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_full_ok cx se) /\
    body_expr_full_ok cx e ==>
    body_stmt_full_ok cx (Assert e (AssertReason se))
Proof
  rpt strip_tac >> rewrite_tac[body_stmt_full_ok_def] >> rpt strip_tac >>
  irule compile_assert_reason_frag_full >> metis_tac[]
QED

(* The joint twin of body_assert_unreachable_case_ptr_at (bodyPtrExitCases): bodyFullCtrlCases. *)
Theorem body_assert_unreachable_case_full:
  !cx e.
    body_expr_full_ok cx e ==> body_stmt_full_ok cx (Assert e AssertUnreachable)
Proof
  ACCEPT_TAC bodyFullCtrlCasesTheory.assert_unreachable_stmt_full_ok
QED

(* Admitted: the joint twin of body_assign_case_ptr_at (bodyPtrAssignCases). *)
Theorem body_assign_case_full:
  !cx t e.
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
            struct_args_unique tops) /\
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
    body_expr_full_ok cx e ==>
    body_stmt_full_ok cx (Assign (BaseTarget t) e)
Proof
  rw[body_stmt_full_ok_def] >>
  `struct_args_unique tops` by
    (drule_then assume_tac body_inv_contract >>
     drule_then assume_tac contract_inv_singleton_source_modules >>
     metis_tac[]) >>
  Cases_on `?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
                    is_word_type ty`
  >- (gvs[] >> irule body_assign_local_word_full >> metis_tac[]) >>
  Cases_on `?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
                    ~is_word_type ty /\
                    (expr_type e = ty \/ lowered_value_type cenv e = ty \/
                     is_bytestring_type ty \/
                     has_length_word (expr_type e) /\ is_empty_value_expr e)`
  >- (`!id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty ==>
              0 < type_memory_bytes cenv ty` by
        (rpt strip_tac >> gvs[] >>
         metis_tac[exprSimAggregateLayoutTheory.assign_local_memory_bytes_pos]) >>
      Cases_on `(lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e))`
      >- (gvs[] >> irule body_assign_local_memory_full >> metis_tac[]) >>
      gvs[] >> irule body_assign_local_widened_full >> metis_tac[]) >>
  Cases_on `?nsid mut ty slot.
              t = TopLevelNameTarget nsid /\
              supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
              (mut = Storage \/ mut = Transient) /\
              ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
              ~is_bytestring_type ty /\
              0 < type_memory_bytes cenv ty /\ expr_type e = ty /\
              lowered_value_type cenv e = expr_type e`
  >- (gvs[] >> irule body_assign_toplevel_copy_full >> metis_tac[]) >>
  Cases_on `?nsid dty. t = TopLevelNameTarget nsid /\
                       supported_scalar_target tops nsid /\
                       type_place_target env t = SOME (Type dty) /\ is_word_type dty`
  >- (gvs[] >> irule body_assign_toplevel_word_full >> metis_tac[]) >>
  Cases_on `?id fld sid fty.
              t = AttributeTarget (NameTarget id) fld /\
              FLOOKUP env.var_types id = SOME (StructT sid) /\
              attribute_type env.type_defs (StructT sid) fld = SOME fty /\
              is_word_type fty`
  >- (gvs[] >> irule body_assign_attr_local_full >> metis_tac[]) >>
  Cases_on `?nsid fld fty.
              t = AttributeTarget (TopLevelNameTarget nsid) fld /\
              supported_storage_field_write tops nsid fld /\
              type_place_target env t = SOME (Type fty) /\ is_word_type fty`
  >- (gvs[] >> irule body_assign_attr_storage_full >> metis_tac[]) >>
  irule body_assign_other_full >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`bindings`, `env`, `env'`, `tops`] >> gvs[]
QED

(* Combine expression evaluation with assignment to a tuple target. *)
Theorem body_assign_tuple_case_full:
  !cx gs e.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget gs) v) /\ body_expr_full_ok cx e ==>
    body_stmt_full_ok cx (Assign (TupleTarget gs) e)
Proof
  rw[body_stmt_full_ok_def] >>
  drule_all body_inv_stmt_const_name_free >> strip_tac >>
  Cases_on `EXISTS (\g. ?t. g = BaseTarget t /\ immutable_root cx t /\
                    ~(?nsid. t = TopLevelNameTarget nsid)) gs`
  >- (irule body_assign_tuple_nested_immutable_full >> metis_tac[]) >>
  reverse (Cases_on `lowered_value_type cenv e = expr_type e`)
  >- (irule body_assign_tuple_widened_full >> metis_tac[]) >>
  Cases_on `?ids. gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] /\
                  EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids`
  >- (gvs[] >> drule_all assign_tuple_locals_bytes_pos >> strip_tac >>
      `EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty /\
                        0 < type_memory_bytes cenv ty) ids` by
        (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
      irule body_assign_tuple_locals_full >> metis_tac[]) >>
  Cases_on `EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                                FLOOKUP env.var_types id = SOME ty /\
                                0 < type_memory_bytes cenv ty) \/
                       (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
                               supported_scalar_target tops nsid) \/
                       (?nsid fld fty.
                          g = BaseTarget
                                (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                          supported_storage_field_write tops nsid fld /\
                          type_place_target env
                            (AttributeTarget (TopLevelNameTarget nsid) fld) =
                            SOME (Type fty) /\ is_word_type fty)) gs`
  >- (Cases_on `EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                   FLOOKUP env.var_types id = SOME ty /\
                   0 < type_memory_bytes cenv ty) \/
                (?nsid dty. g = BaseTarget (TopLevelNameTarget nsid) /\
                  supported_scalar_target tops nsid /\
                  type_place_target env (TopLevelNameTarget nsid) = SOME (Type dty) /\
                  is_word_type dty) \/
                (?nsid fld fty.
                   g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                   supported_storage_field_write tops nsid fld /\
                   type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
                     SOME (Type fty) /\ is_word_type fty)) gs`
      >- (irule body_assign_tuple_targets_word_full >> metis_tac[]) >>
      irule body_assign_tuple_other_full >> metis_tac[]) >>
  irule body_assign_tuple_other_full >> metis_tac[]
QED

(* Attribute's joint leaf is proved in bodyFullAttribute. *)
Theorem body_attribute_case_full:
  !cx v9 e id. body_expr_full_ok cx e ==> body_expr_full_ok cx (Attribute v9 e id)
Proof
  ACCEPT_TAC bodyFullAttributeTheory.attribute_expr_full_ok
QED

(* Admitted: the joint twin of body_augassign_case_ptr_at (bodyPtrAssignCases). *)
Theorem body_augassign_case_full:
  !cx ty t bop e.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\ body_base_target_full_ok cx t ==>
    body_stmt_full_ok cx (AugAssign ty t bop e)
Proof
  rw[body_stmt_full_ok_def] >>
  Cases_on `?id. t = NameTarget id`
  >- (gvs[] >> irule body_augassign_local_full >> metis_tac[]) >>
  Cases_on `?nsid. t = TopLevelNameTarget nsid /\
                   supported_scalar_target tops nsid`
  >- (gvs[] >> irule body_augassign_toplevel_word_full >> metis_tac[]) >>
  Cases_on `?id fld. t = AttributeTarget (NameTarget id) fld`
  >- (gvs[] >> irule body_augassign_attr_local_full >> metis_tac[]) >>
  Cases_on `?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                       supported_storage_field_write tops nsid fld`
  >- (gvs[] >> irule body_augassign_attr_storage_full >> metis_tac[]) >>
  irule body_augassign_other_full >> metis_tac[]
QED

(* The joint twin of body_break_case_ptr_at (bodyPtrCtrlCases): bodyFullCtrlCases. *)
Theorem body_break_case_full:
  !cx. body_stmt_full_ok cx Break
Proof
  ACCEPT_TAC bodyFullCtrlCasesTheory.break_stmt_full_ok
QED

(* Joint environment builtins, excluding Env MsgGas. *)
Theorem env_builtin_expr_full_ok:
  !cx ty bt es.
    (bt = Len \/ bt = CalldataLen \/ (?i. bt = Env i /\ i <> MsgGas) \/
     (?i. bt = Acc i) \/ bt = BlockHash \/ bt = BlobHash \/ bt = MethodId) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len ==>
       body_exprs_full_ok cx es) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_full_ok cx (HD es)) ==>
    body_expr_full_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  ONCE_REWRITE_TAC [body_expr_full_ok_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule env_builtin_sim_full >>
      gvs[type_check_def, assert_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[]
QED

(* Admitted: the joint twin of bodyPtrBopIn's bop_in_expr_ptr_ok. *)
Theorem bop_in_expr_full_ok:
  !cx ty bop es.
    (bop = In \/ bop = NotIn) /\
    (builtin_args_length_ok (Bop bop) (LENGTH es) ==> body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Builtin ty (Bop bop) es)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  ONCE_REWRITE_TAC [body_expr_full_ok_def] >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_bop_args >> strip_tac >> gvs[] >> (
  `body_exprs_full_ok cx [e1;e2]` by fs[builtin_args_length_ok_def] >>
  drule expr_body_pre_bop >> strip_tac >>
  `is_word_type (expr_type e1) /\ ty = BaseT BoolT` by
    gvs[well_typed_binop_def, membership_element_word_boundary, is_word_type_def] >>
  conj_asm1_tac
  >- (Cases_on `word_value_type (expr_type e1) /\ word_value_type (expr_type e2)`
      >- (irule bop_word_sim_full >> metis_tac[]) >>
      Cases_on `?a t n elems. e2 = Builtin a (MakeArray t n) elems`
      >- (gvs[] >> irule bop_in_literal_word_sim_full >> simp[] >>
          gvs[body_exprs_full_ok_def] >>
          metis_tac[body_make_array_children_full_ok]) >>
      irule bop_rest_word_sim_full >> simp[] >>
      metis_tac[]) >>
  match_mp_tac bodyFullExprGenericTheory.expr_vv_sim_stack_full >>
  simp[post_value_type_word, expr_type_def, is_word_type_def, compile_bop_stack] >>
  metis_tac[eval_expr_builtin_value])
QED

(* Admitted: the joint twin of bodyPtrBop's bop_expr_ptr_ok. *)
Theorem bop_expr_full_ok:
  !cx ty bop es.
    bop <> In /\ bop <> NotIn /\
    (builtin_args_length_ok (Bop bop) (LENGTH es) ==> body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Builtin ty (Bop bop) es)
Proof
  rpt gen_tac >> strip_tac >>
  ONCE_REWRITE_TAC [body_expr_full_ok_def] >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_bop_args >> strip_tac >> gvs[] >>
  `body_exprs_full_ok cx [e1;e2]` by fs[builtin_args_length_ok_def] >>
  drule expr_body_pre_bop >> strip_tac >>
  `is_word_type ty` by
    (qpat_assum `expr_body_pre _ _ _ (Builtin ty (Bop bop) [e1;e2]) _`
       (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
     simp[expr_type_def, optionTheory.IS_SOME_EXISTS] >> strip_tac >>
     Cases_on `ty`
     >~ [`is_word_type (BaseT bt)`]
       >- (Cases_on `bt`
           >~ [`is_word_type (BaseT (BytesT bd))`]
             >- (Cases_on `bd` >> Cases_on `bop` >>
                 gvs[well_typed_binop_def, is_numeric_type_def, is_int_type_def,
                     is_bool_type_def, is_flag_type_def, is_word_type_def,
                     vyperValueTheory.evaluate_type_def,
                     optionTheory.IF_EQUALS_OPTION]) >>
           Cases_on `bop` >>
           gvs[well_typed_binop_def, is_numeric_type_def, is_int_type_def,
               is_bool_type_def, is_flag_type_def, is_word_type_def]) >>
     Cases_on `bop` >>
     gvs[well_typed_binop_def, is_numeric_type_def, is_int_type_def,
         is_bool_type_def, is_flag_type_def, is_word_type_def]) >>
  conj_asm1_tac
  >- (Cases_on `(bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1)`
      >- (irule bop_bytestring_eqne_sim_full >> metis_tac[]) >>
      Cases_on `word_value_type (expr_type e1) /\ word_value_type (expr_type e2)`
      >- (irule bop_word_sim_full >> metis_tac[]) >>
      Cases_on `(bop = Eq \/ bop = NotEq) /\
                (expr_type e1 = BaseT AddressT \/
                 ?m. expr_type e1 = BaseT (BytesT (Fixed m)))`
      >- (irule bop_bytes_eq_sim_full >> metis_tac[]) >>
      irule bop_rest_word_sim_full >> simp[] >> metis_tac[]) >>
  match_mp_tac bodyFullExprGenericTheory.expr_vv_sim_stack_full >>
  simp[post_value_type_word, expr_type_def, compile_bop_stack] >>
  metis_tac[eval_expr_builtin_value]
QED

(* Joint MakeArray execution and result ownership. *)
Theorem make_array_expr_full_ok:
  !cx ty bt es.
    (?t n. bt = MakeArray t n) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Builtin ty bt es)
Proof
  rpt strip_tac >> gvs[] >>
  ONCE_REWRITE_TAC [body_expr_full_ok_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule make_array_builtin_sim_full >>
      metis_tac[]) >>
  simp[]
QED

(* Admitted: the joint twin of bodyPtrWordBuiltins's word_builtin_expr_ptr_ok. *)
Theorem word_builtin_expr_full_ok:
  !cx ty bt es.
    (bt = Not \/ bt = Neg \/ bt = Abs \/ (?d. bt = AsWeiValue d) \/ bt = Ceil \/
     bt = Floor \/ bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  ONCE_REWRITE_TAC [body_expr_full_ok_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule word_builtin_sim_full >>
      conj_tac
      >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
          irule expr_vv_sim_stack_full >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          Cases_on `is_word_type (expr_type e)` >- simp[] >>
          qpat_assum `~is_word_type (expr_type e) ==> _` drule >> simp[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`env`, `tops`] >> asm_rewrite_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[]
QED

(* The joint hash producer supplies the same singleton-argument case. *)
Theorem hash_builtin_expr_full_ok:
  !cx ty bt es.
    (bt = Keccak256 \/ bt = Sha256) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Builtin ty bt es)
Proof
  ACCEPT_TAC bodyFullHashTheory.hash_expr_full_ok
QED

(* Joint bytestring suppliers, including Slice's code-source child order. *)
Theorem bytestring_builtin_expr_full_ok:
  !cx ty bt es.
    ((?n. bt = CalldataSlice n) \/ (?n. bt = Concat n) \/ (?n. bt = Slice n) \/
     (?n. bt = Uint2Str n)) /\
    (builtin_args_length_ok bt (LENGTH es) ==>
      case code_slice_source bt es of
        NONE => body_exprs_full_ok cx es
      | SOME (code_ty,addr) =>
          body_exprs_full_ok cx (TL es) /\
          (!s tail_vs t. eval_exprs cx (TL es) s = (INL tail_vs,t) ==>
            body_exprs_full_ok cx [addr])) ==>
    body_expr_full_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  ONCE_REWRITE_TAC [body_expr_full_ok_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `(?n. bt = CalldataSlice n) \/ _` mp_tac >> strip_tac
      >- (gvs[code_slice_source_def] >>
          metis_tac[calldata_slice_expr_sim_full, calldata_slice_vv_sim_full])
      >- (gvs[code_slice_source_def] >> irule concat_sim_full >> metis_tac[])
      >- (gvs[] >> irule slice_builtin_sim_full >> metis_tac[]) >>
      gvs[code_slice_source_def] >> irule uint2str_builtin_sim_full >>
      metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[]
QED

(* Joint precompile execution, including aggregate result ownership. *)
Theorem precompile_builtin_expr_full_ok:
  !cx ty bt es.
    (bt = ECRecover \/ bt = ECAdd \/ bt = ECMul) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  ONCE_REWRITE_TAC [body_expr_full_ok_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `bt = ECRecover` >> gvs[]
      >- (irule ecrecover_builtin_sim_full >> metis_tac[]) >>
      irule ec_arith_builtin_sim_full >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[]
QED

(* msg.gas, by msgGasFull's joint fragment: typing fixes the
   annotation and the empty argument list. *)
Theorem body_msg_gas_full_case:
  !cx ann args. body_expr_full_ok cx (Builtin ann (Env MsgGas) args)
Proof
  rw[body_expr_full_ok_def] >>
  `args = [] /\ ann = env_item_type MsgGas` by
    (drule_then strip_assume_tac expr_body_pre_static_facts >>
     gvs[well_typed_expr_def, well_typed_builtin_app_def]) >>
  gvs[compile_msg_gas_sim_full]
QED

(* A builtin, split by family as body_builtin_case_ptr does. *)
Theorem body_builtin_case_full:
  !cx ty bt es.
    (!s'' x t v code_ty addr tail_s tail_vs t'.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = SOME v /\
       v = (code_ty,addr) /\
       eval_exprs cx (TL es) tail_s = (INL tail_vs,t') ==>
       body_exprs_full_ok cx [addr]) /\
    (!s'' x t v code_ty addr.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = SOME v /\
       v = (code_ty,addr) ==>
       body_exprs_full_ok cx (TL es)) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = NONE ==>
       body_exprs_full_ok cx es) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_full_ok cx (HD es)) ==>
    body_expr_full_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `bt = Env MsgGas` >- simp[body_msg_gas_full_case] >>
  reverse (Cases_on `code_slice_source bt es`)
  >- (rename1 `code_slice_source bt es = SOME src` >>
      Cases_on `src` >> gvs[code_slice_source_SOME] >>
      irule bytestring_builtin_expr_full_ok >>
      gvs[code_slice_source_def, type_check_def, assert_def,
          builtin_args_length_ok_def] >> metis_tac[]) >>
  `builtin_args_length_ok bt (LENGTH es) /\ bt <> Len ==>
   body_exprs_full_ok cx es` by
    metis_tac[type_check_def, assert_def] >>
  Cases_on `bt = Len \/ bt = CalldataLen \/ (?i. bt = Env i) \/ (?i. bt = Acc i) \/
             bt = BlockHash \/ bt = BlobHash \/ bt = MethodId`
  >- (irule env_builtin_expr_full_ok >> rpt conj_tac >> gvs[] >>
      metis_tac[]) >>
  Cases_on `?bop. bt = Bop bop`
  >- (gvs[] >> Cases_on `bop = In \/ bop = NotIn`
      >- (irule bop_in_expr_full_ok >> gvs[]) >>
      irule bop_expr_full_ok >> gvs[]) >>
  Cases_on `bt` >> gvs[] >>
  FIRST (map (fn th => irule th >> simp[] >> NO_TAC)
    [make_array_expr_full_ok, word_builtin_expr_full_ok,
     hash_builtin_expr_full_ok, bytestring_builtin_expr_full_ok,
     precompile_builtin_expr_full_ok])
QED

(* The joint twin of body_continue_case_ptr_at (bodyPtrCtrlCases): bodyFullCtrlCases. *)
Theorem body_continue_case_full:
  !cx. body_stmt_full_ok cx Continue
Proof
  ACCEPT_TAC bodyFullCtrlCasesTheory.continue_stmt_full_ok
QED


(* The joint twin of body_expr_stmt_case_ptr_at (bodyPtrCtrlCases): bodyFullCtrlCases. *)
Theorem body_expr_stmt_case_full:
  !cx e. body_expr_full_ok cx e ==> body_stmt_full_ok cx (Expr e)
Proof
  ACCEPT_TAC bodyFullCtrlCasesTheory.expr_stmt_full_ok
QED

(* Compose the counted request with its return and ABI decoder outcomes. *)
Theorem body_extcall_case_full:
  !cx v14 is_static skip_check sig opts es v15.
    (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_exprs cx (TAKE nargs (DROP 1 es)) s'3' = (INL results,t') ==>
       body_exprs_full_ok cx (DROP (1 + nargs) es)) /\
    (!s'' target t nargs.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_exprs_full_ok cx (TAKE nargs (DROP 1 es))) /\
    body_exprs_full_ok cx (TAKE 1 es) ==>
    body_expr_full_ok cx
      (Call v14 (ExtCall is_static skip_check sig opts) es v15)
Proof
  rpt gen_tac >> strip_tac >> PairCases_on `sig` >> fs[] >>
  irule extcall_body_full_ok_of_vv >> rpt gen_tac >> strip_tac >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    metis_tac[body_inv_contract, contract_inv_acyclic_struct_metadata] >>
  rewrite_tac [expr_vv_sim_full_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q R` >>
  irule gas_outcome_full_post_mono >>
  qexistsl_tac [`Q`, `\H res ee gt r.
    (expr_exit res r /\ halt_exit H cx ee res r) /\
    (ctx_has_dalloca ctx ==> !h. r = Halt h ==> allocas_below_fmp h)`] >>
  BETA_TAC >> simp[Abbr `R`] >>
  qunabbrev_tac `Q` >>
  irule (BETA_RULE (Q.SPEC
        `\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r`
        (Q.GEN `R` bodyFullIntCallReturnHaltTheory.gas_outcome_full_halt_room))) >>
      ho_match_mp_tac (GEN_ALL (SIMP_RULE bool_ss [LET_THM] extcall_request_full)) >>
      rpt (goal_assum (drule_at Any)) >>
      conj_tac
      >- qpat_assum `!st target mid src vs ee. _ ==>
           body_exprs_full_ok cx (DROP (LENGTH sig1 + 1) es)`
           (ACCEPT_TAC o ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM]) >>
      rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      mp_tac extcall_return_full >>
      (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC abi_valid_allocated_joint)) >>
      (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC abi_malformed_allocated_joint)) >>
      disch_then (fn th =>
        mp_tac extcall_ready_return_outcome >>
        (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC (SPEC_ALL th)))) >>
      disch_then ho_match_mp_tac >>
      `TAKE (LENGTH sig1) (vs ++ kws) = vs` by
        (qpat_assum `LENGTH vs = LENGTH sig1` (SUBST1_TAC o SYM) >>
         simp[TAKE_APPEND1,TAKE_LENGTH_ID]) >>
      `DROP (LENGTH sig1) (vs ++ kws) = kws` by
        (qpat_assum `LENGTH vs = LENGTH sig1` (SUBST1_TAC o SYM) >>
         simp[DROP_APPEND]) >>
      simp[LENGTH_APPEND] >>
      qhdtm_assum `extcall_request_ready` (irule_at Any) >>
      rpt (goal_assum (drule_at Any)) >>
      fs[]
QED

(* The joint twin of body_for_case_ptr_at (bodyPtrCtrlCases),
   by its fragment in bodyFullFor. *)
Theorem body_for_case_full:
  !cx id typ it n body.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_full_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_full_ok cx it) /\
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
       stmt_loop_calls_ok [(NONE,tops)] (For id typ it n body)) ==>
    body_stmt_full_ok cx (For id typ it n body)
Proof
  rpt strip_tac >> rewrite_tac[body_stmt_full_ok_def] >> rpt strip_tac >>
  `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
    (drule body_inv_contract >>
     MATCH_ACCEPT_TAC contract_inv_singleton_source_modules) >>
  irule compile_for_frag_full >> metis_tac[]
QED

(* The joint twin of body_if_case_ptr_at (bodyPtrCtrlCases): bodyFullCtrlCases. *)
Theorem body_if_case_full:
  !cx e ss1 ss2.
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_full_ok cx ss1) /\
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_full_ok cx ss2) /\ body_expr_full_ok cx e ==>
    body_stmt_full_ok cx (If e ss1 ss2)
Proof
  ACCEPT_TAC bodyFullCtrlCasesTheory.if_stmt_full_ok
QED

(* The joint twin of body_ifexp_case_ptr_at (bodyPtrExprCases): bodyFullIfExp. *)
Theorem body_ifexp_case_full:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e3) /\
    body_expr_full_ok cx e1 ==>
    body_expr_full_ok cx (IfExp v5 e1 e2 e3)
Proof
  ACCEPT_TAC bodyFullIfExpTheory.ifexp_expr_full_ok
QED

(* The frozen lifts still ask for a restricted Args rule. The concrete
   rule is stronger: its header does not exclude msg.gas defaults. *)
fun apply_case_lift lift =
  mp_tac lift >>
  (impl_tac >-
    (rpt gen_tac >> strip_tac >>
     qmatch_asmsub_rename_tac
       `supported_exprs_exists expr_msg_gas_root (DROP _ defaults)` >>
     MATCH_MP_TAC intcall_args_full >> qexists `defaults` >>
     rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  (impl_tac >- MATCH_ACCEPT_TAC intcall_callee_full) >>
  disch_then (qspecl_then [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`PG`,`func`,
                          `shadow_func`,`tops`,`cenv`,`cx`,`env`,`ty`,`v16`,
                          `fn`,`es`,`v17`,`es'`,`mut`,`nr`,`args`,`ret`,`ss`,
                          `rr`,`dflts`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC;

Definition internal_defaults_const_names_def:
  internal_defaults_const_names tops <=>
    EXISTS (\top. case top of
      FunctionDecl Internal _ _ _ _ _ dflts _ ss =>
        supported_exprs_exists (const_name_root_mods [(NONE,tops)]) dflts \/
        supported_stmts_expr_exists (const_name_root_mods [(NONE,tops)]) ss
    | _ => F) tops
End

Theorem body_intcall_case_full:
  !cx v16 src_id_opt fn es v17.
    (!ts mut nr args dflts ret ss.
       ~MEM (src_id_opt,fn) cx.stk /\
       get_module_code cx src_id_opt = SOME ts /\
       lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) ==>
       body_stmts_full_ok (cx with stk updated_by CONS (src_id_opt,fn))
         (subst_consts_stmts (module_consts_env (cx_tops cx) []) ss) /\
       body_exprs_full_ok (cx with stk updated_by CONS (src_id_opt,fn))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
           (subst_consts_exprs (module_consts_env (cx_tops cx) []) dflts))) /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') ==>
       body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Call v16 (IntCall (src_id_opt,fn)) es v17)
Proof
  rpt gen_tac >> strip_tac >>
  ONCE_REWRITE_TAC[body_expr_full_ok_def] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all body_intcall_source_selection >> strip_tac >>
  drule_then strip_assume_tac bodyInvCodePropsTheory.body_inv_main_code >>
  `~MEM (src_id_opt,fn) cx.stk ==> body_exprs_full_ok cx es` by
    (strip_tac >> drule intcall_results_full_ih >> disch_then drule_all >>
     simp[]) >>
  `~MEM (src_id_opt,fn) cx.stk ==>
     body_stmts_full_ok (cx with stk updated_by CONS (src_id_opt,fn))
       (subst_consts_stmts (module_consts_env tops []) ss) /\
     body_exprs_full_ok (cx with stk updated_by CONS (src_id_opt,fn))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
         (subst_consts_exprs (module_consts_env tops []) dflts))` by
    (strip_tac >>
     qpat_assum `!ts mut nr args dflts ret ss. _ ==> _` drule_all >>
     gvs[]) >>
  `!s1 vs t1.
     ~MEM (src_id_opt,fn) cx.stk /\ eval_exprs cx es s1 = (INL vs,t1) ==>
     body_exprs_full_ok (cx with stk updated_by CONS (src_id_opt,fn))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
         (subst_consts_exprs (module_consts_env tops []) dflts))` by metis_tac[] >>
  `!s1 vs t1 sd dvs td penv rtv.
       ~MEM (src_id_opt,fn) cx.stk /\
       eval_exprs cx es s1 = (INL vs,t1) /\
       eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
         (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
       bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME penv /\
       evaluate_type (get_tenv cx) ret = SOME rtv /\
       (nr ==> IS_SOME cx.nonreentrant_slot) /\
       (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
       body_stmts_full_ok (cx with stk updated_by CONS (src_id_opt,fn))
         (subst_consts_stmts (module_consts_env tops []) ss)` by metis_tac[] >>
  qpat_x_assum `src_id_opt = NONE` SUBST_ALL_TAC >>
  conj_tac
  >- apply_case_lift intcall_sim_full >>
  apply_case_lift intcall_vv_full
QED

(* Log, by bodyFullLog's joint fragment. *)
Theorem body_log_case_full:
  !cx id es. body_exprs_full_ok cx es ==> body_stmt_full_ok cx (Log id es)
Proof
  rw[body_stmt_full_ok_def] >>
  irule compile_log_frag_full >> metis_tac[]
QED

(* Pass, by stmtSimPass's joint fragment. *)
Theorem body_pass_case_full:
  !cx. body_stmt_full_ok cx Pass
Proof
  rw[body_stmt_full_ok_def, gas_shadow_stmt_def, compile_pass_frag_full]
QED

Theorem body_pop_case_full:
  !cx v10 bt. body_base_target_full_ok cx bt ==> body_expr_full_ok cx (Pop v10 bt)
Proof
  ACCEPT_TAC bodyFullPopTheory.pop_expr_full_ok
QED

(* The joint twin of body_raise_bare_case_ptr_at (bodyPtrExitCases): bodyFullCtrlCases. *)
Theorem body_raise_bare_case_full:
  !cx. body_stmt_full_ok cx (Raise RaiseBare)
Proof
  ACCEPT_TAC bodyFullCtrlCasesTheory.raise_bare_stmt_full_ok
QED

(* The joint twin of body_raise_reason_case_ptr_at (bodyPtrExitCases),
   by its fragment in bodyFullRaiseReason. *)
Theorem body_raise_reason_case_full:
  !cx e. body_expr_full_ok cx e ==> body_stmt_full_ok cx (Raise (RaiseReason e))
Proof
  rpt strip_tac >> rewrite_tac[body_stmt_full_ok_def] >> rpt strip_tac >>
  irule compile_raise_reason_frag_full >> metis_tac[]
QED

(* The joint twin of body_raise_unreachable_case_ptr_at (bodyPtrExitCases): bodyFullCtrlCases. *)
Theorem body_raise_unreachable_case_full:
  !cx. body_stmt_full_ok cx (Raise RaiseUnreachable)
Proof
  ACCEPT_TAC bodyFullCtrlCasesTheory.raise_unreachable_stmt_full_ok
QED

(* The joint raw_call-with-calldata case. *)
Theorem body_raw_call_calldata_case_full:
  !cx ty flags es v19.
    body_exprs_full_ok cx es ==>
    body_expr_full_ok cx (Call ty (RawCallCalldataTarget flags) es v19)
Proof
  ACCEPT_TAC bodyFullRawCallCalldataTheory.raw_call_calldata_expr_full_ok
QED

(* RawCall composes counted operands, the call and the return-data suffix. *)
Theorem body_raw_call_case_full:
  !cx ty flags es v18.
    body_exprs_full_ok cx es ==>
    body_expr_full_ok cx (Call ty (RawCallTarget flags) es v18)
Proof
  map_every qx_gen_tac [`cx`,`ann`,`flags`,`args`,`dflt`] >>
  disch_tac >> simp[Once body_expr_full_ok_def] >>
  map_every qx_gen_tac
    [`DF`,`lo`,`dframe`,`PG`,`tops`,`ctx`,`shadow_ctx`,`func`,`shadow_func`,
     `cenv`,`env`,`ty`,`es`] >> strip_tac >>
  reverse conj_asm2_tac
  >- (qpat_assum `body_exprs_full_ok cx args` (fn args_ok =>
      qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
      qpat_assum `shadow_body_inv tops ctx shadow_ctx` (fn shadow =>
      qpat_assum `body_const_cells_agree [(NONE,tops)] cx env es` (fn consts =>
      qpat_assum `expr_body_pre cenv cx env _ es` (fn pre =>
        MATCH_ACCEPT_TAC (MATCH_MP bodyFullRawCallTheory.raw_call_expr_vv_full
          (LIST_CONJ [args_ok,inv,shadow,consts,pre])))))))) >>
  irule bodyFullOfVVTheory.expr_sim_full_of_vv >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]) >>
  drule expr_body_pre_type_evaluates >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qexists `x` >> simp[] >> rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (Call ann (RawCallTarget flags) args dflt)
     (es with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
  strip_tac >> gvs[] >> metis_tac[]
QED

(* RawLog composes its topic and data children at one joint midpoint. *)
Theorem body_raw_log_case_full:
  !cx v20 es v21.
    body_exprs_full_ok cx es ==> body_expr_full_ok cx (Call v20 RawLog es v21)
Proof
  rpt strip_tac >> irule raw_log_expr_full_ok >> simp[] >> conj_tac
  >- (rpt gen_tac >>
      irule (gas_shadow_compiles_multi_exprs
             |> INST [``sh:bool`` |-> ``T``] |> REWRITE_RULE []) >>
      MATCH_ACCEPT_TAC (CONJUNCT1 gas_shadow_compile_expr)) >>
  rpt gen_tac >>
  irule (gas_shadow_compiles_lower_value
         |> INST [``sh:bool`` |-> ``T``] |> REWRITE_RULE []) >>
  MATCH_ACCEPT_TAC (CONJUNCT1 gas_shadow_compile_expr)
QED

(* RawRevert, by raw_revert_expr_full_ok; its lower_value shadow-compile
 * premise is gas_shadow_compile_expr lifted by gas_shadow_compiles_lower_value. *)
Theorem body_raw_revert_case_full:
  !cx v22 es v23.
    body_exprs_full_ok cx es ==> body_expr_full_ok cx (Call v22 RawRevert es v23)
Proof
  rpt strip_tac >>
  `!cenv ty e. gas_shadow_compiles (lower_value compile_expr cenv ty e)
     (lower_value compile_expr cenv ty (gas_shadow_expr e))`
    by (rpt gen_tac >>
        irule (gas_shadow_compiles_lower_value
               |> INST [``sh:bool`` |-> ``T``] |> REWRITE_RULE []) >>
        MATCH_ACCEPT_TAC (CONJUNCT1 gas_shadow_compile_expr)) >>
  irule raw_revert_expr_full_ok >> asm_rewrite_tac[]
QED

(* Return e, by the frame's own joint Return fragment and e's case. *)
Theorem body_return_case_full:
  !cx e. body_expr_full_ok cx e ==> body_stmt_full_ok cx (Return (SOME e))
Proof
  rw[body_stmt_full_ok_def, frame_ret_ok_full_def, gas_shadow_stmt_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  `~supported_expr_exists (const_name_root cx) e` by
    (drule_all body_inv_stmt_const_name_free >>
     simp[supported_stmt_expr_exists_def, supported_expr_exists_def]) >>
  `well_typed_expr env e` by fs[type_stmt_def] >>
  drule_all_then strip_assume_tac bodySingletonCallSupportTheory.supported_singleton_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    drule_then ACCEPT_TAC body_inv_main_support >>
  `cx_tops cx = tops` by (drule_then (ACCEPT_TAC o CONJUNCT2) body_inv_main_code) >>
  `alloc_limits_expr cenv e` by
    gvs[stmt_exprs_ok_flat, alloc_limits_stmt_def, allocLimitsTheory.alloc_limits_expr_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule (Q.SPECL [`cenv`, `cx`, `env`, `e`, `es`, `[]`]
              stmt_expr_body_pre) >>
     gvs[type_stmt_def, stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def] >>
     conj_tac
     >- (rpt strip_tac >> drule_all_then ACCEPT_TAC body_inv_singleton_abi_types) >>
     irule allocLimitsPropsTheory.alloc_limits_expr_not_extcode >>
     qexists_tac `cenv` >>
     fs[alloc_limits_stmt_def,alloc_limits_expr_def]) >>
  first_x_assum (qspecl_then [`cenv`, `env`, `lctx`, `SOME e`, `es`] mp_tac) >>
  simp[same_frame_refl] >> disch_then irule >>
  fs[body_expr_full_ok_def] >> metis_tac[]
QED

(* Return, by the frame's own joint Return fragment. *)
Theorem body_return_none_case_full:
  !cx. body_stmt_full_ok cx (Return NONE)
Proof
  rw[body_stmt_full_ok_def, frame_ret_ok_full_def, gas_shadow_stmt_def] >>
  first_x_assum (qspecl_then [`cenv`, `env`, `lctx`, `NONE`, `es`] mp_tac) >>
  simp[same_frame_refl]
QED

(* Joint composition from the source, paired layout and terminal interfaces. *)
Theorem selfdestruct_expr_full_from_interfaces:
  (!cenv cx env ann args dflt es.
    expr_body_pre cenv cx env (Call ann SelfDestructTarget args dflt) es ==>
    ?e. args = [e] /\ ann = NoneT /\ dflt = NONE /\
      expr_type e = BaseT AddressT /\
      (!es'. expr_sim_inv cenv cx env es' ==>
         expr_body_pre cenv cx env e es') /\
      eval_expr cx (Call ann SelfDestructTarget args dflt) =
        bind (bind (eval_expr cx e) (read_result cx)) (selfdestruct_tail cx)) ==>
  (!cenv ty ann e dflt sa sb vv ssa ssb svv func sfunc.
    expr_type e = BaseT AddressT /\
    gas_shadow_compiles
      (lower_value compile_expr cenv (expr_type e) e)
      (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)) /\
    gas_shadow_state sa ssa /\
    compile_expr cenv ty (Call ann SelfDestructTarget [e] dflt) sa = (vv,sb) /\
    compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Call ann SelfDestructTarget [e] dflt))
      ssa = (svv,ssb) /\
    fn_has_code sa sb func /\ fn_has_code ssa ssb sfunc ==>
    ?op sm ssm.
      vv = StackValue ann (Lit 0w) /\ svv = StackValue ann (Lit 0w) /\
      lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
      lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)
        ssa = (op,ssm) /\
      gas_shadow_state sm ssm /\
      compile_selfdestruct op sm = ((),sb) /\
      compile_selfdestruct op ssm = ((),ssb) /\
      ci_mono sa sm /\ ci_mono sm sb /\
      ci_mono ssa ssm /\ ci_mono ssm ssb /\
      fn_has_code sa sm func /\ fn_has_code sm sb func /\
      fn_has_code ssa ssm sfunc /\ fn_has_code ssm ssb sfunc) ==>
  (!op sm sb func t aw tn G ctx lo d cenv cx ee explicit PG.
    compile_selfdestruct op sm = ((),sb) /\ fn_has_code sm sb func /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t.vs_halted /\
    eval_operand op t = SOME aw /\ op_taint tn op = {} /\ op_prov G op = NONE /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
    ?r. step_inst_base (mk_inst sm.cs_next_id SELFDESTRUCT [op] []) t = r /\
        exit_result r /\
        (!D. ghost_inv_at D lo d cenv cx ee G tn t ==>
          gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
            (t,G,tn) [] (r,G,tn))) ==>
  !cx ann args dflt DF lo d PG tops ctx shadow_ctx func shadow_func
    cenv env ty es.
    body_exprs_full_ok cx args /\ body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Call ann SelfDestructTarget args dflt) es ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call ann SelfDestructTarget args dflt) es
Proof
  disch_then (mk_asm "source_contract") >>
  disch_then (mk_asm "layout_contract") >>
  disch_then (mk_asm "tail_contract") >> rpt gen_tac >> strip_tac >>
  asm "source_contract" drule >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es` by
    (first_x_assum irule >> metis_tac[expr_body_pre_static_facts]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (gvs[body_exprs_full_ok_def] >>
     qpat_x_assum `body_expr_full_ok cx e` mp_tac >>
     simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
  rewrite_tac[expr_sim_full_def] >> rpt gen_tac >> strip_tac >>
  suspend "compiler"
QED

Resume selfdestruct_expr_full_from_interfaces[compiler]:
  `!ce child ss v st.
     compile_expr ce ty (Call NoneT SelfDestructTarget [child] NONE) ss = (v,st) ==>
     v = StackValue NoneT (Lit 0w)` by
    (rpt gen_tac >> simp[Once compile_expr_def, compile_call_def, expr_type_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[])) >>
  `compile_expr cenv ty (Call NoneT SelfDestructTarget [e] NONE) sa =
       (StackValue NoneT (Lit 0w),sb) /\
   compile_expr (gas_shadow_env T cenv) ty
       (gas_shadow_expr (Call NoneT SelfDestructTarget [e] NONE))
       shadow_sa = (StackValue NoneT (Lit 0w),shadow_sb)` by
    (qpat_x_assum `lower_value _ _ _ (Call _ _ _ _) _ = _` mp_tac >>
     qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gas_shadow_expr_def] >> simp[lower_value_def, comp_bind_def] >>
     rpt (pairarg_tac >> simp[]) >>
     `vv' = StackValue NoneT (Lit 0w) /\ vv = StackValue NoneT (Lit 0w)` by
       (conj_tac >> first_x_assum irule >> metis_tac[]) >>
     gvs[unwrap_value_def, comp_return_def]) >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
     (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e))` by
    irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env >>
  asm "layout_contract" drule_all >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ e _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `ssm`, `op'`,
    `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]])) >>
  strip_tac >> suspend "compose"
QED

Resume selfdestruct_expr_full_from_interfaces[compose]:
  asm_x "source_contract" kall_tac >> asm_x "layout_contract" kall_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ fullQ fullR` >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  `!v. storage_trace_frame (bind (selfdestruct_tail cx v) (read_result cx))` by
    (gen_tac >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
     simp[vyperStorageTraceTheory.storage_trace_frame_read_result,
          selfdestructHaltTheory.storage_trace_frame_selfdestruct_tail]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gasOutcomeFullTheory.gas_outcome_full_def])
  >~ [`gas_bad_storage_at _ _ _ _ _ _`]
  >- (rewrite_tac[gasOutcomeFullTheory.gas_outcome_full_def] >>
      qexists `marks` >> disj1_tac >> reverse conj_tac >- metis_tac[] >>
      asm_rewrite_tac[] >> once_rewrite_tac[bind_assoc] >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rewrite_tac[gasOutcomeFullTheory.gas_outcome_full_def] >>
      qexists `marks` >> disj2_tac >> disj2_tac >>
      qexistsl [`err`, `ee`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
      reverse conj_tac >- metis_tac[] >>
      asm_rewrite_tac[] >> rewrite_tac[ignore_bind_def] >>
      ntac 2 (once_rewrite_tac[bind_assoc]) >>
      irule gasExemptCertTheory.gas_exempt_cert_error_value >>
      asm_rewrite_tac[ignore_bind_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  Cases_on `exit_result r`
  >- (`?ex. res = INR ex` by
        (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
           (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
         gvs[Abbr `childQ`, Abbr `childR`, Abbr `fullR`,
             fragExecTheory.exit_result_def] >>
         Cases_on `res` >> gvs[]) >>
      gvs[] >>
      rewrite_tac[gasOutcomeFullTheory.gas_outcome_full_def] >>
      qexists `marks` >> disj2_tac >> disj1_tac >>
      qexistsl [`INR ex`, `ee`, `r`, `G'`, `tn'`] >>
      conj_tac
      >- (asm_rewrite_tac[] >> once_rewrite_tac[bind_assoc] >>
          irule gasSummaryComposeTheory.gas_source_bind_exception >> simp[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[Abbr `childQ`, fragExecTheory.exit_result_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  gvs[fragExecTheory.exit_result_def] >>
  `childQ (storage_trace_horizon ee.storage_trace) res
     (ee with gas_obs := []) G' tn' t` by metis_tac[] >>
  qpat_x_assum `childQ _ _ _ _ _ _` mp_tac >>
  simp[NoAsms, Abbr `childQ`] >> strip_tac >> gvs[] >>
  `?a. dest_AddressV v = SOME a` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     fs[] >> Cases_on `dest_AddressV v` >> simp[] >>
     qpat_x_assum `gas_admissible (bind (bind (bind _ _) _) _) _ _`
       (mp_tac o REWRITE_RULE [gasContextTheory.gas_admissible_def]) >>
     disch_then (qspecl_then [`gas_explicit marks s0.vs_gas_readings`,
       `INR (Error (TypeError "selfdestruct target"))`, `ee with gas_obs := []`] mp_tac) >>
     once_rewrite_tac[bind_assoc] >> pure_once_rewrite_tac[bind_def] >>
     asm_rewrite_tac[] >>
     simp[selfdestruct_tail_def, lift_option_type_def, bind_def, raise_def,
       exprSimDefsTheory.expr_res_ok_def,
       vyperStateTheory.evaluation_state_component_equality]) >>
  `value_has_type (BaseTV AddressT) v` by
    (Cases_on `v` >> gvs[vyperValueTheory.dest_AddressV_def,
                         vyperTypingTheory.value_has_type_def]) >>
  drule exprSimSendTheory.address_typed_dest >> strip_tac >>
  gvs[] >>
  `post_value_type cenv e = BaseT AddressT` by simp[is_word_type_def] >>
  `expr_post (storage_trace_horizon ee.storage_trace) ctx func cenv cx e
     es sa sm s0 (ee with gas_obs := []) v op' t` by metis_tac[] >>
  `eval_operand op' t = SOME (typed_val_to_w256 (BaseTV AddressT) v) /\ ~t.vs_halted /\
   op_taint tn' op' = {} /\ op_prov G' op' = NONE` by
    (conj_tac
     >- (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
         simp[NoAsms, expr_post_def] >> strip_tac >>
         gvs[expr_val_rel_def, is_word_type_def,
             vyperValueTheory.evaluate_type_def]) >>
     conj_tac >- metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_projections,
                           fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted] >>
     gvs[bodyPtrDefsTheory.ptr_val_ok_def, is_word_type_def]) >>
  suspend "normal"
QED

Resume selfdestruct_expr_full_from_interfaces[normal]:
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, ee with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[APPEND_NIL] >> disch_then ACCEPT_TAC) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
      es.storage_trace` by
    (drule vyperStorageFootprintTheory.valid_horizon_frame >>
     disch_then (qspecl_then [`st0`, `ee with gas_obs := []`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
       `INL v`, `cx`, `storage_trace_horizon ee.storage_trace`] mp_tac) >>
     simp[]) >>
  `gas_value_prefix (storage_trace_horizon ee.storage_trace) T
     (ctx,func,cenv,cx) (expr_type e,e) (sa,sm,op')
     (es,s0) marks (v,ee,t)` by
    (simp[gasNormalPrefixTheory.gas_value_prefix_def] >>
     simp[gasSummaryTheory.gas_marked_exec_def,
          fragGasModeTheory.gas_marked_path_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _ /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     drule fragGasOriginPtrTheory.gas_origin_ptr_path_projections >> strip_tac >>
     drule fragGasOriginTheory.gas_origin_path_erase >>
     simp[fragGasModeTheory.gas_marked_path_def]) >>
  `t.vs_call_ctx.cc_address = cx.txn.target /\
   t.vs_call_ctx.cc_created_in_tx = cx.txn.created_in_tx /\
   t.vs_call_ctx.cc_static = cx.txn.is_static` by
    fs[expr_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def,
       loweringStateRelDefsTheory.call_ctx_rel_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     first_assum (ACCEPT_TAC o MATCH_MP
       bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  asm "tail_contract" drule_all >>
  disch_then (qspecl_then [`lo`, `d`, `cenv`, `cx`, `ee with gas_obs := []`,
    `gas_explicit_sites ctx shadow_ctx`, `PG`] strip_assume_tac) >>
  Cases_on `cx.txn.is_static` >- suspend "static" >>
  Cases_on `selfdestruct_overflows cx
      (w2w (typed_val_to_w256 (BaseTV AddressT) v)) ee.accounts`
  >- suspend "overflow" >> suspend "halt"
QED

Resume selfdestruct_expr_full_from_interfaces[static]:
  `r = Abort ExHalt_abort (halt_state (set_returndata [] t))` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operands_def]) >>
  gvs[] >> rewrite_tac[gasOutcomeFullTheory.gas_outcome_full_def] >>
  qexists `marks` >> disj2_tac >> disj1_tac >>
  qexistsl [`INR (Error (RuntimeError "write in static context"))`,
    `ee`, `Abort ExHalt_abort (halt_state (set_returndata [] t))`, `G'`, `tn'`] >>
  conj_tac
  >- (gen_tac >> once_rewrite_tac[bind_assoc] >>
      pure_once_rewrite_tac[bind_def] >> asm_rewrite_tac[] >>
      simp[selfdestruct_tail_def, bind_def, ignore_bind_def, lift_option_type_def,
        check_not_static_def, check_def, assert_def, raise_def, return_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> disch_tac >> reverse conj_tac
  >- (disj2_tac >>
      simp[fragExecTheory.exit_result_def, Abbr `childR`,
        exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _ /\ _` drule >> strip_tac >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (t,G',tn') [] (Abort ExHalt_abort (halt_state (set_returndata [] t)),G',tn')` by
    (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  qpat_assum `gas_origin_ptr_path _ _ marks (OK t,G',tn')`
    (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
  disch_then (qspec_then `t` mp_tac) >> simp[] >>
  disch_then (qspec_then `[]` mp_tac) >> simp[] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

Resume selfdestruct_expr_full_from_interfaces[overflow]:
  rewrite_tac[gasOutcomeFullTheory.gas_outcome_full_def] >>
  qexists `marks` >> disj2_tac >> disj2_tac >>
  qexistsl [`RuntimeError "transfer_value recipient overflow"`,
    `ee`, `func`, `PG`, `G'`, `tn'`, `t`] >>
  conj_tac
  >- (qpat_x_assum `eval_expr cx (Call _ _ _ _) = _` (assume_tac o SYM) >>
      asm_rewrite_tac[] >> rewrite_tac[ignore_bind_def] >>
      once_rewrite_tac[bind_assoc] >>
      irule gasExemptCertTheory.gas_exempt_cert_error_result >>
      irule gasExemptCertTheory.gas_exempt_cert_origin >>
      rewrite_tac[gasExemptOriginTheory.gas_exempt_origin_def] >> disj2_tac >>
      qexistsl [`storage_trace_horizon ee.storage_trace`, `cenv`, `cx`, `ty`,
        `NoneT`, `e`, `NONE`, `sa`, `sb`, `sm`,
        `StackValue NoneT (Lit 0w)`, `op'`, `v`,
        `w2w (typed_val_to_w256 (BaseTV AddressT) v)`] >> simp[]) >>
  qexists `storage_trace_horizon ee.storage_trace` >> simp[] >>
  irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_focus_rules) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  simp[]
QED

Resume selfdestruct_expr_full_from_interfaces[halt]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     ?u. step_inst_base (mk_inst sm.cs_next_id SELFDESTRUCT [op'] []) t = Halt u /\
         u.vs_returndata = [] /\
         halt_rel H cx
           (selfdestruct_final cx
             (w2w (typed_val_to_w256 (BaseTV AddressT) v))
             (ee with gas_obs := [])) u` by
    (rpt strip_tac >> irule step_selfdestruct_halt_rel >> simp[] >>
     irule halt_rel_from_state_rel >>
     metis_tac[expr_post_def, exprLoweringPropsTheory.stmt_state_rel_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?u. _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `step_inst_base _ t = Halt u` mp_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp t` mp_tac >>
     qpat_assum `eval_operand op' t = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operands_def] >>
     rpt (COND_CASES_TAC >> simp[LET_THM]) >>
     strip_tac >> disch_then (SUBST1_TAC o SYM) >>
     fs[allocas_below_fmp_def, halt_state_def, set_returndata_def] >> metis_tac[]) >>
  rewrite_tac[gasOutcomeFullTheory.gas_outcome_full_def] >>
  qexists `marks` >> disj2_tac >> disj1_tac >>
  qexistsl [`INR HaltException`,
    `selfdestruct_final cx (w2w (typed_val_to_w256 (BaseTV AddressT) v)) ee`,
    `Halt u`, `G'`, `tn'`] >>
  conj_tac
  >- (gen_tac >> once_rewrite_tac[bind_assoc] >>
      pure_once_rewrite_tac[bind_def] >> asm_rewrite_tac[] >>
      `selfdestruct_tail cx v (ee with gas_obs := tail) =
         (INR HaltException : eval_result + exception,
          selfdestruct_final cx (w2w (typed_val_to_w256 (BaseTV AddressT) v))
            (ee with gas_obs := tail))` by
        (irule selfdestruct_tail_halt >> simp[]) >>
      simp[bind_def, selfdestruct_final_fields]) >>
  conj_tac >- simp[selfdestruct_final_def] >>
  gen_tac >> disch_tac >>
  `valid_horizon cx st0 H ee.storage_trace` by fs[selfdestruct_final_def] >>
  reverse conj_tac
  >- (disj2_tac >>
      simp[fragExecTheory.exit_result_def, Abbr `childR`,
        exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _ /\ _` drule >> strip_tac >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (t,G',tn') [] (Halt u,G',tn')` by
    (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  qpat_assum `gas_origin_ptr_path _ _ marks (OK t,G',tn')`
    (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
  disch_then (qspec_then `t` mp_tac) >> simp[] >>
  disch_then (qspec_then `[]` mp_tac) >> simp[] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

Finalise selfdestruct_expr_full_from_interfaces

(* A single mask-independent terminal result carries the child ghosts. *)
Theorem selfdestruct_full_compiled_tail_joint:
  !op sm sb func t aw tn G ctx lo d cenv cx ee explicit PG.
    compile_selfdestruct op sm = ((),sb) /\ fn_has_code sm sb func /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t.vs_halted /\
    eval_operand op t = SOME aw /\ op_taint tn op = {} /\
    op_prov G op = NONE /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
    ?r. step_inst_base (mk_inst sm.cs_next_id SELFDESTRUCT [op] []) t = r /\
        exit_result r /\
        (!D. ghost_inv_at D lo d cenv cx ee G tn t ==>
          gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
            (t,G,tn) [] (r,G,tn))
Proof
  rpt gen_tac >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++
     [mk_inst sm.cs_next_id SELFDESTRUCT [op] []]` by
    (qpat_x_assum `compile_selfdestruct _ _ = _` mp_tac >>
     simp[compile_selfdestruct_def, emit_void_def, fresh_id_def, emit_def,
          comp_bind_def] >> strip_tac >> gvs[]) >>
  `?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
    !i. i < LENGTH [mk_inst sm.cs_next_id SELFDESTRUCT [op] []] ==>
      get_instruction bb (LENGTH sm.cs_current_insts + i) =
        SOME (EL i [mk_inst sm.cs_next_id SELFDESTRUCT [op] []])` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >> simp[]) >>
  first_x_assum (qspec_then `0` assume_tac) >> gvs[] >>
  conj_asm1_tac
  >- (simp[step_inst_base_def, mk_inst_def, eval_operands_def] >>
      Cases_on `t.vs_call_ctx.cc_static` >> simp[exit_result_def]) >>
  rpt strip_tac >>
  irule exit_inst_origin_ptr >> simp[] >>
  simp[mk_inst_def, step_inst_non_invoke, gas_events_step_def,
    gas_count_step_def, mem_safe_step_non_invoke,
    inst_mem_below_frontier_def, inst_dload_in_section_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  fs[ghost_inv_at_def, stor_taint_ok_at_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    step_inst_non_invoke, step_inst_base_def, eval_operands_def] >>
  Cases_on `t.vs_call_ctx.cc_static` >> simp[] >>
  rpt strip_tac >> gvs[halt_state_def, set_returndata_def] >>
  simp[step_taint_def, adopt_reset_def, store_taint_def,
       imm_taint_def, ret_taint_def] >>
  Cases_on `t.vs_call_ctx.cc_created_in_tx`
  >- gvs[vfmStateTheory.update_account_def, vfmStateTheory.lookup_account_def,
         combinTheory.APPLY_UPDATE_THM] >>
  gvs[GSYM vfmStateTheory.lookup_account_def,
      vfmSameFrameTheory.transfer_value_preserves_storage]
QED

(* Local source and paired compilation boundaries for the joint case. *)
Theorem selfdestruct_full_source_pre_mods[local]:
  !mods cenv cx env ann args dflt es.
    expr_body_pre_mods mods cenv cx env (Call ann SelfDestructTarget args dflt) es ==>
    ?e. args = [e] /\ ann = NoneT /\ dflt = NONE /\
      expr_type e = BaseT AddressT /\
      (!es'. expr_sim_inv_mods mods cenv cx env es' ==>
         expr_body_pre_mods mods cenv cx env e es') /\
      eval_expr cx (Call ann SelfDestructTarget args dflt) =
        bind (bind (eval_expr cx e) (read_result cx)) (selfdestruct_tail cx)
Proof
  rpt gen_tac >> strip_tac >>
  `?e. args = [e] /\ ann = NoneT /\ dflt = NONE /\
       expr_type e = BaseT AddressT` by
    gvs[expr_body_pre_mods_def, well_typed_expr_def, LENGTH_EQ_NUM_compute] >>
  gvs[eval_selfdestruct_action] >>
  rw[expr_body_pre_mods_def] >>
  gvs[expr_body_pre_mods_def, well_typed_expr_def, byte_widths_expr_def,
      alloc_limits_expr_def, int_calls_expr_def,
      expr_has_evm_run_thm, supported_expr_exists_def,
      supported_exprs_exists_every]
QED

Theorem selfdestruct_full_source_pre:
  !cenv cx env ann args dflt es.
    expr_body_pre cenv cx env (Call ann SelfDestructTarget args dflt) es ==>
    ?e. args = [e] /\ ann = NoneT /\ dflt = NONE /\
      expr_type e = BaseT AddressT /\
      (!es'. expr_sim_inv cenv cx env es' ==>
         expr_body_pre cenv cx env e es') /\
      eval_expr cx (Call ann SelfDestructTarget args dflt) =
        bind (bind (eval_expr cx e) (read_result cx)) (selfdestruct_tail cx)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_body_pre _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_body_pre_split_def]) >>
  drule_then strip_assume_tac selfdestruct_full_source_pre_mods >>
  gvs[expr_body_pre_split_def, int_calls_expr_def, supported_expr_exists_def,
      supported_exprs_exists_every] >>
  rpt strip_tac >> first_assum irule >> fs[expr_sim_inv_split_def]
QED

Theorem selfdestruct_full_layout_shadow:
  !cenv ty ann e dflt sa sb vv ssa ssb svv func sfunc.
    expr_type e = BaseT AddressT /\
    gas_shadow_compiles
      (lower_value compile_expr cenv (expr_type e) e)
      (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)) /\
    gas_shadow_state sa ssa /\
    compile_expr cenv ty (Call ann SelfDestructTarget [e] dflt) sa = (vv,sb) /\
    compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Call ann SelfDestructTarget [e] dflt))
      ssa = (svv,ssb) /\
    fn_has_code sa sb func /\ fn_has_code ssa ssb sfunc ==>
    ?data sm ssm.
      vv = StackValue ann (Lit 0w) /\ svv = StackValue ann (Lit 0w) /\
      lower_value compile_expr cenv (expr_type e) e sa = (data,sm) /\
      lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)
        ssa = (data,ssm) /\
      gas_shadow_state sm ssm /\
      compile_selfdestruct data sm = ((),sb) /\
      compile_selfdestruct data ssm = ((),ssb) /\
      ci_mono sa sm /\ ci_mono sm sb /\
      ci_mono ssa ssm /\ ci_mono ssm ssb /\
      fn_has_code sa sm func /\ fn_has_code sm sb func /\
      fn_has_code ssa ssm sfunc /\ fn_has_code ssm ssb sfunc
Proof
  rpt gen_tac >>
  simp[Once compile_expr_def, gas_shadow_expr_def] >>
  simp[Once compile_expr_def, compile_call_def, expr_type_def,
       lower_value_callback_contract, expr_child_callback_agrees] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  `lower_value
      (expr_child_callback (cenv_defaults_size cenv + expr_size e +
        (type_size ann + (option_size expr_size dflt + 2))) compile_expr)
      cenv (BaseT AddressT) e = lower_value compile_expr cenv (BaseT AddressT) e` by
    (irule lower_value_callback_contract >>
     irule expr_child_callback_agrees >> simp[]) >>
  `lower_value
      (expr_child_callback (cenv_defaults_size (gas_shadow_env T cenv) +
        expr_size (gas_shadow_expr e) + (type_size ann +
         (option_size expr_size (OPTION_MAP gas_shadow_expr dflt) + 2)))
        compile_expr) (gas_shadow_env T cenv) (BaseT AddressT) (gas_shadow_expr e) =
      lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT)
        (gas_shadow_expr e)` by
    (irule lower_value_callback_contract >>
     irule expr_child_callback_agrees >> simp[]) >>
  gvs[] >>
  qpat_x_assum `gas_shadow_compiles _ _` mp_tac >>
  simp[gas_shadow_compiles_def] >>
  disch_then drule >> simp[] >> strip_tac >> gvs[] >>
  `ci_mono sa st1` by
    (`ci_mono sa (SND (lower_value compile_expr cenv (BaseT AddressT) e sa))`
       suffices_by gvs[] >>
     irule ci_mono_lower_value_cfn >> simp[compile_expr_ci_mono]) >>
  `ci_mono ssa st1'` by
    (`ci_mono ssa (SND (lower_value compile_expr (gas_shadow_env T cenv)
                        (BaseT AddressT) (gas_shadow_expr e) ssa))` suffices_by gvs[] >>
     irule ci_mono_lower_value_cfn >> simp[compile_expr_ci_mono]) >>
  `ci_mono st1 sb /\ ci_mono st1' ssb` by
    (qpat_x_assum `compile_selfdestruct data st1 = _` mp_tac >>
     qpat_x_assum `compile_selfdestruct data st1' = _` mp_tac >>
     simp[compile_selfdestruct_def, emit_void_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, emit_def, ci_mono_def,
          cs_extends_def, IS_PREFIX_APPEND, APPEND_ASSOC] >>
     rpt strip_tac >> gvs[] >> conj_tac >> qexists_tac `[]` >> simp[]) >>
  gvs[ci_mono_def] >> metis_tac[fn_has_code_split]
QED

(* Discharge the closed interfaces using their integrated suppliers. *)
Theorem selfdestruct_expr_full:
  !cx ann args dflt DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
    body_exprs_full_ok cx args /\ body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Call ann SelfDestructTarget args dflt) es ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call ann SelfDestructTarget args dflt) es
Proof
  mp_tac selfdestruct_expr_full_from_interfaces >>
  impl_tac >- ACCEPT_TAC selfdestruct_full_source_pre >>
  impl_tac >- ACCEPT_TAC selfdestruct_full_layout_shadow >>
  impl_tac >- ACCEPT_TAC selfdestruct_full_compiled_tail_joint >>
  simp[]
QED

(* Both result judgments extend the same child joint witness. *)
Theorem body_selfdestruct_case_full:
  !cx v24 es v25.
    body_exprs_full_ok cx es ==>
    body_expr_full_ok cx (Call v24 SelfDestructTarget es v25)
Proof
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[body_expr_full_ok_def] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call v24 SelfDestructTarget es v25) es'` by
    (irule selfdestruct_expr_full >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule expr_vv_sim_stack_full >> simp[] >>
  drule selfdestruct_full_source_pre >> strip_tac >> gvs[] >>
  rpt conj_tac
  >- (gen_tac >>
      simp[Once compile_expr_def, compile_call_def, expr_type_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> simp[]))
  >- (rpt strip_tac >>
      gvs[bind_def, AllCaseEqs()] >>
      rename1 `selfdestruct_tail cx target st = (INL _,_)` >>
      qpat_x_assum `selfdestruct_tail _ _ _ = _` mp_tac >>
      qspecl_then [`cx`,`target`,`st`]
        (qx_choosel_then [`ex`,`out`] SUBST1_TAC) selfdestruct_tail_raises >>
      simp[]) >>
  simp[loweringPostsTheory.post_value_type_def, expr_type_def,
       lowered_value_type_def, vyperValueTheory.evaluate_type_def,
       valueEncodingTheory.type_memory_size_def]
QED

(* The send operands and CALL/ASSERT suffix share the joint witness. *)
Theorem body_send_case_full:
  !cx v12 has_gas es v13.
    (!s'' x t.
       type_check (LENGTH es = if has_gas then 3 else 2) "Send args" s'' =
       (INL x,t) ==>
       body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Call v12 (Send has_gas) es v13)
Proof
  ACCEPT_TAC bodyFullSendTheory.body_send_case_full
QED

(* The joint twin of body_stmts_cons_case_ptr_at (bodyPtrCtrlCases): bodyFullCtrlCases. *)
Theorem body_stmts_cons_case_full:
  !cx s ss.
    (!s'' x t. eval_stmt cx s s'' = (INL x,t) ==> body_stmts_full_ok cx ss) /\
    body_stmt_full_ok cx s ==>
    body_stmts_full_ok cx (s::ss)
Proof
  ACCEPT_TAC bodyFullCtrlCasesTheory.stmts_cons_full_ok
QED

(* The empty list, by stmtSimZero's joint fragment. *)
Theorem body_stmts_nil_case_full:
  !cx. body_stmts_full_ok cx []
Proof
  rw[body_stmts_full_ok_def, stmt_frag_nil_full]
QED

Theorem body_structlit_case_full:
  !cx v7 src_id_opt id kes.
    (!ks. ks = MAP FST kes ==> body_exprs_full_ok cx (MAP SND kes)) ==>
    body_expr_full_ok cx (StructLit v7 (src_id_opt,id) kes)
Proof
  ACCEPT_TAC bodyFullStructLitTheory.structlit_expr_full_ok
QED

(* Dispatch the joint subscript cases using the same-endpoint unframed array proof. *)
Theorem body_subscript_case_full:
  !cx v8 e1 e2.
    (!s'' res t s'3' res' t'.
       eval_expr cx e1 s'' = (INL res,t) /\
       (if subscript_reads_base cx e1 e2 then
          bind (read_result cx res) (\v. return (Value v))
        else return res) s'3' = (INL res',t') ==>
       body_expr_full_ok cx e2) /\
    body_expr_full_ok cx e1 ==>
    body_expr_full_ok cx (Subscript v8 e1 e2)
Proof
  rpt gen_tac >> strip_tac >>
  irule bodyFullSubscriptTheory.subscript_expr_full_ok_from_place_base >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  MATCH_ACCEPT_TAC bodyFullSubscriptUnframedArrayTheory.subscript_unframed_array_vv_full
QED

(* Join the TypeBuiltin constructor proofs. *)
Theorem body_type_builtin_case_full:
  !cx v11 tb typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (TypeBuiltin v11 tb typ es)
Proof
  rpt gen_tac >> Cases_on `tb`
  >- MATCH_ACCEPT_TAC bodyFullTypeBuiltinEmptyTheory.empty_expr_full_ok
  >- simp[bodyFullTypeBuiltinWordsTheory.bound_builtin_expr_full_ok]
  >- simp[bodyFullTypeBuiltinWordsTheory.bound_builtin_expr_full_ok]
  >- simp[bodyFullTypeBuiltinWordsTheory.bound_builtin_expr_full_ok]
  >- MATCH_ACCEPT_TAC bodyFullTypeBuiltinConvertTheory.convert_expr_full_ok
  >- MATCH_ACCEPT_TAC bodyFullTypeBuiltinExtract32Theory.extract32_expr_full_ok
  >- MATCH_ACCEPT_TAC bodyFullTypeBuiltinAbiDecodeTheory.abi_decode_expr_full_ok >>
  MATCH_ACCEPT_TAC bodyFullTypeBuiltinAbiEncodeTheory.abi_encode_expr_full_ok
QED
