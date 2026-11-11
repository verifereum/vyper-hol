(*
 * The pointer twin of bodySimMain's induction: the cases for declarations and assignments.
 * Each is the pointer twin of the S1 case of the same name (bodySim*Cases),
 * over bodyPtrPreds's predicates; bodySimPtrMain's body_sim_ptr_mutual
 * uses them.
 *
 * TOP-LEVEL:
 *   body_annassign_case_ptr
 *   body_assign_case_ptr
 *   body_assign_tuple_case_ptr
 *   body_augassign_case_ptr
 *)
Theory bodyPtrAssignCases
Ancestors
  assignBasePtrWordBody assignBasePtrLocalBody assignBasePtrLocalBodyFacts
  assignBasePtrTopWordBody assignBasePtrStorageBody
  assignBasePtrAttrLocal assignBasePtrAttrStorage
  annAssignPtrDispatch annAssignPtrWord annAssignPtrFacts
  assignTuplePtrBodyLocals assignTuplePtrBodyTargets
  bodyPtrAssignResidual bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST vyperInterpreter
  supportedStmts exprLoweringProps compileEnv loweringStateRelDefs vyperTypeEnv
  stmtSimDefs
  vyperState vyperContext vyperTypeCallGraph list
  augAssignPtrLocalBody augAssignPtrToplevelBody augAssignPtrFieldBody
  augAssignPtrStorageFieldBody

val _ = Parse.hide "body";

(* ADMITTED: a piece of the body induction. *)
Theorem body_annassign_case_ptr:
  !cx id typ e.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ptr_ok cx e) ==>
    body_stmt_ptr_ok cx (AnnAssign id typ e)
Proof
  rw[body_stmt_ptr_ok_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  Cases_on `is_word_type typ`
  >- (irule body_annassign_word_ptr >> metis_tac[]) >>
  `0 < type_memory_bytes cenv typ` by
    metis_tac[annassign_memory_bytes_pos_ptr] >>
  Cases_on `lowered_value_type cenv e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type cenv e) /\
    arg_type_fits (lowered_value_type cenv e) (expr_type e)`
  >- (`supported_copy_types typ (expr_type e)` by
        gvs[supported_stmt_def] >>
      `lowered_value_type cenv e = typ \/ is_bytestring_type typ \/
       has_length_word typ /\ is_empty_value_expr e` by
        metis_tac[copy_types_not_word_bytestring_ptr] >>
      irule body_annassign_memory_ptr >> metis_tac[]) >>
  irule body_annassign_widened_aggregate_call_ptr >> metis_tac[]
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_assign_case_ptr:
  !cx t e.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_ptr_ok cx t) /\
    body_expr_ptr_ok cx e ==>
    body_stmt_ptr_ok cx (Assign (BaseTarget t) e)
Proof
  rw[body_stmt_ptr_ok_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def, supported_assignment_def] >>
  Cases_on `?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\ is_word_type ty`
  >- (gvs[] >> irule body_assign_local_word_ptr >> metis_tac[]) >>
  Cases_on `?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
    ~is_word_type ty /\ (expr_type e = ty \/ lowered_value_type cenv e = ty \/
      is_bytestring_type ty \/ has_length_word (expr_type e) /\ is_empty_value_expr e)`
  >- (`!id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty ==>
          0 < type_memory_bytes cenv ty` by
        (rpt strip_tac >> gvs[] >> metis_tac[assign_base_local_memory_bytes_pos]) >>
      Cases_on `lowered_value_type cenv e = expr_type e \/
        is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type cenv e) /\
        arg_type_fits (lowered_value_type cenv e) (expr_type e)`
      >- (gvs[] >> irule body_assign_local_memory_ptr >> metis_tac[]) >>
      gvs[] >> irule body_assign_widened_aggregate_call_ptr >> metis_tac[]) >>
  Cases_on `?nsid. t = TopLevelNameTarget nsid /\ supported_scalar_target tops nsid`
  >- (gvs[] >> rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      irule body_assign_toplevel_word_ptr >> metis_tac[]) >>
  Cases_on `?nsid mut ty slot. t = TopLevelNameTarget nsid /\
    supported_variable_decl tops nsid = SOME (Private,mut,ty,SOME slot) /\
    (mut = Storage \/ mut = Transient) /\ ~is_word_type ty /\
    (!elem n. ty <> ArrayT elem (Dynamic n)) /\ 0 < type_memory_bytes cenv ty /\ expr_type e = ty`
  >- (gvs[] >> irule body_assign_toplevel_copy_ptr >> metis_tac[]) >>
  Cases_on `?id fld sid fty. t = AttributeTarget (NameTarget id) fld /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    attribute_type env.type_defs (StructT sid) fld = SOME fty /\ is_word_type fty`
  >- (gvs[] >> irule body_assign_attr_local_ptr >> metis_tac[]) >>
  Cases_on `?nsid fld fty. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
    supported_storage_field_write tops nsid fld /\
    type_place_target env t = SOME (Type fty) /\ is_word_type fty`
  >- (gvs[] >> rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      irule body_assign_attr_storage_ptr >> metis_tac[]) >>
  irule body_assign_other_ptr >> simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`bindings`, `env`, `env'`, `tops`] >> fs[] >> metis_tac[]
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_assign_tuple_case_ptr:
  !cx gs e.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_ptr_ok cx (TupleTarget gs) v) /\ body_expr_ptr_ok cx e ==>
    body_stmt_ptr_ok cx (Assign (TupleTarget gs) e)
Proof
  rw[body_stmt_ptr_ok_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def, supported_assignment_def] >>
  reverse (Cases_on `lowered_value_type cenv e = expr_type e`)
  >- (irule body_assign_tuple_widened_call_ptr >> metis_tac[]) >>
  Cases_on `?ids. gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] /\
                  EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids`
  >- (gvs[] >> drule_all tuple_locals_bytes_pos_ptr >> strip_tac >>
      `EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty /\
                        0 < type_memory_bytes cenv ty) ids` by
        (fs[EVERY_MEM] >> metis_tac[]) >>
      irule body_assign_tuple_locals_ptr >> metis_tac[]) >>
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
  >- (simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
      `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
        fs[stmt_state_rel_def, state_rel_def] >>
      drule_all body_assign_tuple_targets_ptr >>
      simp[stmt_frag_ptr_def] >> disch_then drule_all >> simp[]) >>
  irule body_assign_tuple_other_ptr >> metis_tac[]
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_augassign_case_ptr:
  !cx ty t bop e.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ptr_ok cx e) /\ body_base_target_ptr_ok cx t ==>
    body_stmt_ptr_ok cx (AugAssign ty t bop e)
Proof
  rw[body_stmt_ptr_ok_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  Cases_on `?id. t = NameTarget id`
  >- (gvs[] >> irule body_augassign_local_ptr >> metis_tac[]) >>
  Cases_on `?nsid. t = TopLevelNameTarget nsid /\ supported_scalar_target tops nsid`
  >- (gvs[] >> rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      irule body_augassign_toplevel_word_ptr >> metis_tac[]) >>
  Cases_on `?id fld. t = AttributeTarget (NameTarget id) fld`
  >- (gvs[] >> irule body_augassign_attr_local_ptr >> metis_tac[]) >>
  Cases_on `?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                       supported_storage_field_write tops nsid fld`
  >- (gvs[] >> rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      irule body_augassign_attr_storage_ptr >> metis_tac[]) >>
  irule body_augassign_other_ptr >> metis_tac[]
QED
