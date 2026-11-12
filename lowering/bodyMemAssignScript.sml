(* Memory case of the body induction (bodyMemory's body_mem_mutual):
   assignment to a base target.  The same split as S1's body_assign_case,
   each subcase in its own bodyMemAssign* leaf. *)
Theory bodyMemAssign
Ancestors
  bodyMemoryPreds
  bodyMemAssignLocalWord bodyMemAssignLocalMem bodyMemAssignWidened
  bodyMemAssignTopWord bodyMemAssignTopCopy bodyMemAssignAttrLocal
  bodyMemAssignAttrStorage bodyMemAssignOther

Theorem body_assign_mem_case:
  !cx t e.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_mem_ok cx t) /\
    body_expr_mem_ok cx e ==>
    body_stmt_mem_ok cx (Assign (BaseTarget t) e)
Proof
  rpt gen_tac >> strip_tac >> PURE_REWRITE_TAC [body_stmt_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
                    is_word_type ty`
  >- (pop_assum (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS)) >>
      qpat_x_assum `t = _` SUBST_ALL_TAC >>
      drule_all body_assign_local_word_mem >> simp[]) >>
  Cases_on `?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
                    ~is_word_type ty /\
                    (expr_type e = ty \/ lowered_value_type cenv e = ty \/
                     is_bytestring_type ty \/
                     has_length_word (expr_type e) /\ is_empty_value_expr e)`
  >- (pop_assum (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS)) >>
      qpat_x_assum `t = _` SUBST_ALL_TAC >>
      Cases_on `lowered_value_type cenv e = expr_type e \/
                is_bytestring_type (expr_type e) /\
                is_bytestring_type (lowered_value_type cenv e) /\
                arg_type_fits (lowered_value_type cenv e) (expr_type e)`
      >- (drule_all body_assign_local_memory_mem >> simp[]) >>
      drule_all body_assign_widened_aggregate_call_mem >> simp[]) >>
  Cases_on `?nsid. t = TopLevelNameTarget nsid /\
                   supported_scalar_target tops nsid`
  >- (pop_assum (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS)) >>
      qpat_x_assum `t = _` SUBST_ALL_TAC >>
      drule_all body_assign_toplevel_word_mem >> simp[]) >>
  Cases_on `?nsid mut ty slot.
              t = TopLevelNameTarget nsid /\
              supported_variable_decl tops nsid =
                SOME (Private, mut, ty, SOME slot) /\
              (mut = Storage \/ mut = Transient) /\
              ~is_word_type ty /\ ~is_abi_dynamic cenv.ce_struct_fields ty /\
              (!elem n. ty <> ArrayT elem (Dynamic n)) /\
              0 < type_memory_bytes cenv ty /\ expr_type e = ty`
  >- (pop_assum (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS)) >>
      qpat_x_assum `t = _` SUBST_ALL_TAC >>
      drule_all body_assign_toplevel_copy_mem >> simp[]) >>
  Cases_on `?id fld sid fty.
              t = AttributeTarget (NameTarget id) fld /\
              FLOOKUP env.var_types id = SOME (StructT sid) /\
              attribute_type env.type_defs (StructT sid) fld = SOME fty /\
              is_word_type fty`
  >- (pop_assum (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS)) >>
      qpat_x_assum `t = _` SUBST_ALL_TAC >>
      drule_all body_assign_attr_local_mem >> simp[]) >>
  Cases_on `?nsid fld fty.
              t = AttributeTarget (TopLevelNameTarget nsid) fld /\
              supported_storage_field_write tops nsid fld /\
              type_place_target env t = SOME (Type fty) /\ is_word_type fty`
  >- (pop_assum (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS)) >>
      qpat_x_assum `t = _` SUBST_ALL_TAC >>
      drule_all body_assign_attr_storage_mem >> simp[]) >>
  drule_all body_assign_other_mem >> simp[]
QED
