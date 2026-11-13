Theory deployOutcomesFreeExprBody
Ancestors
  deployOutcomesFreeLowering exprLowering exprCallBounds e2eDeployDefs
  supportedExprTraverse pairToolsContext compileEnv emitHelper
  deployOutcomesFreeTyping deployOutcomesFreeSelectors vyperTypeSystem list
  deployOutcomesFreeBuiltinDispatch

Theorem outcomes_free_invalid_expr_call:
  P INVALID /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (invalid_expr_call ty s)))
Proof
  strip_tac >> simp[invalid_expr_call_def] >> pairarg_tac >> simp[] >>
  drule_all (cj 3 outcomes_free_emit_ops) >>
  disch_then (qspecl_then [`[]`, `[]`] mp_tac) >> simp[]
QED

Theorem outcomes_free_expr_child_callback:
  (!ce ty e s. expr_size e < bound /\
     ~supported_expr_exists constructor_call_root e /\
     EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e s)))) /\
  P INVALID ==>
  !ce ty e s. ~supported_expr_exists constructor_call_root e /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (expr_child_callback bound f ce ty e s)))
Proof
  rpt strip_tac >> simp[expr_child_callback_def] >>
  IF_CASES_TAC >> simp[outcomes_free_invalid_expr_call]
QED

Theorem outcomes_free_builtin_child_callback:
  (!ce rt ty bi args s. list_size expr_size args < bound /\
     ~precompile_builtin bi /\ ~supported_exprs_exists constructor_call_root args /\
     EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce rt ty bi args s)))) /\
  P INVALID ==>
  !ce rt ty bi args s.
    ~precompile_builtin bi /\ ~supported_exprs_exists constructor_call_root args /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (builtin_child_callback bound f ce rt ty bi args s)))
Proof
  rpt strip_tac >> simp[builtin_child_callback_def] >>
  IF_CASES_TAC >> simp[outcomes_free_invalid_expr_call]
QED

Theorem outcomes_free_type_child_callback:
  (!ce vt ty tb rt args s. list_size expr_size args < bound /\
     ~supported_exprs_exists constructor_call_root args /\
     EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce vt ty tb rt args s)))) /\
  P INVALID ==>
  !ce vt ty tb rt args s. ~supported_exprs_exists constructor_call_root args /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (type_child_callback bound f ce vt ty tb rt args s)))
Proof
  rpt strip_tac >> simp[type_child_callback_def] >>
  IF_CASES_TAC >> simp[outcomes_free_invalid_expr_call]
QED

(* These wrappers are parametric in the state invariant.  The join supplies
   opcode exclusion and the generator contracts proved independently. *)
Theorem outcomes_free_lower_value:
  (!s. Q s ==> Q (SND (f ce ty e s))) /\
  (!v s. Q s ==> Q (SND (unwrap_value ce v s))) /\ Q s ==>
  Q (SND (lower_value f ce ty e s))
Proof
  strip_tac >> simp[lower_value_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> metis_tac[pairTheory.SND]
QED

Theorem outcomes_free_attribute:
  (!s. Q s ==> Q (SND (f ce ty e s))) /\
  (!ops s. Q s ==> Q (SND (emit_op ADD ops s))) /\ Q s ==>
  Q (SND (compile_attribute f ce rt ty e fld s))
Proof
  strip_tac >> simp[compile_attribute_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  metis_tac[pairTheory.SND]
QED

Theorem outcomes_free_subscript:
  (!ty e s. (e = base_e \/ e = idx_e) /\ Q s ==> Q (SND (f ce ty e s))) /\
  (!v s. Q s ==> Q (SND (unwrap_value ce v s))) /\
  (!v s. Q s ==> Q (SND (compile_keccak256_key v F s))) /\
  (!b k s. Q s ==> Q (SND (compile_mapping_subscript b k s))) /\
  (!b n s. Q s ==> Q (SND (compile_tuple_subscript b n s))) /\
  (!b i d n ws sz sg loc s. Q s ==>
    Q (SND (compile_array_subscript b i d n ws sz sg
      (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc) s))) /\ Q s ==>
  Q (SND (compile_subscript f ce rt ty base_e idx_e s))
Proof
  strip_tac >>
  `!ity st. Q st ==> Q (SND (lower_value f ce ity idx_e st))`
    by (rpt strip_tac >> irule outcomes_free_lower_value >> simp[]) >>
  simp[compile_subscript_def, comp_bind_def] >>
  pairarg_tac >> simp[] >>
  rename1 `f ce ty base_e s = (vv,s1)` >>
  `Q s1` by metis_tac[pairTheory.SND] >>
  Cases_on `place_type ce base_e`
  >- (simp[comp_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >>
      Cases_on `is_bytestring_type t` >> gvs[comp_return_def] >>
      metis_tac[pairTheory.SND]) >>
  rename1 `ValPT bt` >> Cases_on `bt` >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >>
  metis_tac[pairTheory.SND]
QED

Theorem outcomes_free_typed_target_ptr:
  (!env e ce ty s. (well_typed_expr env e \/
       (?vt. type_place_expr env e = SOME vt)) /\
     ~supported_expr_exists constructor_call_root e /\ Q s ==>
     Q (SND (f ce ty e s))) /\
  (!ce v s. Q s ==> Q (SND (unwrap_value ce v s))) /\
  (!v s. Q s ==> Q (SND (compile_keccak256_key v F s))) /\
  (!b k s. Q s ==> Q (SND (compile_mapping_subscript b k s))) /\
  (!ce b i d n ws sz sg loc s. Q s ==>
    Q (SND (compile_array_subscript b i d n ws sz sg
      (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc) s))) /\
  (!ops s. Q s ==> Q (SND (emit_op ADD ops s))) ==>
  !t env vt ce s. type_place_target env t = SOME vt /\
    ~supported_target_exists constructor_call_root t /\ Q s ==>
    Q (SND (compile_get_target_ptr f ce t s))
Proof
  strip_tac >> gen_tac >>
  measureInduct_on `base_assignment_target_size t` >> Cases_on `t` >>
  rpt gen_tac >> strip_tac
  >- (simp[compile_get_target_ptr_def] >>
      Cases_on `FLOOKUP ce.ce_vars s` >> simp[comp_return_def] >>
      Cases_on `x` >> simp[comp_return_def])
  >- (simp[compile_get_target_ptr_def] >>
      Cases_on `FLOOKUP ce.ce_module_vars p` >> simp[comp_return_def] >>
      Cases_on `x` >> simp[comp_return_def])
  >- (drule_all outcomes_free_typed_subscript_target >> strip_tac >>
      `!ty st. Q st ==> Q (SND (lower_value f ce ty e st))`
        by (rpt strip_tac >> irule outcomes_free_lower_value >>
            metis_tac[]) >>
      simp[compile_get_target_ptr_def, comp_bind_def] >>
      rpt (pairarg_tac >> simp[]) >>
      `Q cs'` by (first_x_assum (qspec_then `b` mp_tac) >>
        simp[vyperASTTheory.expr_size_def] >> metis_tac[pairTheory.SND]) >>
      Cases_on `SND (SND result)`
      >- (simp[comp_bind_def] >> rpt (pairarg_tac >> simp[]) >>
          simp[comp_return_def] >> metis_tac[pairTheory.SND]) >>
      Cases_on `x` >> simp[comp_bind_def] >>
      rpt (pairarg_tac >> simp[]) >> simp[comp_return_def]
      >- (Cases_on `is_bytestring_type t` >> gvs[comp_return_def] >>
          metis_tac[pairTheory.SND]) >>
      metis_tac[pairTheory.SND])
  >> drule_all outcomes_free_typed_attribute_target >> strip_tac >>
  simp[compile_get_target_ptr_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >>
  `Q cs'` by (first_x_assum (qspec_then `b` mp_tac) >>
    simp[vyperASTTheory.expr_size_def] >> metis_tac[pairTheory.SND]) >>
  metis_tac[pairTheory.SND]
QED

(* Open expression body: recursive and generator certificates remain explicit.
   The source environment is independent of the compiler environment. *)
Theorem outcomes_free_typed_expr_body:
  (!env e ce ty s. (well_typed_expr env e \/
      (?vt. type_place_expr env e = SOME vt)) /\
    ~supported_expr_exists constructor_call_root e /\ Q s ==>
    Q (SND (f ce ty e s))) /\
  (!env ty bi args ce ct s. well_typed_expr env (Builtin ty bi args) /\
    ~supported_expr_exists constructor_call_root (Builtin ty bi args) /\ Q s ==>
    Q (SND (bc ce ty ct bi args s))) /\
  (!env ty tb rt args ce ct s. well_typed_expr env (TypeBuiltin ty tb rt args) /\
    ~supported_expr_exists constructor_call_root (TypeBuiltin ty tb rt args) /\ Q s ==>
    Q (SND (tc ce ty ct tb rt args s))) /\
  (!ty lit s. Q s ==> Q (SND (compile_literal_vv ty lit s))) /\
  (!ce ty id s. Q s ==> Q (SND (compile_name_vv ce ty id s))) /\
  (!ce v s. Q s ==> Q (SND (unwrap_value ce v s))) /\
  (!v s. Q s ==> Q (SND (compile_keccak256_key v F s))) /\
  (!b k s. Q s ==> Q (SND (compile_mapping_subscript b k s))) /\
  (!b n s. Q s ==> Q (SND (compile_tuple_subscript b n s))) /\
  (!ce b i d n ws sz sg loc s. Q s ==>
    Q (SND (compile_array_subscript b i d n ws sz sg
      (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc) s))) /\
  (!ops s. Q s ==> Q (SND (emit_op ADD ops s))) /\
  (!op ops outs s. MEM op [JNZ; ASSIGN; JMP; INVALID] /\ Q s ==>
    Q (SND (emit_inst op ops outs s))) /\
  (!s. Q s ==> Q (SND (fresh_var s))) /\
  (!lbl s. Q s ==> Q (SND (fresh_label lbl s))) /\
  (!lbl s. Q s ==> Q (SND (new_block lbl s))) /\
  (!ce ty vt v s. Q s ==> Q (SND (compile_ifexp_arm ce ty vt v s))) /\
  (!ce rt at a bt b mt m s. Q s ==>
    Q (SND (compile_addmod_names ce rt at a bt b mt m s))) /\
  (!ce rt at a bt b mt m s. Q s ==>
    Q (SND (compile_mulmod_names ce rt at a bt b mt m s))) /\
  (!ce rt at a bt b s. Q s ==>
    Q (SND (compile_powmod256_names ce rt at a bt b s))) /\
  (!n s. Q s ==> Q (SND (compile_alloc_buffer n s))) /\
  (!env fields ce ty buf off s.
    EVERY (\kv. well_typed_expr env (SND kv) /\
      ~supported_expr_exists constructor_call_root (SND kv)) fields /\ Q s ==>
    Q (SND (compile_struct_lit f ce ty fields buf off s))) /\
  (!env t vt ce s. type_place_target env t = SOME vt /\
    ~supported_target_exists constructor_call_root t /\ Q s ==>
    Q (SND (compile_get_target_ptr f ce t s))) /\
  (!ptr ws sz ctor imm loc s. Q s ==>
    Q (SND (compile_dynarray_pop ptr ws sz ctor imm loc s))) ==>
  !env e ce ty s. (well_typed_expr env e \/
      (?vt. type_place_expr env e = SOME vt)) /\
    ~supported_expr_exists constructor_call_root e /\ Q s ==>
    Q (SND (compile_expr_body f bc tc ce ty e s))
Proof
  strip_tac >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >> Cases_on `e`
  >~ [`Literal t l`] >- (simp[compile_expr_body_def] >> metis_tac[])
  >~ [`Name t id`] >- (simp[compile_expr_body_def] >> metis_tac[])
  >~ [`IfExp t a b c`] >- suspend "ifexp"
  >~ [`Builtin t bi args`] >- suspend "builtin"
  >~ [`TypeBuiltin t tb rt args`] >- suspend "typebuiltin"
  >~ [`Subscript t b i`] >- suspend "subscript"
  >~ [`Attribute t b fld`] >- suspend "attribute"
  >~ [`StructLit t n fields`] >- suspend "struct"
  >~ [`FlagMember t n m`] >- simp[compile_expr_body_def]
  >~ [`TopLevelName t n`] >- suspend "topname"
  >~ [`Call t tg args dr`] >-
    gvs[supported_expr_exists_def, constructor_call_root_def]
  >> suspend "pop"
QED

Resume outcomes_free_typed_expr_body[ifexp]:
  gvs[well_typed_expr_def, supported_expr_exists_def] >>
  `!ty st. Q st ==> Q (SND (lower_value f ce ty a st))` by
    (rpt strip_tac >> irule outcomes_free_lower_value >> metis_tac[]) >>
  simp[compile_expr_body_def] >> rpt (pairarg_tac >> simp[]) >>
  IF_CASES_TAC >> simp[] >> metis_tac[pairTheory.SND]
QED
Resume outcomes_free_typed_expr_body[builtin]:
  `well_typed_expr env (Builtin t bi args)` by
    gvs[well_typed_expr_def] >>
  irule outcomes_free_builtin_dispatch >> simp[] >> metis_tac[]
QED
Resume outcomes_free_typed_expr_body[typebuiltin]:
  gvs[well_typed_expr_def] >>
  simp[compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  first_x_assum irule >> simp[] >> qexists_tac `env` >> simp[]
QED
Resume outcomes_free_typed_expr_body[subscript]:
  drule_all outcomes_free_typed_subscript_children >> strip_tac >>
  simp[compile_expr_body_def] >> irule outcomes_free_subscript >>
  metis_tac[]
QED
Resume outcomes_free_typed_expr_body[attribute]:
  drule_all outcomes_free_typed_attribute_child >> strip_tac >>
  simp[compile_expr_body_def] >> irule outcomes_free_attribute >>
  metis_tac[]
QED
Resume outcomes_free_typed_expr_body[struct]:
  `EVERY (\kv. well_typed_expr env (SND kv) /\
      ~supported_expr_exists constructor_call_root (SND kv)) fields` by
    (gvs[well_typed_expr_def, supported_expr_exists_def,
         outcomes_free_typed_fields_every, EVERY_MEM,
         supported_fields_exists_every, EXISTS_MEM] >>
     metis_tac[]) >>
  simp[compile_expr_body_def] >> rpt (pairarg_tac >> simp[]) >>
  metis_tac[pairTheory.SND]
QED
Resume outcomes_free_typed_expr_body[topname]:
  simp[compile_expr_body_def] >>
  Cases_on `FLOOKUP ce.ce_module_vars n` >> simp[]
  >- (pairarg_tac >> simp[] >> metis_tac[pairTheory.SND, MEM]) >>
  Cases_on `x` >> simp[] >> pairarg_tac >> simp[] >>
  metis_tac[pairTheory.SND, MEM]
QED
Resume outcomes_free_typed_expr_body[pop]:
  drule_all outcomes_free_typed_pop_target >> strip_tac >>
  simp[compile_expr_body_def] >> rpt (pairarg_tac >> simp[]) >>
  metis_tac[pairTheory.SND]
QED
Finalise outcomes_free_typed_expr_body
