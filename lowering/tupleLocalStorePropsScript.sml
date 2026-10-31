(*
 * Source writes of a tuple into locals and the code of the stores, shared
 * by the word-only and the memory-backed tuple assignment.
 *
 * TOP-LEVEL:
 *   assign_tuple_target_local, assign_tuple_target_list_local_cons,
 *     assign_tuple_target_list_length — the source writes
 *   lookup_scopes_write_local_type — a write keeps every name's type
 *   tuple_store_local_step, tuple_store_locals_grows,
 *     tuple_store_locals_extends — the code of the stores
 *)
Theory tupleLocalStoreProps
Ancestors
  list rich_list finite_map pred_set stmtSimAssignStore stmtSimDeclMem
  stmtLowering emitHelperProps exprLoweringProps vyperInterpreter vyperLookup
  vyperState vyperValue compileEnv emitHelper fragExec

Theorem assign_tuple_target_local:
  !cx id v es res es'.
    assign_tuple_targets cx (BaseTarget (NameTarget id)) v es = (res, es') /\
    (!m. res <> INR (Error (TypeError m))) ==>
    ?pre env entry rest abi.
      find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
      res = INL () /\
      es' = es with <|scopes :=
              pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) ::
              rest; abi_memory := abi|>
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, return_def, raise_def] >>
  Cases_on `lookup_scopes id es.scopes` >>
  simp[raise_def, return_def, get_place_def] >>
  rpt strip_tac >> drule write_place_local >> simp[] >> metis_tac[]
QED

Theorem assign_tuple_target_list_length:
  !gs cx vs es es'.
    assign_tuple_target_list cx gs vs es = (INL (), es') ==>
    LENGTH gs = LENGTH vs
Proof
  Induct >> Cases_on `vs` >>
  simp[Once evaluate_def, return_def, raise_def] >>
  rpt gen_tac >> simp[ignore_bind_def, bind_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem lookup_scopes_write_local_type:
  !id sc pre env entry rest v n e'.
    find_containing_scope id sc = SOME (pre, env, entry, rest) /\
    lookup_scopes n
      (pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) =
      SOME e' ==>
    ?e. lookup_scopes n sc = SOME e /\ e.type = e'.type
Proof
  rpt strip_tac >>
  drule find_containing_scope_lookup >> strip_tac >>
  drule find_containing_scope_structure >> strip_tac >>
  Cases_on `n = id`
  >- (drule find_containing_scope_pre_none >> strip_tac >>
      drule_then (qspecl_then [`env`, `entry with <|value := v; popped := []|>`,
                               `rest`] mp_tac) lookup_scopes_update >>
      strip_tac >> gvs[] >> qexists_tac `entry` >>
      REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> ASM_REWRITE_TAC []) >>
  qexists_tac `e'` >>
  `lookup_scopes n (pre ++ env::rest) = SOME e'` by
    metis_tac[lookup_scopes_update_other] >>
  ASM_REWRITE_TAC []
QED

Theorem tuple_store_local_step:
  !cenv ty tys id ids op ops st st' p sz vt.
    compile_tuple_store_all cenv (ty::tys)
      (BaseTarget (NameTarget id) :: MAP (BaseTarget o NameTarget) ids)
      (op::ops) st = ((), st') /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vt /\
    (is_word_type vt = is_word_type ty) ==>
    ?sm. (if is_word_type ty then emit_void MSTORE [Var p; op]
          else compile_store_memory cenv op (Var p) vt ty) st = ((), sm) /\
         compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids)
           ops sm = ((), st')
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_get_target_ptr_local >> strip_tac >>
  qpat_x_assum `compile_tuple_store_all _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss())
    [compile_tuple_store_all_def, compile_store_at_loc_def,
     compile_assign_value_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, LET_THM, combinTheory.o_THM] >>
  Cases_on `is_word_type ty` >> simp[] >>
  pairarg_tac >> simp[]
QED

Theorem tuple_store_locals_grows:
  !ids tys ops cenv st st'.
    compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids) ops
      st = ((), st') /\
    (!i. i < LENGTH ids /\ i < LENGTH tys ==>
       ?p sz vt. FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) sz) /\
         cenv.ce_var_type (EL i ids) = SOME vt /\
         (is_word_type vt = is_word_type (EL i tys)) /\
         (~is_word_type vt ==> vt = EL i tys \/ is_bytestring_type vt)) ==>
    cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var
Proof
  Induct
  >- (rpt gen_tac >> Cases_on `tys` >> Cases_on `ops` >>
      simp[compile_tuple_store_all_def, comp_return_def, cs_extends_refl]) >>
  rpt gen_tac >> Cases_on `tys`
  >- simp[compile_tuple_store_all_def, comp_return_def, cs_extends_refl] >>
  Cases_on `ops`
  >- simp[compile_tuple_store_all_def, comp_return_def, cs_extends_refl] >>
  rename1 `compile_tuple_store_all cenv (ty::tys1) _ (op::ops1) st = _` >>
  strip_tac >>
  qpat_assum `!i. i < LENGTH (_::_) /\ _ ==> _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >> strip_tac >>
  fs[MAP, combinTheory.o_THM] >>
  drule_all tuple_store_local_step >> strip_tac >>
  `cs_extends st sm /\ st.cs_next_var <= sm.cs_next_var` by
    (Cases_on `is_word_type ty` >> gvs[]
     >- metis_tac[ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
     metis_tac[ci_mono_compile_store_memory, ci_mono_def, pairTheory.SND]) >>
  `!i. i < LENGTH ids /\ i < LENGTH tys1 ==>
       ?p sz vt. FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) sz) /\
         cenv.ce_var_type (EL i ids) = SOME vt /\
         (is_word_type vt = is_word_type (EL i tys1)) /\
         (~is_word_type vt ==> vt = EL i tys1 \/ is_bytestring_type vt)` by
    (rpt strip_tac >>
     qpat_x_assum `!i. i < SUC _ /\ _ ==> _`
       (qspec_then `SUC i` mp_tac) >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem tuple_store_locals_extends:
  !ids tys ops cenv st st'.
    compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids) ops
      st = ((), st') /\
    (!i. i < LENGTH ids /\ i < LENGTH tys ==>
       ?p sz vt. FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) sz) /\
         cenv.ce_var_type (EL i ids) = SOME vt /\
         (is_word_type vt = is_word_type (EL i tys)) /\
         (~is_word_type vt ==> vt = EL i tys \/ is_bytestring_type vt)) ==>
    cs_extends st st'
Proof
  metis_tac[tuple_store_locals_grows]
QED

Theorem assign_tuple_target_list_local_cons:
  !cx id ids v vs es es'.
    assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) (id::ids))
      (v::vs) es = (INL (), es') ==>
    ?pre env entry rest es1 abi.
      find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
      es1 = es with <|scopes :=
        pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest;
        abi_memory := abi|> /\
      assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) ids) vs es1 =
        (INL (), es')
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, combinTheory.o_THM, ignore_bind_def, bind_def] >>
  Cases_on `assign_tuple_targets cx (BaseTarget (NameTarget id)) v es` >>
  rename1 `_ = (r1, es1)` >> Cases_on `r1` >> simp[] >> strip_tac >>
  drule assign_tuple_target_local >> simp[] >> strip_tac >>
  gvs[] >> metis_tac[]
QED
