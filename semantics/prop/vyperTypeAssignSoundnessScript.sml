(*
 * Fresh assignment-target soundness helpers for the executable type system.
 *)

Theory vyperTypeAssignSoundness
Ancestors
  list rich_list finite_map option pair arithmetic
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping vyperLookup
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperTypeEnv vyperTypeExprSoundness vyperTypeStatePreservation
  vyperTypeBuiltins vyperExprNoControl
Libs
  wordsLib markerLib

(* ===== Error-shape lemmas ===== *)

Theorem lift_sum_error:
  lift_sum x y = (INR e, s) ==> (?m. e = Error m)
Proof
  rw[lift_sum_def, CaseEq"sum", sum_CASE_rator, return_def, raise_def]
QED

Theorem lift_option_type_error:
  lift_option_type x z y = (INR e, s) ==> e = Error (TypeError z)
Proof
  rw[lift_option_type_def, CaseEq"option", option_CASE_rator, return_def, raise_def]
QED


Theorem get_immutables_error:
  get_immutables x y z = (INR e, s) ==> ?m. e = Error m
Proof
  rw[get_immutables_def, bind_apply, AllCaseEqs(), return_def,
     get_address_immutables_def] >>
  drule lift_option_type_error >> rw[]
QED

Theorem set_storage_backend_no_error[simp]:
  set_storage_backend a b c st <> (INR e, f)
Proof
  Cases_on `b` >> rw[set_storage_backend_def] >>
  gvs[update_transient_def, return_def] >>
  gvs[bind_apply, AllCaseEqs(), get_accounts_def, return_def] >>
  gvs[update_accounts_def, return_def]
QED

Theorem write_storage_slot_error:
  write_storage_slot a b c d e f = (INR g, h) ==> ?m. g = Error m
Proof
  rw[write_storage_slot_def, bind_apply, AllCaseEqs(), lift_option_def,
     return_def, raise_def] >> gvs[]
  >- (Cases_on `encode_value d e` >> gvs[return_def, raise_def]) >>
  Cases_on `b` >> gvs[get_storage_backend_def, get_accounts_def,
    get_transient_storage_def, bind_def, return_def]
QED

Theorem lookup_global_error:
  lookup_global a b c d = (INR e, f) ==> (?m. e = Error m)
Proof
  rw[lookup_global_def, bind_apply, AllCaseEqs(), option_CASE_rator,
     lift_option_type_def, raise_def, return_def] >>
  gvs[var_decl_info_CASE_rator, prod_CASE_rator, AllCaseEqs(),
      bind_apply, lift_option_type_def, raise_def, return_def]
  >- (drule get_immutables_error >> rw[]) >>
  gvs[option_CASE_rator, AllCaseEqs(), raise_def, return_def]
QED

Theorem set_global_error:
  set_global a b c d e = (INR x, y) ==> ?t. x = Error t
Proof
  rw[set_global_def, bind_apply, AllCaseEqs()] >>
  gvs[lift_option_type_def, option_CASE_rator, AllCaseEqs(), raise_def,
      return_def, bind_apply, var_decl_info_CASE_rator, prod_CASE_rator] >>
  drule write_storage_slot_error >> rw[]
QED


Theorem get_scopes_result:
  !st r st'. get_scopes st = (r, st') ==> r = INL st.scopes /\ st' = st
Proof
  simp[get_scopes_def, return_def]
QED


Theorem get_module_code_NONE_lookup_global_TypeError:
  get_module_code cx src = NONE ==>
  lookup_global cx src n st = (INR (Error (TypeError "lookup_global get_module_code")), st)
Proof
  rw[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def]
QED


Theorem lookup_global_INL_imp_decl_facts:
  !cx src n st tv r.
    lookup_global cx src n st = (INL tv, r) ==>
    ?code. get_module_code cx src = SOME code
Proof
  rpt gen_tac >> strip_tac >>
  CCONTR_TAC >> fs[] >>
  Cases_on `get_module_code cx src` >> gvs[] >>
  drule get_module_code_NONE_lookup_global_TypeError >> strip_tac >>
  gvs[]
QED



Theorem lookup_global_INL_StorageVarDecl_imp_IS_SOME:
  !cx src n st code is_transient typ id_str tv r.
    get_module_code cx src = SOME code /\
    lookup_global cx src n st = (INL tv, r) /\
    find_var_decl_by_name n code = SOME (StorageVarDecl is_transient typ, id_str) ==>
    IS_SOME (evaluate_type (get_tenv cx) typ) /\
    IS_SOME (lookup_var_slot_from_layout cx is_transient src id_str)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def, LET_THM, return_def, raise_def] >>
  Cases_on `lookup_var_slot_from_layout cx is_transient src id_str` >> gvs[return_def, raise_def] >>
  Cases_on `evaluate_type (get_tenv cx) typ` >> gvs[return_def, raise_def]
QED

(* If lookup_global returns INL and find_var_decl is SOME(HashMapVarDecl ...),
   then lookup_var_slot_from_layout must return SOME.
   This follows from lookup_global_def: it calls lift_option_type on
   lookup_var_slot_from_layout before returning HashMapRef. *)
Theorem lookup_global_INL_HashMapVarDecl_imp_IS_SOME:
  !cx src n st code is_transient kt vt id_str tv r.
    get_module_code cx src = SOME code /\
    lookup_global cx src n st = (INL tv, r) /\
    find_var_decl_by_name n code = SOME (HashMapVarDecl is_transient kt vt, id_str) ==>
    IS_SOME (lookup_var_slot_from_layout cx is_transient src id_str)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def, LET_THM, return_def, raise_def] >>
  Cases_on `lookup_var_slot_from_layout cx is_transient src id_str` >> gvs[return_def, raise_def]
QED
