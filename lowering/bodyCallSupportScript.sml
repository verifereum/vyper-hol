Theory bodyCallSupport
Ancestors
  supportedProgram supportedDecls supportedTypes vyperContext vyperTypeContract
  vyperTypeCallGraph vyperTypeContractStaticMaps vyperInterpreter vyperAST
  alist finite_map list pair

(* Allocation is a property of the linked unit. State declarations in
   uses-only modules may have no slot. The main module retains the
   allocated-header check through supported_program. *)
Definition supported_module_declaration_header_def:
  supported_module_declaration_header tops top <=>
    case top of
      VariableDecl vis Storage name ty slot => supported_storage_type tops ty
    | VariableDecl vis Transient name ty slot => supported_storage_type tops ty
    | HashMapDecl vis transient name kt vt slot =>
        supported_hashmap_key_type kt /\ supported_hashmap_value tops vt
    | _ => supported_declaration_header tops top
End

Definition supported_module_headers_def:
  supported_module_headers tops <=>
    EVERY (supported_module_declaration_header tops) tops /\
    supported_declaration_names tops /\
    ALL_DISTINCT (supported_internal_function_names tops) /\
    EVERY (supported_pure_expr tops o SND) (module_consts_env tops [])
End

Theorem supported_program_module_headers:
  supported_program tops ==> supported_module_headers tops
Proof
  simp[supported_program_def, supported_module_headers_def,
       supported_declaration_headers_def, EVERY_MEM] >>
  rpt strip_tac >> res_tac >>
  Cases_on `e` >>
  gvs[supported_module_declaration_header_def, supported_declaration_header_def,
      AllCaseEqs()] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* The interpreter can synthesize an empty constructor on lookup failure.
   The compiler emits imported constructors from declarations. *)
Definition supported_linked_callee_def:
  supported_linked_callee in_deploy tops (src, name) <=>
    IS_SOME (supported_function_decl tops (NONE,name) Internal) \/
    (in_deploy /\ src <> NONE /\
     IS_SOME (supported_function_decl tops (NONE,name) Deploy))
End

Theorem supported_function_decl_exists:
  !tops. MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops ==>
    IS_SOME (supported_function_decl tops (NONE,name) vis)
Proof
  Induct >> simp[supported_function_decl_def] >>
  Cases >> simp[supported_function_decl_def] >>
  rw[] >> gvs[]
QED

Definition source_body_call_supported_def:
  source_body_call_supported cx call <=>
    ?tops. get_module_code cx (FST call) = SOME tops /\
           supported_module_headers tops /\
           supported_linked_callee cx.in_deploy tops call /\
           (if FST call = NONE then supported_program tops
            else
              ?vis mut nr raw args dflts ret ss.
                include_fn_sig cx.in_deploy vis /\
                MEM (FunctionDecl vis mut nr raw (SND call) args dflts ret ss) tops /\
                lookup_callable_function cx.in_deploy (SND call) tops =
                  SOME (mut,nr,args,dflts,ret,ss) /\
                supported_declaration_body tops
                  (FunctionDecl vis mut nr raw (SND call) args dflts ret ss) /\
                (cx.in_deploy ==> supported_deploy_declaration tops
                  (FunctionDecl vis mut nr raw (SND call) args dflts ret ss)))
End

(* The checked artifact contains a declaration for each signature. In
   particular an empty deploy fallback from the interpreter is no signature. *)
Definition linked_fn_sigs_declared_def:
  linked_fn_sigs_declared mods cx fn_sigs <=>
    (!tops. mods <> [(NONE,tops)]) ==>
    !src name sig. FLOOKUP fn_sigs (src,name) = SOME sig ==>
      ?tops vis mut nr raw args dflts ss.
        ALOOKUP mods src = SOME tops /\
        include_fn_sig cx.in_deploy vis /\
        MEM (FunctionDecl vis mut nr raw name args dflts sig.ret_ty ss) tops /\
        lookup_callable_function cx.in_deploy name tops =
          SOME (mut,nr,args,dflts,sig.ret_ty,ss)
End

Theorem linked_fn_sigs_declared_singleton[simp]:
  linked_fn_sigs_declared [(NONE,tops)] cx fn_sigs
Proof
  simp[linked_fn_sigs_declared_def]
QED

Theorem linked_fn_sigs_declared_stk[simp]:
  (linked_fn_sigs_declared mods (cx with stk := stk) fn_sigs <=>
   linked_fn_sigs_declared mods cx fn_sigs) /\
  (linked_fn_sigs_declared mods (cx with stk updated_by f) fn_sigs <=>
   linked_fn_sigs_declared mods cx fn_sigs)
Proof
  simp[linked_fn_sigs_declared_def]
QED

Theorem check_contract_linked_fn_sigs_declared:
  check_contract cx.in_deploy layouts addr mods = SOME art ==>
  linked_fn_sigs_declared mods cx art.cta_fn_sigs
Proof
  rw[check_contract_def, linked_fn_sigs_declared_def] >>
  gvs[live_artifact_def, FLOOKUP_DRESTRICT_SOME] >>
  drule_all build_contract_type_artifact_fn_sigs_declared_sound >>
  metis_tac[]
QED

(* The linked gate covers occurrences in the bodies and defaults the
   checker examines. The singleton body proofs recover main-module
   resolution from typing and the unqualified support rules. *)
Definition linked_body_calls_resolved_def:
  linked_body_calls_resolved mods cx <=>
    (!tops. mods <> [(NONE,tops)]) ==>
    !src tops vis mut nr raw name args dflts ret ss.
      ALOOKUP mods src = SOME tops /\
      MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops /\
      context_function_live cx (src,name) /\
      check_function_body_in_mode cx.in_deploy vis ==>
      EVERY (\call. ?target_tops.
        ALOOKUP mods (FST call) = SOME target_tops /\
        supported_linked_callee cx.in_deploy target_tops call)
        (function_int_calls dflts ss)
End

Theorem linked_body_calls_resolved_singleton[simp]:
  linked_body_calls_resolved [(NONE,tops)] cx
Proof
  simp[linked_body_calls_resolved_def]
QED

Theorem source_body_calls_main:
  EVERY (\c. FST c = NONE) calls /\
  EVERY (source_body_call_supported cx) calls <=>
  EVERY (\c. FST c = NONE /\
             ?tops. supported_program tops /\
                    get_module_code cx NONE = SOME tops /\
                    IS_SOME (supported_function_decl tops c Internal)) calls
Proof
  simp[EVERY_MEM, FORALL_PROD, source_body_call_supported_def,
       supported_linked_callee_def] >>
  metis_tac[supported_program_module_headers]
QED
