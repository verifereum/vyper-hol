(* PLAN 5.6 declaration whitelist and syntactic resolution.
   TOP-LEVEL: supported_declaration_header(s), supported_variable_decl,
   supported_hashmap_decl, supported_function_decl, supported_event_fields.
   No definition here checks or admits a function body. TASK_021 must conjoin
   its body checks; TASK_020 consumes the lookups. Typing is separate. *)
Theory supportedDecls
Ancestors
  supportedTypes vyperAST list alist

(* ===== Body-independent declarations ===== *)

Definition supported_interface_signature_def:
  supported_interface_signature tops (name, args, ret, mut) <=>
    EVERY (supported_value_type tops o SND) args /\
    supported_return_type tops ret
End

(* External arguments are decoded into fresh storage of their own type.
   Internal argument copies retain their separate layout restriction. *)
Definition supported_function_argument_def:
  supported_function_argument tops External ty = supported_place_type tops ty /\
  supported_function_argument tops vis ty = supported_value_type tops ty
End

Definition supported_function_return_def:
  supported_function_return tops External ty =
    (ty = NoneT \/ supported_place_type tops ty) /\
  supported_function_return tops vis ty = supported_return_type tops ty
End

Definition supported_declaration_header_def:
  supported_declaration_header tops top <=>
    case top of
      FunctionDecl vis mut nr rr name args defaults ret body =>
        ~nr /\ ~rr /\ NULL defaults /\
        EVERY (supported_function_argument tops vis o SND) args /\
        supported_function_return tops vis ret
    | VariableDecl Private Storage name ty (SOME slot) =>
        supported_storage_type tops ty
    | VariableDecl Private Transient name ty (SOME slot) =>
        supported_storage_type tops ty
    | HashMapDecl Private transient name kt vt (SOME slot) =>
        supported_hashmap_key_type kt /\ supported_hashmap_value tops vt
    | StructDecl name fields =>
        EVERY (supported_place_type tops o SND) fields
    | EventDecl name fields =>
        EVERY (supported_scalar_type o SND o FST) fields
    | InterfaceDecl name methods =>
        EVERY (supported_interface_signature tops) methods
    | _ => F
End

Definition supported_declaration_headers_def:
  supported_declaration_headers tops <=>
    EVERY (supported_declaration_header tops) tops
End

(* ===== Declaration lookups (first match; module NONE only) ===== *)

Definition supported_variable_decl_def:
  supported_variable_decl ([] : toplevel list) (id : nsid) = NONE /\
  supported_variable_decl (top :: rest) (module_id, name) =
    if module_id <> NONE then NONE
    else case top of
      VariableDecl vis mut s ty slot =>
        if s = name then SOME (vis, mut, ty, slot)
        else supported_variable_decl rest (module_id, name)
    | _ => supported_variable_decl rest (module_id, name)
End

Definition supported_hashmap_decl_def:
  supported_hashmap_decl ([] : toplevel list) (id : nsid) = NONE /\
  supported_hashmap_decl (top :: rest) (module_id, name) =
    if module_id <> NONE then NONE
    else case top of
      HashMapDecl vis transient s kt vt slot =>
        if s = name then SOME (vis, transient, kt, vt, slot)
        else supported_hashmap_decl rest (module_id, name)
    | _ => supported_hashmap_decl rest (module_id, name)
End

Definition supported_function_decl_def:
  supported_function_decl ([] : toplevel list) (id : nsid) vis = NONE /\
  supported_function_decl (top :: rest) (module_id, name) vis =
    if module_id <> NONE then NONE
    else case top of
      FunctionDecl v mut nr rr s args defaults ret body =>
        if s = name /\ v = vis then
          SOME (mut, nr, rr, args, defaults, ret, body)
        else supported_function_decl rest (module_id, name) vis
    | _ => supported_function_decl rest (module_id, name) vis
End

Definition supported_event_fields_def:
  supported_event_fields ([] : toplevel list) (id : nsid) = NONE /\
  supported_event_fields (top :: rest) (module_id, name) =
    if module_id <> NONE then NONE
    else case top of
      EventDecl s fields =>
        if s = name then SOME fields
        else supported_event_fields rest (module_id, name)
    | _ => supported_event_fields rest (module_id, name)
End

(* ===== Consumer contracts ===== *)

Theorem supported_function_header_contract:
  supported_declaration_header tops
    (FunctionDecl vis mut nr rr name args defaults ret body) <=>
  ~nr /\ ~rr /\ NULL defaults /\
  EVERY (supported_function_argument tops vis o SND) args /\
  supported_function_return tops vis ret
Proof
  simp[supported_declaration_header_def]
QED

Theorem supported_header_body_independent:
  supported_declaration_header tops
    (FunctionDecl vis mut nr rr name args defaults ret body1) =
  supported_declaration_header tops
    (FunctionDecl vis mut nr rr name args defaults ret body2)
Proof
  simp[supported_function_header_contract]
QED

Theorem supported_storage_header_contract:
  supported_declaration_header tops
    (VariableDecl Private Storage name ty (SOME slot)) <=>
  supported_storage_type tops ty
Proof
  simp[supported_declaration_header_def]
QED

Theorem supported_transient_header_contract:
  supported_declaration_header tops
    (VariableDecl Private Transient name ty (SOME slot)) <=>
  supported_storage_type tops ty
Proof
  simp[supported_declaration_header_def]
QED

Theorem supported_hashmap_header_contract:
  supported_declaration_header tops
    (HashMapDecl vis transient name kt vt slot) <=>
  vis = Private /\ IS_SOME slot /\
  supported_hashmap_key_type kt /\ supported_hashmap_value tops vt
Proof
  Cases_on `vis` >> Cases_on `slot` >> simp[supported_declaration_header_def]
QED

Theorem supported_public_variables_rejected:
  ~supported_declaration_header tops (VariableDecl Public mut name ty slot)
Proof
  Cases_on `mut` >> Cases_on `slot` >>
  simp[supported_declaration_header_def]
QED

Theorem supported_missing_slots_rejected:
  ~supported_declaration_header tops (VariableDecl vis mut name ty NONE) /\
  ~supported_declaration_header tops (HashMapDecl vis transient name kt vt NONE)
Proof
  Cases_on `vis` >> Cases_on `mut` >> Cases_on `transient` >>
  Cases_on `vt` >> simp[supported_declaration_header_def]
QED

Theorem supported_immutables_constants_rejected:
  ~supported_declaration_header tops (VariableDecl vis Immutable name ty slot) /\
  ~supported_declaration_header tops (VariableDecl vis (Constant e) name ty slot)
Proof
  Cases_on `vis` >> Cases_on `slot` >>
  simp[supported_declaration_header_def]
QED

Theorem supported_hashmap_location_independent:
  supported_declaration_header tops (HashMapDecl vis T name kt vt slot) <=>
  supported_declaration_header tops (HashMapDecl vis F name kt vt slot)
Proof
  simp[supported_hashmap_header_contract]
QED

Theorem supported_flags_rejected:
  ~supported_declaration_header tops (FlagDecl name members)
Proof
  simp[supported_declaration_header_def]
QED

Theorem supported_lookup_other_module:
  module_id <> NONE ==>
    supported_variable_decl tops (module_id, name) = NONE /\
    supported_hashmap_decl tops (module_id, name) = NONE /\
    supported_function_decl tops (module_id, name) vis = NONE /\
    supported_event_fields tops (module_id, name) = NONE
Proof
  Cases_on `tops` >> simp[supported_variable_decl_def,
    supported_hashmap_decl_def, supported_function_decl_def,
    supported_event_fields_def]
QED
