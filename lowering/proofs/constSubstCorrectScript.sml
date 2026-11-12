(* Proof interfaces for declaration-order constant inlining. *)
Theory constSubstCorrect
Ancestors
  constSubst vyperTypeConstantFold vyperAST vyperTypeContractContext
  vyperState vyperValue vyperContext vyperTypeInvariants vyperInterpreter
  vyperMisc vyperTyping vyperTypeValues
  vyperPlaceFrames vyperStatePreservation
  vyperImmutablesPreservation vyperScopePreservation vyperCallOutcomeFrame
  vyperCreateFrame vyperCallFrame vyperMachineFrame
  vyperTypeContract vyperTypeContractStaticMaps vyperTypeSystem finite_map alist list

Definition const_local_refs_def:
  const_local_refs (TopLevelName ty ns) =
    (case ns of (NONE,id) => [(ty,id)] | _ => []) /\
  const_local_refs (StructLit ty ns fs) = const_local_fields fs /\
  const_local_refs (Subscript ty a b) = const_local_refs a ++ const_local_refs b /\
  const_local_refs (Attribute ty a id) = const_local_refs a /\
  const_local_refs (Builtin ty bi es) = const_local_exprs es /\
  const_local_refs (TypeBuiltin ty bi t es) = const_local_exprs es /\
  const_local_refs e = [] /\
  const_local_exprs [] = [] /\
  const_local_exprs (e::es) = const_local_refs e ++ const_local_exprs es /\
  const_local_fields [] = [] /\
  const_local_fields ((id,e)::fs) = const_local_refs e ++ const_local_fields fs
Termination
  WF_REL_TAC `measure (\x. case x of
      INL e => expr_size e
    | INR (INL es) => list_size expr_size es
    | INR (INR fs) => list_size (pair_size (list_size char_size) expr_size) fs)` >>
  simp[expr_size_def, list_size_def, basicSizeTheory.pair_size_def]
End

Definition const_acc_agrees_def:
  const_acc_agrees mods imms E A <=>
    ALL_DISTINCT (MAP FST E) /\ set (MAP FST E) = FDOM A /\
    (!id r. ALOOKUP E id = SOME r ==>
      constant_expr mods r /\ const_local_refs r = [] /\
      ?tv v. FLOOKUP A id = SOME (tv,v) /\
        evaluate_type (type_env_all_modules mods) (expr_type r) = SOME tv /\
        constant_value mods imms r = SOME v)
End

Theorem const_local_exprs_map:
  const_local_exprs es = FLAT (MAP const_local_refs es)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_local_fields_map:
  const_local_fields fs = const_local_exprs (MAP SND fs)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem fold_const_builtin_constant:
  constant_builtin bi /\ EVERY (constant_expr mods) es ==>
  constant_expr mods (fold_const_builtin ty bi es)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem fold_const_expr_constant:
  (!e. constant_expr mods e ==> constant_expr mods (fold_const_expr e)) /\
  (!es. EVERY (constant_expr mods) es ==>
    EVERY (constant_expr mods) (fold_const_exprs es)) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) ==>
    EVERY (constant_expr mods) (MAP SND (fold_const_fields fs)))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem fold_const_builtin_value:
  constant_value mods imms (fold_const_builtin ty bi es) =
  constant_value mods imms (Builtin ty bi es)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem fold_const_expr_value_aux[local]:
  (!e. constant_expr mods e ==>
    constant_value mods imms (fold_const_expr e) = constant_value mods imms e) /\
  (!es. EVERY (constant_expr mods) es ==>
    MAP expr_type (fold_const_exprs es) = MAP expr_type es /\
    constant_values mods imms (fold_const_exprs es) = constant_values mods imms es /\
    LENGTH (fold_const_exprs es) = LENGTH es) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) ==>
    MAP FST (fold_const_fields fs) = MAP FST fs /\
    constant_values mods imms (MAP SND (fold_const_fields fs)) =
      constant_values mods imms (MAP SND fs))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem fold_const_expr_value:
  constant_expr mods e ==>
  constant_value mods imms (fold_const_expr e) = constant_value mods imms e
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem fold_const_builtin_local_closed:
  const_local_exprs es = [] ==>
  const_local_refs (fold_const_builtin ty bi es) = []
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem fold_const_expr_local_closed:
  (!e. const_local_refs e = [] ==>
    const_local_refs (fold_const_expr e) = []) /\
  (!es. const_local_exprs es = [] ==>
    const_local_exprs (fold_const_exprs es) = []) /\
  (!fs. const_local_fields fs = [] ==>
    const_local_fields (fold_const_fields fs) = [])
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem subst_consts_expr_type_constant:
  constant_expr mods e /\
  (!ty id r. MEM (ty,id) (const_local_refs e) /\ ALOOKUP E id = SOME r ==>
    expr_type r = ty) ==>
  expr_type (subst_consts_expr E e) = expr_type e
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Definition const_replacements_ok_def:
  const_replacements_ok mods imms E refs <=>
    !ty id r. MEM (ty,id) refs /\ ALOOKUP E id = SOME r ==>
      expr_type r = ty /\ constant_expr mods r /\
      constant_value mods imms r = constant_value mods imms (TopLevelName ty (NONE,id))
End

Theorem const_replacements_ok_append[simp]:
  const_replacements_ok mods imms E (a ++ b) <=>
  const_replacements_ok mods imms E a /\ const_replacements_ok mods imms E b
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_subst_constant_value:
  (!e. !E. constant_expr mods e /\
      const_replacements_ok mods imms E (const_local_refs e) ==>
    expr_type (subst_consts_expr E e) = expr_type e /\
    constant_expr mods (subst_consts_expr E e) /\
    constant_value mods imms (subst_consts_expr E e) = constant_value mods imms e) /\
  (!es. !E. EVERY (constant_expr mods) es /\
      const_replacements_ok mods imms E (const_local_exprs es) ==>
    MAP expr_type (subst_consts_exprs E es) = MAP expr_type es /\
    EVERY (constant_expr mods) (subst_consts_exprs E es) /\
    constant_values mods imms (subst_consts_exprs E es) = constant_values mods imms es /\
    LENGTH (subst_consts_exprs E es) = LENGTH es) /\
  (!fs. !E. EVERY (constant_expr mods) (MAP SND fs) /\
      const_replacements_ok mods imms E (const_local_fields fs) ==>
    MAP FST (subst_consts_fields E fs) = MAP FST fs /\
    EVERY (constant_expr mods) (MAP SND (subst_consts_fields E fs)) /\
    constant_values mods imms (MAP SND (subst_consts_fields E fs)) =
      constant_values mods imms (MAP SND fs))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_subst_expr_value:
  constant_expr mods e /\ const_replacements_ok mods imms E (const_local_refs e) ==>
  constant_value mods imms (subst_consts_expr E e) = constant_value mods imms e
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_subst_expr_annotation:
  constant_expr mods e /\ const_replacements_ok mods imms E (const_local_refs e) ==>
  expr_type (subst_consts_expr E e) = expr_type e
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_subst_expr_constant:
  constant_expr mods e /\ const_replacements_ok mods imms E (const_local_refs e) ==>
  constant_expr mods (subst_consts_expr E e)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem constant_value_local_closed:
  (!e. !imms imms'. constant_expr mods e /\ const_local_refs e = [] /\
    (!src. IS_SOME src ==> get_source_immutables src imms = get_source_immutables src imms') ==>
    constant_value mods imms e = constant_value mods imms' e) /\
  (!es. !imms imms'. EVERY (constant_expr mods) es /\ const_local_exprs es = [] /\
    (!src. IS_SOME src ==> get_source_immutables src imms = get_source_immutables src imms') ==>
    constant_values mods imms es = constant_values mods imms' es) /\
  (!fs. !imms imms'. EVERY (constant_expr mods) (MAP SND fs) /\ const_local_fields fs = [] /\
    (!src. IS_SOME src ==> get_source_immutables src imms = get_source_immutables src imms') ==>
    constant_values mods imms (MAP SND fs) = constant_values mods imms' (MAP SND fs))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem constant_value_closed_stable:
  constant_expr mods e /\ const_local_refs e = [] /\
  (!src. IS_SOME src ==> get_source_immutables src imms = get_source_immutables src imms') ==>
  constant_value mods imms e = constant_value mods imms' e
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED


Definition const_decl_names_def:
  const_decl_names [] = [] /\
  const_decl_names (VariableDecl vis (Constant e) id ty slot :: ts) =
    id :: const_decl_names ts /\
  const_decl_names (_ :: ts) = const_decl_names ts
End

Theorem checked_const_decl_typed:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl vis (Constant e) id ty slot) ts ==>
  assignable_type (type_env_all_modules mods) ty /\
  well_typed_expr (artifact_env artifact mods src) e /\
  expr_type e = ty /\ constant_expr mods e
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem constant_value_local_refs_present:
  (!e. !imms v ty id.
    constant_value mods imms e = SOME v /\ MEM (ty,id) (const_local_refs e) ==>
    IS_SOME (FLOOKUP (get_source_immutables NONE imms) id)) /\
  (!es. !imms vs ty id.
    constant_values mods imms es = SOME vs /\ MEM (ty,id) (const_local_exprs es) ==>
    IS_SOME (FLOOKUP (get_source_immutables NONE imms) id)) /\
  (!fs. !imms vs ty id.
    constant_values mods imms (MAP SND fs) = SOME vs /\
    MEM (ty,id) (const_local_fields fs) ==>
    IS_SOME (FLOOKUP (get_source_immutables NONE imms) id))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_decl_names_MEM:
  !ts id. MEM id (const_decl_names ts) <=>
    ?vis e ty slot. MEM (VariableDecl vis (Constant e) id ty slot) ts
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_decl_names_distinct:
  !ts src. ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)) ==>
    ALL_DISTINCT (const_decl_names ts)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_const_decl_names_distinct:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods src = SOME ts ==> ALL_DISTINCT (const_decl_names ts)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem constants_fold_module_prefix_refs:
  !pre A B vis e id ty slot rest ety n.
  constants_fold_module mods imms NONE
    (pre ++ VariableDecl vis (Constant e) id ty slot :: rest) A = SOME B /\
  MEM (ety,n) (const_local_refs e) ==>
  IS_SOME (FLOOKUP (get_source_immutables NONE imms) n) \/
  n IN FDOM A \/ MEM n (const_decl_names pre)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem constants_fold_append:
  !pre imms rest out.
  constants_fold mods imms (pre ++ rest) = SOME out ==>
  ?mid. constants_fold mods imms pre = SOME mid /\
        constants_fold mods mid rest = SOME out
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem constants_order_main_last:
  !mods tops. ALL_DISTINCT (MAP FST mods) /\ ALOOKUP mods NONE = SOME tops ==>
  ?imports. constants_order mods = imports ++ [(NONE,tops)] /\
    EVERY (IS_SOME o FST) imports
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem constants_fold_imports_preserve_local:
  !imports imms out. EVERY (IS_SOME o FST) imports /\
    constants_fold mods imms imports = SOME out ==>
    get_source_immutables NONE out = get_source_immutables NONE imms
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem constant_expr_local_refs_declared:
  (!e. constant_expr mods e ==>
    !ty id. MEM (ty,id) (const_local_refs e) ==> declared_constant mods NONE id) /\
  (!es. EVERY (constant_expr mods) es ==>
    !ty id. MEM (ty,id) (const_local_exprs es) ==> declared_constant mods NONE id) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) ==>
    !ty id. MEM (ty,id) (const_local_fields fs) ==> declared_constant mods NONE id)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_const_initializer_prefix_names:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  tops = pre ++ VariableDecl vis (Constant e) id ty slot :: rest /\
  MEM (ety,n) (const_local_refs e) ==>
  MEM n (const_decl_names pre)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_constant_refs_well_typed:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods ==>
  (!e. constant_expr mods e /\
    well_typed_expr (artifact_env artifact mods current_src) e ==>
    !ty id. MEM (ty,id) (const_local_refs e) ==>
      well_typed_expr (artifact_env artifact mods current_src) (TopLevelName ty (NONE,id))) /\
  (!es. EVERY (constant_expr mods) es /\
    well_typed_exprs (artifact_env artifact mods current_src) es ==>
    !ty id. MEM (ty,id) (const_local_exprs es) ==>
      well_typed_expr (artifact_env artifact mods current_src) (TopLevelName ty (NONE,id))) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) /\
    well_typed_named_exprs (artifact_env artifact mods current_src) fs ==>
    !ty id. MEM (ty,id) (const_local_fields fs) ==>
      well_typed_expr (artifact_env artifact mods current_src) (TopLevelName ty (NONE,id)))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_constant_reference_annotation:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl vis (Constant init) id ty slot) ts /\
  constant_expr mods e /\ well_typed_expr (artifact_env artifact mods current_src) e /\
  MEM (ann,id) (const_local_refs e) /\ src = NONE ==> ann = ty
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_const_initializer_prefix:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  tops = pre ++ VariableDecl vis (Constant e) id ty slot :: rest ==>
  constant_expr mods e /\ expr_type e = ty /\
  well_typed_expr (artifact_env artifact mods NONE) e /\
  (!ety n. MEM (ety,n) (const_local_refs e) ==>
    MEM n (const_decl_names pre) /\
    ?v init slot'. MEM (VariableDecl v (Constant init) n ety slot') pre)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_subst_local_refs_closed:
  (!e. !E. constant_expr mods e /\
    (!ty id. MEM (ty,id) (const_local_refs e) ==>
      ?r. ALOOKUP E id = SOME r /\ const_local_refs r = []) ==>
    const_local_refs (subst_consts_expr E e) = []) /\
  (!es. !E. EVERY (constant_expr mods) es /\
    (!ty id. MEM (ty,id) (const_local_exprs es) ==>
      ?r. ALOOKUP E id = SOME r /\ const_local_refs r = []) ==>
    const_local_exprs (subst_consts_exprs E es) = []) /\
  (!fs. !E. EVERY (constant_expr mods) (MAP SND fs) /\
    (!ty id. MEM (ty,id) (const_local_fields fs) ==>
      ?r. ALOOKUP E id = SOME r /\ const_local_refs r = []) ==>
    const_local_fields (subst_consts_fields E fs) = [])
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem merge_constant_imms_imports:
  IS_SOME src ==>
  get_source_immutables src (merge_constant_imms NONE A imms) =
  get_source_immutables src imms
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_acc_agrees_stable:
  const_acc_agrees mods imms E A /\
  (!src. IS_SOME src ==> get_source_immutables src imms = get_source_immutables src imms') ==>
  const_acc_agrees mods imms' E A
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_acc_agrees_empty:
  const_acc_agrees mods imms [] FEMPTY
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_acc_agrees_snoc:
  const_acc_agrees mods imms E A /\ ~MEM id (MAP FST E) /\
  constant_expr mods r /\ const_local_refs r = [] /\
  evaluate_type (type_env_all_modules mods) (expr_type r) = SOME tv /\
  constant_value mods imms' r = SOME v /\
  (!src. IS_SOME src ==> get_source_immutables src imms = get_source_immutables src imms') ==>
  const_acc_agrees mods imms' (E ++ [(id,r)]) (A |+ (id,(tv,v)))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_constant_name_fold:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  MEM (VariableDecl vis (Constant init) id ty slot) tops /\
  FLOOKUP A id = SOME (tv,v) ==>
  constant_value mods (merge_constant_imms NONE A imms)
    (TopLevelName ann (NONE,id)) = SOME v
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

(* Metadata connecting expanded syntax to its checked source declarations. *)
Definition const_prefix_syntax_def:
  const_prefix_syntax E pre <=>
    MAP FST E = const_decl_names pre /\
    (!id r. ALOOKUP E id = SOME r ==>
      ?vis init ty slot. MEM (VariableDecl vis (Constant init) id ty slot) pre /\
        expr_type r = ty)
End

Theorem checked_const_prefix_replacements:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  tops = pre ++ VariableDecl vis (Constant e) id ty slot :: rest /\
  const_prefix_syntax E pre /\
  const_acc_agrees mods (merge_constant_imms NONE A imms) E A ==>
  const_replacements_ok mods (merge_constant_imms NONE A imms) E (const_local_refs e) /\
  (!ann n. MEM (ann,n) (const_local_refs e) ==>
    ?r. ALOOKUP E n = SOME r /\ const_local_refs r = [])
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_decl_names_append:
  !pre rest. const_decl_names (pre ++ rest) = const_decl_names pre ++ const_decl_names rest
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_prefix_syntax_snoc:
  const_prefix_syntax E pre /\ expr_type r = ty ==>
  const_prefix_syntax (E ++ [(id,r)]) (pre ++ [VariableDecl vis (Constant init) id ty slot])
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_const_acc_step:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  tops = pre ++ VariableDecl vis (Constant e) id ty slot :: rest /\
  const_prefix_syntax E pre /\
  const_acc_agrees mods (merge_constant_imms NONE A imms) E A /\
  evaluate_type (type_env_all_modules mods) ty = SOME tv /\
  constant_value mods (merge_constant_imms NONE A imms) e = SOME v ==>
  const_acc_agrees mods (merge_constant_imms NONE (A |+ (id,(tv,v))) imms)
    (E ++ [(id,fold_const_expr (subst_consts_expr E e))]) (A |+ (id,(tv,v))) /\
  const_prefix_syntax (E ++ [(id,fold_const_expr (subst_consts_expr E e))])
    (pre ++ [VariableDecl vis (Constant e) id ty slot])
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_prefix_syntax_skip:
  const_prefix_syntax E pre /\ const_decl_names [t] = [] ==>
  const_prefix_syntax E (pre ++ [t])
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem constants_fold_module_subst_acc:
  !ts pre E A B.
    check_contract mode layouts addr mods = SOME artifact /\
    ALOOKUP mods NONE = SOME tops /\ tops = pre ++ ts /\
    const_prefix_syntax E pre /\
    const_acc_agrees mods (merge_constant_imms NONE A imms) E A /\
    constants_fold_module mods imms NONE ts A = SOME B ==>
    const_acc_agrees mods (merge_constant_imms NONE B imms) (module_consts_env ts E) B /\
    const_prefix_syntax (module_consts_env ts E) tops
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_module_consts_env_agrees:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A ==>
  const_acc_agrees mods (merge_constant_imms NONE A imms) (module_consts_env tops []) A /\
  const_prefix_syntax (module_consts_env tops []) tops
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_module_consts_env_replacement:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  ALOOKUP (module_consts_env tops []) id = SOME r ==>
  ?vis init ty slot tv v.
    MEM (VariableDecl vis (Constant init) id ty slot) tops /\
    expr_type r = ty /\ FLOOKUP A id = SOME (tv,v) /\
    constant_expr mods r /\ const_local_refs r = [] /\
    evaluate_type (type_env_all_modules mods) ty = SOME tv /\
    constant_value mods (merge_constant_imms NONE A imms) r = SOME v
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_module_consts_env_runtime:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  ALOOKUP (module_consts_env tops []) id = SOME r /\
  (!src. IS_SOME src ==> get_source_immutables src imms' = get_source_immutables src imms) /\
  (!tv v. FLOOKUP A id = SOME (tv,v) ==>
    FLOOKUP (get_source_immutables NONE imms') id = SOME (tv,v)) ==>
  constant_expr mods r /\ const_local_refs r = [] /\
  constant_value mods imms' r = constant_value mods imms' (TopLevelName (expr_type r) (NONE,id))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_const_initializer_read_fold:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods src = SOME full /\
  MEM (VariableDecl vis (Constant e) id ty slot) full /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
  constant_fmap_declared_typed (type_env_all_modules mods) full acc /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  (do pv <- eval_expr cx e; read_result cx pv od)
    (initial_state (merge_constants cx.txn.target src acc am) [FEMPTY]) = (INL v,st') ==>
  constant_value mods
    (merge_constant_imms src acc (constant_machine_immutables am cx.txn.target)) e = SOME v /\
  constant_fmap_declared_typed (type_env_all_modules mods) full (acc |+ (id,(tv,v)))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem constants_env_fold_agreement_acc:
  !ts acc A.
    check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
    ALOOKUP cx.sources cx.txn.target = SOME mods /\
    ALOOKUP mods src = SOME full /\ EVERY (\t. MEM t full) ts /\
    deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
    constant_fmap_declared_typed (type_env_all_modules mods) full acc /\
    constants_env cx am cx.txn.target src ts acc = SOME A ==>
    constants_fold_module mods (constant_machine_immutables am cx.txn.target) src ts acc = SOME A /\
    constant_fmap_declared_typed (type_env_all_modules mods) full A
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_constants_env_fold:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME tops /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
  constants_env cx am cx.txn.target NONE tops FEMPTY = SOME A ==>
  constants_fold_module mods (constant_machine_immutables am cx.txn.target)
    NONE tops FEMPTY = SOME A
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_constants_env_subst_agrees:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME tops /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
  constants_env cx am cx.txn.target NONE tops FEMPTY = SOME A ==>
  const_acc_agrees mods
    (merge_constant_imms NONE A (constant_machine_immutables am cx.txn.target))
    (module_consts_env tops []) A /\
  const_prefix_syntax (module_consts_env tops []) tops
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

(* The typing premise is the evaluator's ordinary expression interface; the
   collector supplies the value, not a new runtime typing assumption. *)
Theorem checked_module_consts_env_runtime_read:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  ALOOKUP (module_consts_env tops []) id = SOME r /\
  (!src. IS_SOME src ==>
    get_source_immutables src (constant_machine_immutables am cx.txn.target) =
    get_source_immutables src imms) /\
  (!tv v. FLOOKUP A id = SOME (tv,v) ==>
    FLOOKUP (get_source_immutables NONE
      (constant_machine_immutables am cx.txn.target)) id = SOME (tv,v)) /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
  well_typed_expr (artifact_env artifact mods current_src) r ==>
  ?v pv.
    constant_value mods (constant_machine_immutables am cx.txn.target)
      (TopLevelName (expr_type r) (NONE,id)) = SOME v /\
    eval_expr cx r (initial_state am sc) = (INL pv,initial_state am sc) /\
    read_result cx pv (initial_state am sc) = (INL v,initial_state am sc) /\
    value_runtime_typed (artifact_env artifact mods current_src) (expr_type r) v
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED


(* Constant roots cannot occur in the checked immutable-write namespace. *)
Theorem checked_constant_not_assignable:
  contract_namespaces_ok F mods /\ declared_constant mods src id ==>
  FLOOKUP (build_contract_type_artifact F mods).cta_bare_global_assignable
    (src,id) = NONE
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

(* Mutation typing is inherited by the syntactic place root. *)
Definition base_target_root_def:
  base_target_root (AttributeTarget t id) = base_target_root t /\
  base_target_root (SubscriptTarget t e) = base_target_root t /\
  base_target_root t = t
End

Theorem type_place_target_root:
  !bt env. IS_SOME (type_place_target env bt) ==>
    IS_SOME (type_place_target env (base_target_root bt))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_constant_bare_global:
  contract_namespaces_ok F mods /\ declared_constant mods src id ==>
  IS_SOME (FLOOKUP (build_contract_type_artifact F mods).cta_bare_globals (src,id))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem constant_root_not_typable:
  FLOOKUP env.bare_global_assignable (src,id) = NONE /\
  IS_SOME (FLOOKUP env.bare_globals (src,id)) ==>
  type_place_target env (TopLevelNameTarget (src,id)) = NONE
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem typed_mutation_root_excludes_constant:
  IS_SOME (type_place_target env bt) /\
  FLOOKUP env.bare_global_assignable (src,id) = NONE /\
  IS_SOME (FLOOKUP env.bare_globals (src,id)) ==>
  base_target_root bt <> TopLevelNameTarget (src,id)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem push_function_target:
  push_function fn sc cx st = (INL cx',st') ==> cx'.txn.target = cx.txn.target
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem extend_storage_place_not_immutable:
  extend_storage_place cx tr slot tv sb st <>
    (INL (ImmutablePlace src id path),st')
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem extend_place_immutable_root:
  extend_place cx pv sb st = (INL (PlaceR (ImmutablePlace src id path)),st') ==>
  ?p. pv = PlaceR (ImmutablePlace src id p)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem lookup_global_immutable_root:
  lookup_global cx src0 id0 st = (INL (PlaceR (ImmutablePlace src id path)),st') ==>
  src0 = src /\ id0 = id
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem eval_base_place_immutable_root:
  !bt cx st src id path st'.
    eval_base_place cx bt st = (INL (PlaceR (ImmutablePlace src id path)),st') ==>
    base_target_root bt = TopLevelNameTarget (src,id)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem eval_target_place_immutable_root:
  eval_target_place cx bt st = (INL (ImmutablePlace src id path),st') ==>
  base_target_root bt = TopLevelNameTarget (src,id)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem typed_base_atarget:
  atarget_accepts env (BaseTarget bt) ty ==>
  IS_SOME (type_place_target env bt)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem typed_tuple_atarget_member:
  atarget_accepts env (TupleTarget tgts) ty /\ MEM tgt tgts ==>
  ?t. well_typed_atarget env tgt t
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem typed_atarget_base:
  well_typed_atarget env (BaseTarget bt) ty ==>
  IS_SOME (type_place_target env bt)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem typed_atarget_tuple_member:
  well_typed_atarget env (TupleTarget tgts) ty /\ MEM tgt tgts ==>
  ?t. well_typed_atarget env tgt t
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_signature_callable_mode:
  check_contract F cx.layouts cx.txn.target mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  FLOOKUP art.cta_fn_sigs (src,fn) = SOME sig /\
  get_module_code cx src = SOME ts ==>
  lookup_callable_function mode fn ts = lookup_callable_function F fn ts
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

(* A typed internal call selects a live signature from the actual checked
   artifact.  No runtime stack or global evaluator soundness is needed. *)
Theorem checked_callable_body_typing:
  check_contract F cx.layouts cx.txn.target mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  FLOOKUP art.cta_fn_sigs (src,fn) = SOME sig /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function mode fn ts = SOME (mut,nr,args,dflts,ret,ss) ==>
  IS_SOME (type_stmts (function_entry_env art mods src Internal args) ret ss) /\
  well_typed_exprs (defaults_env (function_entry_env art mods src Internal args)) dflts
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_typed_intcall_body:
  check_contract F cx.layouts cx.txn.target mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  well_typed_expr env (Call ty (IntCall (src,fn)) es drv) /\
  env.fn_sigs = art.cta_fn_sigs /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function mode fn ts = SOME (mut,nr,args,dflts,ret,ss) ==>
  IS_SOME (type_stmts (function_entry_env art mods src Internal args) ret ss) /\
  well_typed_exprs (defaults_env (function_entry_env art mods src Internal args)) dflts
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_artifact_mutation_root:
  check_contract F layouts addr mods = SOME art /\
  declared_constant mods src id /\
  env.bare_global_assignable = art.cta_bare_global_assignable /\
  env.bare_globals = art.cta_bare_globals /\
  IS_SOME (type_place_target env bt) ==>
  base_target_root bt <> TopLevelNameTarget (src,id)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_artifact_intcall_body:
  check_contract F cx.layouts cx.txn.target mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  well_typed_expr (artifact_env art mods current_src)
    (Call ty (IntCall (src,fn)) es drv) /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) ==>
  IS_SOME (type_stmts (function_entry_env art mods src Internal args) ret ss) /\
  well_typed_exprs (defaults_env (function_entry_env art mods src Internal args)) dflts
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem function_entry_constant_maps:
  (function_entry_env art mods src Internal args).bare_globals = art.cta_bare_globals /\
  (function_entry_env art mods src Internal args).bare_global_assignable =
    art.cta_bare_global_assignable /\
  (function_entry_env art mods src Internal args).fn_sigs = art.cta_fn_sigs /\
  (defaults_env (function_entry_env art mods src Internal args)).bare_globals = art.cta_bare_globals /\
  (defaults_env (function_entry_env art mods src Internal args)).bare_global_assignable =
    art.cta_bare_global_assignable /\
  (defaults_env (function_entry_env art mods src Internal args)).fn_sigs = art.cta_fn_sigs
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem typed_assign_target:
  IS_SOME (type_stmt env ret (Assign tgt e)) ==>
  atarget_accepts env tgt (expr_type e)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem typed_augassign_target:
  IS_SOME (type_stmt env ret (AugAssign ty bt bop e)) ==>
  IS_SOME (type_place_target env bt)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem typed_append_target:
  IS_SOME (type_stmt env ret (Append bt e)) ==>
  IS_SOME (type_place_target env bt)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem typed_pop_target:
  well_typed_expr env (Pop ty bt) ==> IS_SOME (type_place_target env bt)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

(* A cell frame observes exactly one address/source/name, including absence.
   It is independent of the constant-footprint observation relation below. *)
Definition protected_cell_frame_def:
  protected_cell_frame addr src id (st:evaluation_state) (st':evaluation_state) <=>
    OPTION_BIND (ALOOKUP st'.immutables addr)
      (\imms. FLOOKUP (get_source_immutables src imms) id) =
    OPTION_BIND (ALOOKUP st.immutables addr)
      (\imms. FLOOKUP (get_source_immutables src imms) id)
End

Theorem protected_cell_frame_refl[simp]:
  protected_cell_frame addr src id st st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_eq:
  st'.immutables = st.immutables ==> protected_cell_frame addr src id st st'
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_trans:
  protected_cell_frame addr src id s t /\ protected_cell_frame addr src id t u ==>
  protected_cell_frame addr src id s u
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem set_immutable_other_cell_frame:
  (addr <> cx.txn.target \/ src <> written_src \/ id <> written_id) /\
  set_immutable cx written_src written_id tv v st = (res,st') ==>
  protected_cell_frame addr src id st st'
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Definition place_excludes_cell_def:
  place_excludes_cell cx addr src id p <=>
    !written_src written_id path.
      p = ImmutablePlace written_src written_id path ==>
      addr <> cx.txn.target \/ src <> written_src \/ id <> written_id
End

Theorem write_place_protected_cell:
  place_excludes_cell cx addr src id p /\
  write_place cx p v st = (res,st') ==>
  protected_cell_frame addr src id st st'
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem append_place_protected_cell:
  !cx addr src id p v st res st'.
  place_excludes_cell cx addr src id p /\
  append_place cx p v st = (res,st') ==>
  protected_cell_frame addr src id st st'
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem pop_place_protected_cell:
  !cx addr src id p st res st'.
  place_excludes_cell cx addr src id p /\
  pop_place cx p st = (res,st') ==>
  protected_cell_frame addr src id st st'
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem typed_target_place_excludes_constant:
  IS_SOME (type_place_target env bt) /\
  FLOOKUP env.bare_global_assignable (src,id) = NONE /\
  IS_SOME (FLOOKUP env.bare_globals (src,id)) /\
  eval_target_place cx bt st = (INL p,st') ==>
  place_excludes_cell cx addr src id p
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_state:
  (!st res st'. f st = (res,st') ==> st' = st) ==>
  state_rel_frame (protected_cell_frame addr src id) f
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_eq_op:
  (!st res st'. f st = (res,st') ==> st'.immutables = st.immutables) ==>
  state_rel_frame (protected_cell_frame addr src id) f
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_bind:
  state_rel_frame (protected_cell_frame addr src id) f /\
  (!s v t. f s = (INL v,t) ==>
    state_rel_frame (protected_cell_frame addr src id) (g v)) ==>
  state_rel_frame (protected_cell_frame addr src id) (vyperState$bind f g)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_finally[local]:
  state_rel_frame (protected_cell_frame addr src id) f /\
  state_rel_frame (protected_cell_frame addr src id) g ==>
  state_rel_frame (protected_cell_frame addr src id) (finally f g)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_reads:
  state_rel_frame (protected_cell_frame addr src id) (read_result cx pv) /\
  state_rel_frame (protected_cell_frame addr src id) (read_results cx results) /\
  state_rel_frame (protected_cell_frame addr src id) (select_result cx ann pv sb) /\
  state_rel_frame (protected_cell_frame addr src id) (conditional_result cx pv) /\
  state_rel_frame (protected_cell_frame addr src id) (lookup_global cx source nm) /\
  state_rel_frame (protected_cell_frame addr src id) (lookup_flag_mem cx nsid mid) /\
  state_rel_frame (protected_cell_frame addr src id) (read_storage_slot cx b slot ty) /\
  state_rel_frame (protected_cell_frame addr src id) (result_array_length cx pv) /\
  state_rel_frame (protected_cell_frame addr src id) (lift_sum z) /\
  state_rel_frame (protected_cell_frame addr src id) (get_immutables cx source) /\
  state_rel_frame (protected_cell_frame addr src id) (get_place pv) /\
  state_rel_frame (protected_cell_frame addr src id) (read_place cx p) /\
  state_rel_frame (protected_cell_frame addr src id) (place_type_value cx p) /\
  state_rel_frame (protected_cell_frame addr src id) (extend_place cx pv sb) /\
  state_rel_frame (protected_cell_frame addr src id) (resolve_array_element cx b slot ty subs)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_primitives:
  state_rel_frame (protected_cell_frame addr src id) get_scopes /\
  state_rel_frame (protected_cell_frame addr src id) (set_scopes scs) /\
  state_rel_frame (protected_cell_frame addr src id) push_scope /\
  state_rel_frame (protected_cell_frame addr src id) pop_scope /\
  state_rel_frame (protected_cell_frame addr src id) (push_scope_with_var nm ty v) /\
  state_rel_frame (protected_cell_frame addr src id) (new_variable nm ty v) /\
  state_rel_frame (protected_cell_frame addr src id) (append_logs ls) /\
  state_rel_frame (protected_cell_frame addr src id) (push_log lg) /\
  state_rel_frame (protected_cell_frame addr src id) get_pending_deletions /\
  state_rel_frame (protected_cell_frame addr src id) (update_pending_deletions fp) /\
  state_rel_frame (protected_cell_frame addr src id) (transfer_value sender target amount) /\
  state_rel_frame (protected_cell_frame addr src id) (acquire_nonreentrant_lock target lock view) /\
  state_rel_frame (protected_cell_frame addr src id) (release_nonreentrant_lock target lock) /\
  state_rel_frame (protected_cell_frame addr src id) (push_function fn sc cx) /\
  state_rel_frame (protected_cell_frame addr src id) (pop_function scs) /\
  state_rel_frame (protected_cell_frame addr src id) (write_storage_slot cx b slot ty v) /\
  state_rel_frame (protected_cell_frame addr src id) (set_global cx source nm v)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

(* The call oracle and concrete EVM creation adapters update accounts,
   transient storage, logs and request/outcome queues, not immutable cells. *)
Theorem protected_cell_frame_locals:
  (!s t. t.scopes = s.scopes /\ t.immutables = s.immutables ==>
    protected_cell_frame addr src id s t)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_call_primitives:
  state_rel_frame (protected_cell_frame addr src id) (vyperState$return v) /\
  state_rel_frame (protected_cell_frame addr src id) (vyperState$raise e) /\
  state_rel_frame (protected_cell_frame addr src id) get_accounts /\
  state_rel_frame (protected_cell_frame addr src id) get_transient_storage /\
  state_rel_frame (protected_cell_frame addr src id) (update_accounts upd) /\
  state_rel_frame (protected_cell_frame addr src id) (update_transient upd_t) /\
  state_rel_frame (protected_cell_frame addr src id) (adopt_call_outcome rq co) /\
  state_rel_frame (protected_cell_frame addr src id)
    (take_call_outcome target calldata value_opt)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_pure_guards[local]:
  state_rel_frame (protected_cell_frame addr src id) (type_check b msg) /\
  state_rel_frame (protected_cell_frame addr src id) (check b msg) /\
  state_rel_frame (protected_cell_frame addr src id) (lift_option_type opt msg) /\
  state_rel_frame (protected_cell_frame addr src id) (lift_option opt msg)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_check_not_static[local,simp]:
  state_rel_frame (protected_cell_frame addr src id) (check_not_static cx)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_raw_call[local]:
  state_rel_frame (protected_cell_frame addr src id)
    (eval_raw_call cx flags target calldata amount gas)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_send[local]:
  state_rel_frame (protected_cell_frame addr src id) (eval_send cx has_gas vs)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_next_gas_reading:
  state_rel_frame (protected_cell_frame addr src id) next_gas_reading
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_create:
  state_rel_frame (protected_cell_frame addr src id)
    (eval_create cx kind has_salt rof arg_tys vs blueprint_size)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_extcall_tail:
  state_rel_frame (protected_cell_frame addr src id) k ==>
  state_rel_frame (protected_cell_frame addr src id)
    (do check success msg;
        update_accounts (K accounts); update_transient (K transient);
        append_logs logs; k od)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_mutations:
  place_excludes_cell cx addr src id p ==>
  state_rel_frame (protected_cell_frame addr src id) (write_place cx p v) /\
  state_rel_frame (protected_cell_frame addr src id) (append_place cx p v) /\
  state_rel_frame (protected_cell_frame addr src id) (pop_place cx p)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

(* A constant footprint records typed roots, rather than evaluator behavior. *)
Definition const_cells_agree_def:
  const_cells_agree roots (st:evaluation_state) <=>
    !addr src id tv root.
      MEM (addr,src,id,tv,root) roots ==>
      ?imms. ALOOKUP st.immutables addr = SOME imms /\
        FLOOKUP (get_source_immutables src imms) id = SOME (tv,root)
End

Definition const_result_at_def:
  const_result_at roots cx ty pv v <=>
    (?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v) /\
    (pv = Value v \/
     ?src id path tv root etv.
       pv = PlaceR (ImmutablePlace src id path) /\
       MEM (cx.txn.target,src,id,tv,root) roots /\
       subscripts_type tv path = SOME etv /\
       evaluate_type (get_tenv cx) ty = SOME etv /\
       evaluate_subscripts tv root path = INL v)
End

Definition const_results_related_def:
  const_results_related roots cx ty p q <=>
    p = q \/ ?v. const_result_at roots cx ty p v /\ const_result_at roots cx ty q v
End

Definition const_computations_related_def:
  const_computations_related R f g st <=>
    ?a b st'. f st = (a,st') /\ g st = (b,st') /\
      (case (a,b) of
       | (INL x,INL y) => R x y
       | (INR x,INR y) => x = y
       | _ => F)
End

Definition const_result_lists_related_def:
  const_result_lists_related roots cx tys ps qs <=>
    LIST_REL (\(ty,p) (ty',q).
      ty = ty' /\ const_results_related roots cx ty p q)
      (ZIP (tys,ps)) (ZIP (tys,qs)) /\
    LENGTH ps = LENGTH tys /\ LENGTH qs = LENGTH tys
End

Definition const_select_output_def:
  const_select_output (Value v) sb w = Value w /\
  const_select_output (PlaceR (ImmutablePlace src id path)) sb w =
    PlaceR (ImmutablePlace src id (path ++ [sb])) /\
  const_select_output pv sb w = Value w
End

Theorem constant_result_selection_outcome:
  constant_result_shape pv /\
  eval_result_typed (env,cx,st) pv (Type ty) /\
  read_result cx pv st = (INL v,st) /\
  env.type_defs = get_tenv cx /\ evaluate_type env.type_defs ty = SOME tv ==>
  select_result cx ty pv sb st =
    case evaluate_subscripts tv v [sb] of
    | INL w => (INL (const_select_output pv sb w),st)
    | INR err => (INR (Error err),st)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_result_at_observe:
  const_result_at roots cx ty pv v /\ const_cells_agree roots st ==>
  constant_result_shape pv /\
  read_result cx pv st = (INL v,st) /\
  (!env. env.type_defs = get_tenv cx ==>
    eval_result_typed (env,cx,st) pv (Type ty))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem constant_result_length_outcome:
  constant_result_shape pv /\ read_result cx pv st = (INL v,st) ==>
  result_array_length cx pv st = result_array_length cx (Value v) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_results_related_read:
  const_results_related roots cx ty p q /\ const_cells_agree roots st ==>
  read_result cx p st = read_result cx q st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_result_at_conditional:
  const_result_at roots cx ty pv v /\ const_cells_agree roots st ==>
  conditional_result cx pv st = (INL (Value v),st)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_results_related_conditional:
  const_results_related roots cx ty p q /\ const_cells_agree roots st ==>
  conditional_result cx p st = conditional_result cx q st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_result_lists_related_read:
  const_result_lists_related roots cx tys ps qs /\ const_cells_agree roots st ==>
  read_results cx ps st = read_results cx qs st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_results_related_length:
  const_results_related roots cx ty p q /\ const_cells_agree roots st ==>
  result_array_length cx p st = result_array_length cx q st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_result_at_select:
  const_result_at roots cx ty pv v /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  subscript_type tv sb = SOME etv /\
  evaluate_type (get_tenv cx) result_ty = SOME etv /\
  evaluate_subscripts tv v [sb] = INL w ==>
  const_result_at roots cx result_ty (const_select_output pv sb w) w
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_results_related_select:
  const_results_related roots cx ty p q /\ const_cells_agree roots st /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  subscript_type tv sb = SOME etv /\
  evaluate_type (get_tenv cx) result_ty = SOME etv ==>
  (?err. select_result cx ty p sb st = (INR err,st) /\
         select_result cx ty q sb st = (INR err,st)) \/
  (?p' q'. select_result cx ty p sb st = (INL p',st) /\
           select_result cx ty q sb st = (INL q',st) /\
           const_results_related roots cx result_ty p' q') \/ p = q
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_results_related_select_total:
  const_results_related roots cx ty p q /\ const_cells_agree roots st /\
  (!v tv w. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    evaluate_subscripts tv v [sb] = INL w ==>
    ?etv. subscript_type tv sb = SOME etv /\
      evaluate_type (get_tenv cx) result_ty = SOME etv) ==>
  const_computations_related (const_results_related roots cx result_ty)
    (select_result cx ty p sb) (select_result cx ty q sb) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_results_related_subscript:
  const_results_related roots cx ct p q /\ const_cells_agree roots st /\
  subscript_type_ok ct ie ty /\
  vyperTypeExprResult$subscript_index_matches ct ie idx ==>
  const_computations_related (const_results_related roots cx ty)
    (select_result cx ct p (ValueSubscript idx))
    (select_result cx ct q (ValueSubscript idx)) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_results_related_attribute:
  const_results_related roots cx ct p q /\ const_cells_agree roots st /\
  attribute_type (get_tenv cx) ct id = SOME ty ==>
  const_computations_related (const_results_related roots cx ty)
    (select_result cx ct p (AttrSubscript id))
    (select_result cx ct q (AttrSubscript id)) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_cells_agree_append:
  const_cells_agree (xs ++ ys) st <=>
  const_cells_agree xs st /\ const_cells_agree ys st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_result_at_mono:
  const_result_at xs cx ty pv v /\
  (!root. MEM root xs ==> MEM root ys) ==>
  const_result_at ys cx ty pv v
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_result_at_intro:
  constant_result_shape pv /\
  eval_result_typed (env,cx,st) pv (Type ty) /\
  env.type_defs = get_tenv cx /\ read_result cx pv st = (INL v,st) /\
  (?vt. evaluate_type (get_tenv cx) ty = SOME vt /\ value_has_type vt v) ==>
  ?roots. const_cells_agree roots st /\ const_result_at roots cx ty pv v
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_results_related_intro:
  constant_result_shape p /\ constant_result_shape q /\
  eval_result_typed (env,cx,st) p (Type ty) /\
  eval_result_typed (env,cx,st) q (Type ty) /\
  env.type_defs = get_tenv cx /\
  read_result cx p st = (INL v,st) /\ read_result cx q st = (INL v,st) /\
  (?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v) ==>
  ?roots. const_cells_agree roots st /\ const_results_related roots cx ty p q
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_module_consts_env_result_footprint:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  ALOOKUP (module_consts_env tops []) id = SOME r /\
  (!src. IS_SOME src ==>
    get_source_immutables src (constant_machine_immutables am cx.txn.target) =
    get_source_immutables src imms) /\
  (!tv v. FLOOKUP A id = SOME (tv,v) ==>
    FLOOKUP (get_source_immutables NONE
      (constant_machine_immutables am cx.txn.target)) id = SOME (tv,v)) /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
  well_typed_expr (artifact_env artifact mods current_src) r ==>
  ?v pv roots.
    eval_expr cx r (initial_state am sc) = (INL pv,initial_state am sc) /\
    read_result cx pv (initial_state am sc) = (INL v,initial_state am sc) /\
    const_cells_agree roots (initial_state am sc) /\
    const_results_related roots cx (expr_type r)
      (PlaceR (ImmutablePlace NONE id [])) pv
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

(* Mutation steps of the mutual frame consume recursive frames only for
   evaluation, and syntactic target typing only for the eventual write. *)
Theorem protected_cell_frame_typed_pop:
  well_typed_expr env (Pop ty bt) /\
  FLOOKUP env.bare_global_assignable (src,id) = NONE /\
  IS_SOME (FLOOKUP env.bare_globals (src,id)) /\
  state_rel_frame (protected_cell_frame addr src id) (eval_target_place cx bt) ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_expr cx (Pop ty bt))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_cells_agree:
  const_cells_agree roots st /\
  (!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
    protected_cell_frame addr src id st st') ==>
  const_cells_agree roots st'
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_typed_append:
  IS_SOME (type_stmt env ret (Append bt e)) /\
  FLOOKUP env.bare_global_assignable (src,id) = NONE /\
  IS_SOME (FLOOKUP env.bare_globals (src,id)) /\
  state_rel_frame (protected_cell_frame addr src id) (eval_target_place cx bt) /\
  state_rel_frame (protected_cell_frame addr src id) (eval_expr cx e) ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_stmt cx (Append bt e))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_typed_assign:
  IS_SOME (type_stmt env ret (Assign (BaseTarget bt) e)) /\
  FLOOKUP env.bare_global_assignable (src,id) = NONE /\
  IS_SOME (FLOOKUP env.bare_globals (src,id)) /\
  state_rel_frame (protected_cell_frame addr src id) (eval_target_place cx bt) /\
  state_rel_frame (protected_cell_frame addr src id) (eval_expr cx e) ==>
  state_rel_frame (protected_cell_frame addr src id)
    (eval_stmt cx (Assign (BaseTarget bt) e))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

(* Static inputs for the specialized evaluator frame.  No runtime invariant is
   hidden in these abbreviations. *)
Definition frame_maps_def:
  frame_maps env art <=>
    env.bare_globals = art.cta_bare_globals /\
    env.bare_global_assignable = art.cta_bare_global_assignable /\
    env.fn_sigs = art.cta_fn_sigs
End

Definition checked_frame_context_def:
  checked_frame_context cx mods art src id env <=>
    check_contract F cx.layouts cx.txn.target mods = SOME art /\
    ALOOKUP cx.sources cx.txn.target = SOME mods /\
    declared_constant mods src id /\ frame_maps env art
End

Theorem frame_maps_extend_local[simp]:
  frame_maps (extend_local env nm ty writable) art = frame_maps env art
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem frame_maps_defaults_env[simp]:
  frame_maps (defaults_env env) art = frame_maps env art
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem frame_maps_function_entry[simp]:
  frame_maps (function_entry_env art mods current_src Internal args) art
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_frame_context_transport:
  checked_frame_context cx mods art src id env /\
  cx'.layouts = cx.layouts /\ cx'.txn.target = cx.txn.target /\
  cx'.sources = cx.sources /\ frame_maps env' art ==>
  checked_frame_context cx' mods art src id env'
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_frame_context_stack[simp]:
  checked_frame_context (cx with stk := stack) mods art src id env =
  checked_frame_context cx mods art src id env
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_frame_context_push_function:
  checked_frame_context cx mods art src id env /\
  push_function fn sc cx st = (INL cx',st') ==>
  checked_frame_context cx' mods art src id env
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_frame_intcall_static:
  checked_frame_context cx mods art src id env /\
  well_typed_expr env (Call ty (IntCall (call_src,fn)) es drv) /\
  get_module_code cx call_src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) ==>
  checked_frame_context cx mods art src id
    (function_entry_env art mods call_src Internal args) /\
  IS_SOME (type_stmts (function_entry_env art mods call_src Internal args) ret ss) /\
  well_typed_exprs (defaults_env (function_entry_env art mods call_src Internal args)) dflts
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem type_frame_maps_mutual:
  (!env ret s env'. type_stmt env ret s = SOME env' ==>
    !art. frame_maps env art ==> frame_maps env' art) /\
  (!env ret ss env'. type_stmts env ret ss = SOME env' ==>
    !art. frame_maps env art ==> frame_maps env' art)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem type_stmt_frame_maps:
  type_stmt env ret s = SOME env' /\ frame_maps env art ==>
  frame_maps env' art
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem type_stmts_frame_maps:
  type_stmts env ret ss = SOME env' /\ frame_maps env art ==>
  frame_maps env' art
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Definition writable_atarget_def:
  writable_atarget env g <=> ?ty. atarget_accepts env g ty
End

Theorem writable_atarget_base:
  writable_atarget env (BaseTarget bt) ==> IS_SOME (type_place_target env bt)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem well_typed_atarget_writable:
  !g ty. well_typed_atarget env g ty ==> writable_atarget env g
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem writable_atarget_tuple:
  writable_atarget env (TupleTarget gs) ==> EVERY (writable_atarget env) gs
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem type_place_target_subscript_child:
  IS_SOME (type_place_target env (SubscriptTarget bt e)) ==>
  IS_SOME (type_place_target env bt) /\ well_typed_expr env e
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem type_place_target_attribute_child:
  IS_SOME (type_place_target env (AttributeTarget bt fld)) ==>
  IS_SOME (type_place_target env bt)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem frame_well_typed_exprs_every:
  !es. well_typed_exprs env es <=> EVERY (well_typed_expr env) es
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem frame_well_typed_exprs_slices:
  well_typed_exprs env es ==>
  well_typed_exprs env (TAKE n es) /\ well_typed_exprs env (DROP n es)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem frame_well_typed_exprs_member:
  well_typed_exprs env es /\ MEM e es ==> well_typed_expr env e
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem frame_well_typed_exprs_cons:
  well_typed_exprs env (e::es) <=>
  well_typed_expr env e /\ well_typed_exprs env es
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_frame_context_extend_local[simp]:
  checked_frame_context cx mods art src id (extend_local env nm ty writable) =
  checked_frame_context cx mods art src id env
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_frame_context_defaults_env[simp]:
  checked_frame_context cx mods art src id (defaults_env env) =
  checked_frame_context cx mods art src id env
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_frame_context_type_stmt:
  checked_frame_context cx mods art src id env /\
  type_stmt env ret s = SOME env' ==>
  checked_frame_context cx mods art src id env'
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_frame_context_type_stmts:
  checked_frame_context cx mods art src id env /\
  type_stmts env ret ss = SOME env' ==>
  checked_frame_context cx mods art src id env'
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_frame_context_function_entry:
  checked_frame_context cx mods art src id env ==>
  checked_frame_context cx mods art src id
    (function_entry_env art mods current_src Internal args)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_frame_context_constant_root:
  checked_frame_context cx mods art src id env ==>
  FLOOKUP env.bare_global_assignable (src,id) = NONE /\
  IS_SOME (FLOOKUP env.bare_globals (src,id))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem writable_atarget_member:
  EVERY (writable_atarget env) gs /\ MEM g gs ==> writable_atarget env g
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem writable_atarget_cons:
  EVERY (writable_atarget env) (g::gs) <=>
  writable_atarget env g /\ EVERY (writable_atarget env) gs
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem frame_ordered_custom_error_typing:
  well_typed_custom_error env err /\
  order_custom_error_args params err = SOME es ==>
  well_typed_exprs env es
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_return[simp]:
  state_rel_frame (protected_cell_frame addr src id) (return v)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_raise[simp]:
  state_rel_frame (protected_cell_frame addr src id) (raise ex)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_read_tail:
  (!v. state_rel_frame (protected_cell_frame addr src id) (k v)) ==>
  state_rel_frame (protected_cell_frame addr src id)
    (bind (read_result cx tv) k)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_string_raise:
  state_rel_frame (protected_cell_frame addr src id)
    (bind (read_result cx tv) (\v.
      bind (lift_option_type (dest_StringV v) "not StringV")
        (\s. raise (AssertException s))))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_custom_error_tail:
  state_rel_frame (protected_cell_frame addr src id)
    (bind (lift_option (build_custom_error_data tenv nm tys vs)
      "custom error encoding") (\data. raise (Error (RevertData data))))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_switch:
  state_rel_frame (protected_cell_frame addr src id) f /\
  state_rel_frame (protected_cell_frame addr src id) g ==>
  state_rel_frame (protected_cell_frame addr src id) (switch_BoolV cx tv f g)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_at:
  f st = (res,st') ==>
  state_rel_frame (protected_cell_frame addr src id) f ==>
  protected_cell_frame addr src id st st'
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem frame_subscript_typing:
  (well_typed_expr env (Subscript ty e idx) \/
   ?vt. type_place_expr env (Subscript ty e idx) = SOME vt) ==>
  (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) /\
  well_typed_expr env idx
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem frame_place_expr_other:
  type_place_expr env (IfExp ty a b c) = NONE /\
  type_place_expr env (StructLit ty nm fs) = NONE /\
  type_place_expr env (Attribute ty e fld) = NONE /\
  type_place_expr env (Builtin ty bt es) = NONE /\
  type_place_expr env (TypeBuiltin ty tbt aty es) = NONE /\
  type_place_expr env (Pop ty btgt) = NONE /\
  type_place_expr env (Call ty ct es d) = NONE
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_blueprint[local]:
  state_rel_frame (protected_cell_frame addr src id) (check_create_blueprint has_salt vs)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem protected_cell_frame_ext_call[local]:
  state_rel_frame (protected_cell_frame addr src id)
    (eval_ext_call cx static skip sig opts vs)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_protected_cell_frame_mutual_aux:
  (!cx s st res st'. eval_stmt cx s st = (res,st') ==>
    !mods art src id env addr ret. checked_frame_context cx mods art src id env /\
      IS_SOME (type_stmt env ret s) ==> protected_cell_frame addr src id st st') /\
  (!cx ss st res st'. eval_stmts cx ss st = (res,st') ==>
    !mods art src id env addr ret. checked_frame_context cx mods art src id env /\
      IS_SOME (type_stmts env ret ss) ==> protected_cell_frame addr src id st st') /\
  (!cx it st res st'. eval_iterator cx it st = (res,st') ==>
    !mods art src id env addr ty. checked_frame_context cx mods art src id env /\
      well_typed_iterator env ty it ==> protected_cell_frame addr src id st st') /\
  (!cx tyv nm body vs st res st'. eval_for cx tyv nm body vs st = (res,st') ==>
    !mods art src id env addr ret. checked_frame_context cx mods art src id env /\
      IS_SOME (type_stmts env ret body) ==> protected_cell_frame addr src id st st') /\
  (!cx e st res st'. eval_expr cx e st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) ==>
      protected_cell_frame addr src id st st') /\
  (!cx es st res st'. eval_exprs cx es st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      well_typed_exprs env es ==> protected_cell_frame addr src id st st') /\
  (!cx bt st res st'. eval_base_place cx bt st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      IS_SOME (type_place_target env bt) ==> protected_cell_frame addr src id st st') /\
  (!cx bt st res st'. eval_target_place cx bt st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      IS_SOME (type_place_target env bt) ==> protected_cell_frame addr src id st st') /\
  (!cx g v st res st'. assign_tuple_targets cx g v st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      writable_atarget env g ==> protected_cell_frame addr src id st st') /\
  (!cx gs vs st res st'. assign_tuple_target_list cx gs vs st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      EVERY (writable_atarget env) gs ==> protected_cell_frame addr src id st st') /\
  (!cx es st res st'. eval_expr_results cx es st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      well_typed_exprs env es ==> protected_cell_frame addr src id st st')
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED


Theorem checked_protected_cell_frame_mutual:
  (!cx s st res st'. eval_stmt cx s st = (res,st') ==>
    !mods art src id env addr ret. checked_frame_context cx mods art src id env /\
      IS_SOME (type_stmt env ret s) ==> protected_cell_frame addr src id st st') /\
  (!cx ss st res st'. eval_stmts cx ss st = (res,st') ==>
    !mods art src id env addr ret. checked_frame_context cx mods art src id env /\
      IS_SOME (type_stmts env ret ss) ==> protected_cell_frame addr src id st st') /\
  (!cx it st res st'. eval_iterator cx it st = (res,st') ==>
    !mods art src id env addr ty. checked_frame_context cx mods art src id env /\
      well_typed_iterator env ty it ==> protected_cell_frame addr src id st st') /\
  (!cx tyv nm body vs st res st'. eval_for cx tyv nm body vs st = (res,st') ==>
    !mods art src id env addr ret. checked_frame_context cx mods art src id env /\
      IS_SOME (type_stmts env ret body) ==> protected_cell_frame addr src id st st') /\
  (!cx e st res st'. eval_expr cx e st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      well_typed_expr env e ==> protected_cell_frame addr src id st st') /\
  (!cx es st res st'. eval_exprs cx es st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      well_typed_exprs env es ==> protected_cell_frame addr src id st st') /\
  (!cx bt st res st'. eval_base_place cx bt st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      IS_SOME (type_place_target env bt) ==> protected_cell_frame addr src id st st') /\
  (!cx bt st res st'. eval_target_place cx bt st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      IS_SOME (type_place_target env bt) ==> protected_cell_frame addr src id st st') /\
  (!cx g v st res st'. assign_tuple_targets cx g v st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      writable_atarget env g ==> protected_cell_frame addr src id st st') /\
  (!cx gs vs st res st'. assign_tuple_target_list cx gs vs st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      EVERY (writable_atarget env) gs ==> protected_cell_frame addr src id st st') /\
  (!cx es st res st'. eval_expr_results cx es st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      well_typed_exprs env es ==> protected_cell_frame addr src id st st')
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_eval_stmt_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ IS_SOME (type_stmt env ret s) ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_stmt cx s)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_eval_stmts_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ IS_SOME (type_stmts env ret ss) ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_stmts cx ss)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_eval_iterator_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ well_typed_iterator env ty it ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_iterator cx it)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_eval_for_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ IS_SOME (type_stmts env ret ss) ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_for cx tyv nm ss vs)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_eval_expr_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ well_typed_expr env e ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_expr cx e)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_eval_exprs_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ well_typed_exprs env es ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_exprs cx es)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_eval_base_place_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ IS_SOME (type_place_target env bt) ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_base_place cx bt)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_eval_target_place_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ IS_SOME (type_place_target env bt) ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_target_place cx bt)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_assign_tuple_targets_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ writable_atarget env g ==>
  state_rel_frame (protected_cell_frame addr src id) (assign_tuple_targets cx g v)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_assign_tuple_target_list_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ EVERY (writable_atarget env) gs ==>
  state_rel_frame (protected_cell_frame addr src id) (assign_tuple_target_list cx gs vs)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_eval_expr_results_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ well_typed_exprs env es ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_expr_results cx es)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_eval_expr_const_cells_agree:
  eval_expr cx e st = (res,st') /\ const_cells_agree roots st /\
  well_typed_expr env e /\
  (!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
    checked_frame_context cx mods art src id env) ==>
  const_cells_agree roots st'
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_eval_expr_or_place_const_cells_agree:
  eval_expr cx e st = (res,st') /\ const_cells_agree roots st /\
  (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) /\
  (!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
    checked_frame_context cx mods art src id env) ==>
  const_cells_agree roots st'
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_eval_stmts_const_cells_agree:
  eval_stmts cx ss st = (res,st') /\ const_cells_agree roots st /\
  IS_SOME (type_stmts env ret ss) /\
  (!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
    checked_frame_context cx mods art src id env) ==>
  const_cells_agree roots st'
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

(* Selection validates immutable paths, so replay requires agreement on
   their typed root, not just equality of the raw place result. *)
Theorem constant_result_selection_replay:
  const_result_at roots cx ty pv v /\
  const_cells_agree roots st0 /\ const_cells_agree roots st /\
  select_result cx ty pv sb st0 = (res,st0) ==>
  select_result cx ty pv sb st = (res,st)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem constant_result_length_replay:
  constant_result_shape pv /\
  read_result cx pv st0 = (INL v,st0) /\
  read_result cx pv st = (INL v,st) /\
  result_array_length cx pv st0 = (res,st0) ==>
  result_array_length cx pv st = (res,st)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

(* Every root in a replay footprint denotes a checked module constant. *)
Definition constant_roots_provenance_def:
  constant_roots_provenance mods addr roots <=>
    !a src id tv v. MEM (a,src,id,tv,v) roots ==>
      a = addr /\ declared_constant mods src id
End

Theorem constant_roots_provenance_append:
  constant_roots_provenance mods addr (xs ++ ys) <=>
  constant_roots_provenance mods addr xs /\
  constant_roots_provenance mods addr ys
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem constant_expr_replay_aux[local]:
  (!mods imms e v cx am sc artifact current_src.
    constant_value mods imms e = SOME v /\
    check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
    ALOOKUP cx.sources cx.txn.target = SOME mods /\
    constant_machine_immutables am cx.txn.target = imms /\
    deployment_constant_cells_typed (type_env_all_modules mods)
      cx.txn.target mods am /\
    well_typed_expr (artifact_env artifact mods current_src) e /\
    constant_expr mods e /\ no_sha256_expr e ==>
    ?pv roots.
      const_cells_agree roots (initial_state am sc) /\
      constant_roots_provenance mods cx.txn.target roots /\
      const_result_at roots cx (expr_type e) pv v /\
      (!st. const_cells_agree roots st ==>
        eval_expr cx e st = (INL pv,st))) /\
  (!mods imms es vs cx am sc artifact current_src.
    constant_values mods imms es = SOME vs /\
    check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
    ALOOKUP cx.sources cx.txn.target = SOME mods /\
    constant_machine_immutables am cx.txn.target = imms /\
    deployment_constant_cells_typed (type_env_all_modules mods)
      cx.txn.target mods am /\
    well_typed_exprs (artifact_env artifact mods current_src) es /\
    EVERY (constant_expr mods) es /\ EVERY no_sha256_expr es ==>
    ?roots.
      const_cells_agree roots (initial_state am sc) /\
      constant_roots_provenance mods cx.txn.target roots /\
      (!st. const_cells_agree roots st ==>
        eval_exprs cx es st = (INL vs,st)) /\
      LIST_REL (\e v. ?pv. const_result_at roots cx (expr_type e) pv v /\
        (!st. const_cells_agree roots st ==> eval_expr cx e st = (INL pv,st))) es vs)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED



Theorem constant_expr_replay_footprint:
  constant_value mods imms e = SOME v /\
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  constant_machine_immutables am cx.txn.target = imms /\
  deployment_constant_cells_typed (type_env_all_modules mods)
    cx.txn.target mods am /\
  well_typed_expr (artifact_env artifact mods current_src) e /\
  constant_expr mods e /\ no_sha256_expr e ==>
  ?pv roots.
    const_cells_agree roots (initial_state am sc) /\
    constant_roots_provenance mods cx.txn.target roots /\
    const_result_at roots cx (expr_type e) pv v /\
    eval_expr cx e (initial_state am sc) = (INL pv,initial_state am sc) /\
    eval_result_typed (artifact_env artifact mods current_src,cx,initial_state am sc)
      pv (Type (expr_type e)) /\
    read_result cx pv (initial_state am sc) = (INL v,initial_state am sc) /\
    value_runtime_typed (artifact_env artifact mods current_src) (expr_type e) v /\
    constant_result_shape pv /\
    (!st. const_cells_agree roots st ==>
      eval_expr cx e st = (INL pv,st) /\ read_result cx pv st = (INL v,st))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

(* Static typing of the declaration-order replacement environment. *)
Theorem const_subst_literal_forms[local]:
  (int_literal_value e = SOME n ==>
    int_literal_value (subst_consts_expr E e) = SOME n) /\
  (nonneg_int_literal e ==> nonneg_int_literal (subst_consts_expr E e))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_subst_subscript_form[local]:
  expr_type (subst_consts_expr E ix) = expr_type ix /\
  subscript_type_ok ty ix rt ==>
  subscript_type_ok ty (subst_consts_expr E ix) rt
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem subst_consts_constant_expr:
  (!e. !E. constant_expr mods e /\
    (!ty id r. MEM (ty,id) (const_local_refs e) /\ ALOOKUP E id = SOME r ==>
      constant_expr mods r) ==> constant_expr mods (subst_consts_expr E e)) /\
  (!es. !E. EVERY (constant_expr mods) es /\
    (!ty id r. MEM (ty,id) (const_local_exprs es) /\ ALOOKUP E id = SOME r ==>
      constant_expr mods r) ==> EVERY (constant_expr mods) (subst_consts_exprs E es)) /\
  (!fs. !E. EVERY (constant_expr mods) (MAP SND fs) /\
    (!ty id r. MEM (ty,id) (const_local_fields fs) /\ ALOOKUP E id = SOME r ==>
      constant_expr mods r) ==>
    EVERY (constant_expr mods) (MAP SND (subst_consts_fields E fs)))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_subst_builtin_operands[local]:
  (!aty id r. MEM (aty,id) (const_local_exprs es) /\ ALOOKUP E id = SOME r ==>
    constant_expr mods r /\ (!n. int_literal_value r = SOME n ==> 0 <= n)) /\
  MAP expr_type (subst_consts_exprs E es) = MAP expr_type es /\
  well_typed_builtin_app ty bt (MAP expr_type es) /\
  builtin_operands_ok ty bt es ==>
  builtin_operands_ok ty bt (subst_consts_exprs E es)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_subscript_domain_type_ok:
  (well_typed_expr env (Subscript ty a b) \/
   IS_SOME (type_place_expr env (Subscript ty a b))) /\
  (~?kt vt. type_place_expr env a = SOME (HashMapT kt vt)) ==>
  subscript_type_ok (expr_type a) b ty
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_subscript_hashmap_base:
  type_place_expr env (Subscript ty a b) = SOME (HashMapT kt vt) ==>
  ?kt0 vt0. type_place_expr env a = SOME (HashMapT kt0 vt0)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem fold_const_literal_forms[local]:
  (int_literal_value e = SOME n ==>
    int_literal_value (fold_const_expr e) = SOME n) /\
  (nonneg_int_literal e ==> nonneg_int_literal (fold_const_expr e))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem fold_const_subscript_form[local]:
  subscript_type_ok ty ix rt ==>
  subscript_type_ok ty (fold_const_expr ix) rt
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem fold_const_subscript_base_exact[local]:
  !env e. subscript_base_type_exact env e ==>
    subscript_base_type_exact env (fold_const_expr e)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem fold_const_builtin_operands[local]:
  well_typed_builtin_app ty bt (MAP expr_type es) /\
  builtin_operands_ok ty bt es ==>
  builtin_operands_ok ty bt (fold_const_exprs es)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem fold_const_builtin_typed[local]:
  well_typed_expr env (Builtin ty bt es) ==>
  well_typed_expr env (fold_const_builtin ty bt es)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem fold_const_collection_metadata[simp]:
  MAP expr_type (fold_const_exprs es) = MAP expr_type es /\
  LENGTH (fold_const_exprs es) = LENGTH es /\
  MAP FST (fold_const_fields fs) = MAP FST fs /\
  MAP (expr_type o SND) (fold_const_fields fs) = MAP (expr_type o SND) fs
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem fold_const_typing_aux[local]:
  (!e. (!env. well_typed_expr env e ==> well_typed_expr env (fold_const_expr e)) /\
       (!env vt. type_place_expr env e = SOME vt ==>
          type_place_expr env (fold_const_expr e) = SOME vt)) /\
  (!t env vt. type_place_target env t = SOME vt ==>
     type_place_target env (fold_const_btarget t) = SOME vt) /\
  (!es env. well_typed_exprs env es ==>
     well_typed_exprs env (fold_const_exprs es)) /\
  (!d env. well_typed_opt env d ==> well_typed_opt env (fold_const_opt d)) /\
  (!fs env. well_typed_named_exprs env fs ==>
     well_typed_named_exprs env (fold_const_fields fs))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED


Theorem fold_const_expr_typed:
  well_typed_expr env e ==> well_typed_expr env (fold_const_expr e)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem constant_subscript_base_exact[local]:
  constant_expr mods e ==> subscript_base_type_exact env e
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_fragment_subst_typed:
  (!e ty ix. constant_expr mods e /\
    well_typed_expr env (Subscript ty e ix) ==> well_typed_expr env e) ==>
  (!e. constant_expr mods e /\ well_typed_expr env e /\
    (!ty id r. MEM (ty,id) (const_local_refs e) /\ ALOOKUP E id = SOME r ==>
      expr_type r = ty /\ well_typed_expr env r /\ constant_expr mods r /\
      (!n. int_literal_value r = SOME n ==> 0 <= n)) ==>
    well_typed_expr env (subst_consts_expr E e) /\
    expr_type (subst_consts_expr E e) = expr_type e) /\
  (!es. EVERY (constant_expr mods) es /\ well_typed_exprs env es /\
    (!ty id r. MEM (ty,id) (const_local_exprs es) /\ ALOOKUP E id = SOME r ==>
      expr_type r = ty /\ well_typed_expr env r /\ constant_expr mods r /\
      (!n. int_literal_value r = SOME n ==> 0 <= n)) ==>
    well_typed_exprs env (subst_consts_exprs E es) /\
    MAP expr_type (subst_consts_exprs E es) = MAP expr_type es) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) /\ well_typed_named_exprs env fs /\
    (!ty id r. MEM (ty,id) (const_local_fields fs) /\ ALOOKUP E id = SOME r ==>
      expr_type r = ty /\ well_typed_expr env r /\ constant_expr mods r /\
      (!n. int_literal_value r = SOME n ==> 0 <= n)) ==>
    well_typed_named_exprs env (subst_consts_fields E fs) /\
    MAP FST (subst_consts_fields E fs) = MAP FST fs /\
    MAP (expr_type o SND) (subst_consts_fields E fs) = MAP (expr_type o SND) fs)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_const_fragment_subst_typed[local]:
  check_contract mode layouts addr mods = SOME artifact /\
  constant_expr mods e /\ well_typed_expr (artifact_env artifact mods NONE) e /\
  (!ty id r. MEM (ty,id) (const_local_refs e) /\ ALOOKUP E id = SOME r ==>
    expr_type r = ty /\ well_typed_expr (artifact_env artifact mods NONE) r /\
    constant_expr mods r /\ (!n. int_literal_value r = SOME n ==> 0 <= n)) ==>
  well_typed_expr (artifact_env artifact mods NONE) (subst_consts_expr E e) /\
  expr_type (subst_consts_expr E e) = expr_type e
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_const_prefix_subst_typed[local]:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  tops = pre ++ VariableDecl vis (Constant e) id ty slot :: rest /\
  const_prefix_syntax E pre /\
  (!n r. ALOOKUP E n = SOME r ==>
    well_typed_expr (artifact_env artifact mods NONE) r /\ constant_expr mods r /\
    (!i. int_literal_value r = SOME i ==> 0 <= i)) ==>
  well_typed_expr (artifact_env artifact mods NONE) (subst_consts_expr E e) /\
  expr_type (subst_consts_expr E e) = ty
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_subst_literal_nonneg[local]:
  (!n. int_literal_value e = SOME n ==> 0 <= n) /\
  (!ty id r. MEM (ty,id) (const_local_refs e) /\ ALOOKUP E id = SOME r ==>
    !n. int_literal_value r = SOME n ==> 0 <= n) ==>
  !n. int_literal_value (subst_consts_expr E e) = SOME n ==> 0 <= n
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem fold_const_int_literal_origin[local]:
  int_literal_value (fold_const_expr e) = SOME n ==> int_literal_value e = SOME n
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_module_consts_env_typed_acc[local]:
  !ts pre E.
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\ tops = pre ++ ts /\
  const_prefix_syntax E pre /\
  (!vis e id ty slot n. MEM (VariableDecl vis (Constant e) id ty slot) tops /\
    int_literal_value e = SOME n ==> 0 <= n) /\
  (!n r. ALOOKUP E n = SOME r ==>
    well_typed_expr (artifact_env artifact mods NONE) r /\ constant_expr mods r /\
    (!i. int_literal_value r = SOME i ==> 0 <= i)) ==>
  const_prefix_syntax (module_consts_env ts E) tops /\
  (!n r. ALOOKUP (module_consts_env ts E) n = SOME r ==>
    well_typed_expr (artifact_env artifact mods NONE) r /\ constant_expr mods r /\
    (!i. int_literal_value r = SOME i ==> 0 <= i))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_module_consts_env_replacement_typed:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  (!vis e id ty slot n. MEM (VariableDecl vis (Constant e) id ty slot) tops /\
    int_literal_value e = SOME n ==> 0 <= n) /\
  ALOOKUP (module_consts_env tops []) id = SOME r ==>
  well_typed_expr (artifact_env artifact mods NONE) r
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_module_consts_env_syntax_acc[local]:
  !ts pre E.
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\ tops = pre ++ ts /\ const_prefix_syntax E pre ==>
  const_prefix_syntax (module_consts_env ts E) tops
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_module_consts_env_replacement_annotation:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  ALOOKUP (module_consts_env tops []) id = SOME r ==>
  ?vis init ty slot. MEM (VariableDecl vis (Constant init) id ty slot) tops /\
    expr_type r = ty
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_module_consts_env_replacement_replay:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME tops /\
  (!vis e id ty slot n. MEM (VariableDecl vis (Constant e) id ty slot) tops /\
    int_literal_value e = SOME n ==> 0 <= n) /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  ALOOKUP (module_consts_env tops []) id = SOME r /\
  no_sha256_expr r /\
  (!src. IS_SOME src ==>
    get_source_immutables src (constant_machine_immutables am cx.txn.target) =
    get_source_immutables src imms) /\
  (!tv v. FLOOKUP A id = SOME (tv,v) ==>
    FLOOKUP (get_source_immutables NONE
      (constant_machine_immutables am cx.txn.target)) id = SOME (tv,v)) /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am ==>
  ?pv roots.
    const_cells_agree roots (initial_state am sc) /\
    constant_roots_provenance mods cx.txn.target roots /\
    const_results_related roots cx (expr_type r)
      (PlaceR (ImmutablePlace NONE id [])) pv /\
    (!st. const_cells_agree roots st ==> eval_expr cx r st = (INL pv,st))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_results_related_mono:
  (!cell. MEM cell xs ==> MEM cell ys) /\ const_results_related xs cx ty p q ==>
  const_results_related ys cx ty p q
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_replacement_footprints_union:
  !ns.
  (!id r. MEM id ns /\ ALOOKUP E id = SOME r ==>
    ?pv roots. const_cells_agree roots st0 /\
      constant_roots_provenance mods cx.txn.target roots /\
      const_results_related roots cx (expr_type r)
        (PlaceR (ImmutablePlace NONE id [])) pv /\
      (!st. const_cells_agree roots st ==> eval_expr cx r st = (INL pv,st))) ==>
  ?roots. const_cells_agree roots st0 /\
    constant_roots_provenance mods cx.txn.target roots /\
    (!id r. MEM id ns /\ ALOOKUP E id = SOME r ==>
      ?pv. const_results_related roots cx (expr_type r)
        (PlaceR (ImmutablePlace NONE id [])) pv /\
      (!st. const_cells_agree roots st ==> eval_expr cx r st = (INL pv,st)))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_module_consts_env_replay_footprint:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME tops /\
  (!vis e id ty slot n. MEM (VariableDecl vis (Constant e) id ty slot) tops /\
    int_literal_value e = SOME n ==> 0 <= n) /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  (!id r. ALOOKUP (module_consts_env tops []) id = SOME r ==>
    no_sha256_expr r) /\
  (!src. IS_SOME src ==>
    get_source_immutables src (constant_machine_immutables am cx.txn.target) =
    get_source_immutables src imms) /\
  (!id tv v. FLOOKUP A id = SOME (tv,v) ==>
    FLOOKUP (get_source_immutables NONE
      (constant_machine_immutables am cx.txn.target)) id = SOME (tv,v)) /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am ==>
  ?roots. const_cells_agree roots (initial_state am sc) /\
    constant_roots_provenance mods cx.txn.target roots /\
    (!id r. ALOOKUP (module_consts_env tops []) id = SOME r ==>
      ?pv. const_results_related roots cx (expr_type r)
        (PlaceR (ImmutablePlace NONE id [])) pv /\
      (!st. const_cells_agree roots st ==> eval_expr cx r st = (INL pv,st)))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem constant_roots_checked_frame_context:
  constant_roots_provenance mods cx.txn.target roots /\
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\ frame_maps env artifact ==>
  !addr src id tv v. MEM (addr,src,id,tv,v) roots ==>
    addr = cx.txn.target /\ checked_frame_context cx mods artifact src id env
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

(* Congruence boundaries retain delayed results until the interpreter reads them. *)
Theorem const_computations_related_refl:
  (!x. R x x) ==> const_computations_related R f f st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_equal:
  f st = g st /\ (!x. R x x) ==> const_computations_related R f g st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_bind:
  const_computations_related R f g st /\
  (!x y s. f st = (INL x,s) /\ g st = (INL y,s) /\ R x y ==>
    const_computations_related Rel (k x) (l y) s) ==>
  const_computations_related Rel (bind f k) (bind g l) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_read:
  const_results_related roots cx ty p q /\ const_cells_agree roots st ==>
  const_computations_related $= (read_result cx p) (read_result cx q) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_read_results:
  const_result_lists_related roots cx tys ps qs /\ const_cells_agree roots st ==>
  const_computations_related $= (read_results cx ps) (read_results cx qs) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_attribute:
  const_computations_related (const_results_related roots cx ct) f g st /\
  (!p s. f st = (INL p,s) ==> const_cells_agree roots s) /\
  attribute_type (get_tenv cx) ct id = SOME ty ==>
  const_computations_related (const_results_related roots cx ty)
    (bind f (\p. select_result cx ct p (AttrSubscript id)))
    (bind g (\q. select_result cx ct q (AttrSubscript id))) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_length:
  const_computations_related (const_results_related roots cx ct) f g st /\
  (!p s. f st = (INL p,s) ==> const_cells_agree roots s) ==>
  const_computations_related $=
    (bind f (result_array_length cx)) (bind g (result_array_length cx)) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_conditional:
  const_computations_related (const_results_related roots cx ty) f g st /\
  (!p s. f st = (INL p,s) ==> const_cells_agree roots s) ==>
  const_computations_related (const_results_related roots cx ty)
    (bind f (conditional_result cx)) (bind g (conditional_result cx)) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_switch:
  const_results_related roots cx ct p q /\ const_cells_agree roots st /\
  const_computations_related Rel f f' st /\
  const_computations_related Rel g g' st ==>
  const_computations_related Rel (switch_BoolV cx p f g)
    (switch_BoolV cx q f' g') st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_ifexp:
  const_computations_related (const_results_related roots cx ct) c c' st /\
  (!p s. c st = (INL p,s) ==> const_cells_agree roots s) /\
  (!s. const_cells_agree roots s ==>
    const_computations_related (const_results_related roots cx ty) f f' s /\
    const_computations_related (const_results_related roots cx ty) g g' s) /\
  (!p s. bind c (\v. switch_BoolV cx v f g) st = (INL p,s) ==>
    const_cells_agree roots s) ==>
  const_computations_related (const_results_related roots cx ty)
    (bind (bind c (\v. switch_BoolV cx v f g)) (conditional_result cx))
    (bind (bind c' (\v. switch_BoolV cx v f' g')) (conditional_result cx)) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_subscript:
  const_computations_related (const_results_related roots cx ct) bf bf' st /\
  (!p s. bf st = (INL p,s) ==> const_cells_agree roots s) /\
  (!s. const_cells_agree roots s ==>
    const_computations_related (const_results_related roots cx it) idx idx' s) /\
  (!s p t. const_cells_agree roots s /\ idx s = (INL p,t) ==>
    const_cells_agree roots t) /\ subscript_type_ok ct ie ty /\
  (!s p t v. const_cells_agree roots s /\ idx s = (INL p,t) /\
    read_result cx p t = (INL v,t) ==>
    vyperTypeExprResult$subscript_index_matches ct ie v) ==>
  const_computations_related (const_results_related roots cx ty)
    (bind bf (\p. bind idx (\i. bind (read_result cx i)
      (\v. select_result cx ct p (ValueSubscript v)))))
    (bind bf' (\p. bind idx' (\i. bind (read_result cx i)
      (\v. select_result cx ct p (ValueSubscript v))))) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_prefix:
  const_computations_related $= f g st /\
  (!x s. f st = (INL x,s) ==> const_computations_related Rel (k x) (l x) s) ==>
  const_computations_related Rel (bind f k) (bind g l) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_subscript_exact_base:
  bf st = bf' st /\
  (!p s. bf st = (INL p,s) ==> const_cells_agree roots s) /\
  (!s. const_cells_agree roots s ==>
    const_computations_related (const_results_related roots cx it) idx idx' s) /\
  (!s p t. const_cells_agree roots s /\ idx s = (INL p,t) ==>
    const_cells_agree roots t) ==>
  const_computations_related $=
    (bind bf (\p. bind idx (\i. bind (read_result cx i)
      (\v. select_result cx ct p (ValueSubscript v)))))
    (bind bf' (\p. bind idx' (\i. bind (read_result cx i)
      (\v. select_result cx ct p (ValueSubscript v))))) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_delayed_read:
  const_result_lists_related roots cx tys ps qs /\
  const_computations_related $= f g st /\
  (!x s. f st = (INL x,s) ==> const_cells_agree roots s) /\
  (!x. Rel x x) ==>
  const_computations_related Rel
    (bind f (\x. bind (read_results cx ps) (k x)))
    (bind g (\x. bind (read_results cx qs) (k x))) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_arguments:
  const_computations_related (const_result_lists_related roots cx tys) args args' st /\
  (!ps s. args st = (INL ps,s) ==> const_cells_agree roots s) /\
  (!s. const_cells_agree roots s ==> const_computations_related $= suffix suffix' s) /\
  (!s x t. const_cells_agree roots s /\ suffix s = (INL x,t) ==>
    const_cells_agree roots t) /\ (!x. Rel x x) ==>
  const_computations_related Rel
    (bind args (\ps. bind suffix (\x. bind (read_results cx ps) (k x))))
    (bind args' (\ps. bind suffix' (\x. bind (read_results cx ps) (k x)))) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_intcall_defaults_protected_cell_frame:
  checked_frame_context cx mods art src id env /\
  well_typed_expr env (Call ty (IntCall (call_src,fn)) es drv) /\
  get_module_code cx call_src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) ==>
  state_rel_frame (protected_cell_frame addr src id)
    (finally
      (bind (set_scopes [FEMPTY]) (\u.
        eval_exprs (cx with stk updated_by CONS (call_src,fn)) (DROP n dflts)))
      (set_scopes prev))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_intcall_defaults_const_cells_agree:
  well_typed_expr env (Call ty (IntCall (call_src,fn)) es drv) /\
  get_module_code cx call_src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) /\
  (!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
    checked_frame_context cx mods art src id env) /\
  const_cells_agree roots st /\
  finally
    (bind (set_scopes [FEMPTY]) (\u.
      eval_exprs (cx with stk updated_by CONS (call_src,fn)) (DROP n dflts)))
    (set_scopes prev) st = (res,st') ==>
  const_cells_agree roots st'
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_observe_results:
  const_computations_related (const_result_lists_related roots cx tys) f g st /\
  (!ps s. f st = (INL ps,s) ==> const_cells_agree roots s) ==>
  const_computations_related $= (bind f (read_results cx)) (bind g (read_results cx)) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_extcall:
  const_computations_related $= target target' st /\
  (!v s. target st = (INL v,s) ==> const_cells_agree roots s) /\
  (!s. const_cells_agree roots s ==>
    const_computations_related (const_result_lists_related roots cx tys) actuals actuals' s) /\
  (!s ps t. const_cells_agree roots s /\ actuals s = (INL ps,t) ==>
    const_cells_agree roots t) /\
  (!s. const_cells_agree roots s ==> const_computations_related $= kwargs kwargs' s) /\
  (!s kw t. const_cells_agree roots s /\ kwargs s = (INL kw,t) ==>
    const_cells_agree roots t) ==>
  const_computations_related (const_results_related roots cx ty)
    (bind target (\tg. bind actuals (\ps. bind kwargs (\kw.
      bind (read_results cx ps) (\vs. eval_ext_call cx static skip sig opts (tg ++ vs ++ kw))))))
    (bind target' (\tg. bind actuals' (\ps. bind kwargs' (\kw.
      bind (read_results cx ps) (\vs. eval_ext_call cx static skip sig opts (tg ++ vs ++ kw)))))) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_create_blueprint:
  const_computations_related $= prefix prefix' st /\
  (!v s. prefix st = (INL v,s) ==> const_cells_agree roots s) /\
  (!s. const_cells_agree roots s ==>
    const_computations_related (const_result_lists_related roots cx tys) actuals actuals' s) /\
  (!s ps t. const_cells_agree roots s /\ actuals s = (INL ps,t) ==>
    const_cells_agree roots t) ==>
  const_computations_related (const_results_related roots cx ty)
    (bind prefix (\pre. bind (check_create_blueprint salt pre) (\sz.
      bind (bind actuals (read_results cx)) (\vs.
        eval_create cx (CreateFromBlueprint raw_args) salt rof ats (pre ++ vs) (SOME sz)))))
    (bind prefix' (\pre. bind (check_create_blueprint salt pre) (\sz.
      bind (bind actuals' (read_results cx)) (\vs.
        eval_create cx (CreateFromBlueprint raw_args) salt rof ats (pre ++ vs) (SOME sz))))) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_raw_create:
  const_computations_related $= prefix prefix' st /\
  (!v s. prefix st = (INL v,s) ==> const_cells_agree roots s) /\
  (!s. const_cells_agree roots s ==>
    const_computations_related (const_result_lists_related roots cx tys) actuals actuals' s) /\
  (!s ps t. const_cells_agree roots s /\ actuals s = (INL ps,t) ==>
    const_cells_agree roots t) /\
  (!s. const_cells_agree roots s ==> const_computations_related $= salt salt' s) ==>
  const_computations_related (const_results_related roots cx ty)
    (bind prefix (\pre. bind (bind actuals (read_results cx)) (\vs.
      bind salt (\sv. eval_create cx RawCreate has_salt rof ats (pre ++ vs ++ sv) NONE))))
    (bind prefix' (\pre. bind (bind actuals' (read_results cx)) (\vs.
      bind salt' (\sv. eval_create cx RawCreate has_salt rof ats (pre ++ vs ++ sv) NONE)))) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_intcall_arguments:
  const_computations_related (const_result_lists_related roots cx tys)
    (eval_expr_results cx es) actuals' st /\
  (!ps s. eval_expr_results cx es st = (INL ps,s) ==> const_cells_agree roots s) /\
  well_typed_expr env (Call ty (IntCall (call_src,fn)) es drv) /\
  get_module_code cx call_src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) /\
  (!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
    checked_frame_context cx mods art src id env) /\ (!x. Rel x x) ==>
  const_computations_related Rel
    (bind (eval_expr_results cx es) (\ps. bind get_scopes (\prev.
      bind (finally
        (bind (set_scopes [FEMPTY]) (\u.
          eval_exprs (cx with stk updated_by CONS (call_src,fn)) (DROP n dflts)))
        (set_scopes prev)) (\vs. bind (read_results cx ps) (k prev vs)))))
    (bind actuals' (\ps. bind get_scopes (\prev.
      bind (finally
        (bind (set_scopes [FEMPTY]) (\u.
          eval_exprs (cx with stk updated_by CONS (call_src,fn)) (DROP n dflts)))
        (set_scopes prev)) (\vs. bind (read_results cx ps) (k prev vs))))) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_computations_related_intcall_results:
  const_computations_related (const_result_lists_related roots cx tys)
    (eval_expr_results cx es) actuals' st /\
  (!ps s. eval_expr_results cx es st = (INL ps,s) ==> const_cells_agree roots s) /\
  well_typed_expr env (Call ty (IntCall (call_src,fn)) es drv) /\
  get_module_code cx call_src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) /\
  (!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
    checked_frame_context cx mods art src id env) ==>
  const_computations_related (const_results_related roots cx out_ty)
    (bind (eval_expr_results cx es) (\ps. bind get_scopes (\prev.
      bind (finally
        (bind (set_scopes [FEMPTY]) (\u.
          eval_exprs (cx with stk updated_by CONS (call_src,fn)) (DROP n dflts)))
        (set_scopes prev)) (\vs. bind (read_results cx ps) (\vals. k prev vs vals)))))
    (bind actuals' (\ps. bind get_scopes (\prev.
      bind (finally
        (bind (set_scopes [FEMPTY]) (\u.
          eval_exprs (cx with stk updated_by CONS (call_src,fn)) (DROP n dflts)))
        (set_scopes prev)) (\vs. bind (read_results cx ps) (\vals. k prev vs vals))))) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

(* Fixed-footprint inputs for the structural induction.  The collector
   specialization discharges these static maps and pure replay facts. *)
Definition const_subst_context_def:
  const_subst_context roots cx env E mods art <=>
    env.type_defs = get_tenv cx /\
    (!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
      checked_frame_context cx mods art src id env) /\
    (!id r. ALOOKUP E id = SOME r ==>
      FLOOKUP env.bare_globals (NONE,id) = SOME (expr_type r) /\
      FLOOKUP env.toplevel_vtypes (NONE,id) = SOME (Type (expr_type r)) /\
      (!st. const_cells_agree roots st ==>
        lookup_global cx NONE id st = (INL (PlaceR (ImmutablePlace NONE id [])),st)) /\
      ?pv. const_results_related roots cx (expr_type r)
        (PlaceR (ImmutablePlace NONE id [])) pv /\
        (!st. const_cells_agree roots st ==> eval_expr cx r st = (INL pv,st)))
End

Theorem const_subst_typed_annotation:
  const_subst_context roots cx env E mods art /\
  (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
  expr_type (subst_consts_expr E e) = expr_type e
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem subst_consts_exprs_map:
  subst_consts_exprs E es = MAP (subst_consts_expr E) es
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem subst_consts_fields_maps:
  MAP FST (subst_consts_fields E fs) = MAP FST fs /\
  MAP SND (subst_consts_fields E fs) = subst_consts_exprs E (MAP SND fs)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_subst_typed_annotations:
  const_subst_context roots cx env E mods art /\ well_typed_exprs env es ==>
  MAP expr_type (subst_consts_exprs E es) = MAP expr_type es
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_subst_context_expr_frame:
  const_subst_context roots cx env E mods art /\
  (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) /\
  const_cells_agree roots st /\ eval_expr cx e st = (res,st') ==>
  const_cells_agree roots st'
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_subst_context_exprs_frame:
  const_subst_context roots cx env E mods art /\
  well_typed_exprs env es /\ const_cells_agree roots st /\
  eval_exprs cx es st = (res,st') ==> const_cells_agree roots st'
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_subst_context_results_frame:
  const_subst_context roots cx env E mods art /\
  well_typed_exprs env es /\ const_cells_agree roots st /\
  eval_expr_results cx es st = (res,st') ==> const_cells_agree roots st'
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_subst_context_base_frame:
  const_subst_context roots cx env E mods art /\
  IS_SOME (type_place_target env bt) /\ const_cells_agree roots st /\
  eval_base_place cx bt st = (res,st') ==>
  const_cells_agree roots st'
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Definition const_subst_expr_ok_def:
  const_subst_expr_ok roots cx env E e <=>
    (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
    !st. const_cells_agree roots st ==>
      const_computations_related (const_results_related roots cx (expr_type e))
        (eval_expr cx e) (eval_expr cx (subst_consts_expr E e)) st /\
      (!kt vt. type_place_expr env e = SOME (HashMapT kt vt) ==>
        eval_expr cx e st = eval_expr cx (subst_consts_expr E e) st)
End

Definition const_subst_btarget_ok_def:
  const_subst_btarget_ok roots cx env E bt <=>
    IS_SOME (type_place_target env bt) ==>
    !st. const_cells_agree roots st ==>
      eval_base_place cx bt st = eval_base_place cx (subst_consts_btarget E bt) st /\
      eval_target_place cx bt st = eval_target_place cx (subst_consts_btarget E bt) st
End

Definition const_subst_exprs_ok_def:
  const_subst_exprs_ok roots cx env E es <=>
    well_typed_exprs env es ==>
    !st. const_cells_agree roots st ==>
      eval_exprs cx es st = eval_exprs cx (subst_consts_exprs E es) st /\
      const_computations_related (const_result_lists_related roots cx (MAP expr_type es))
        (eval_expr_results cx es) (eval_expr_results cx (subst_consts_exprs E es)) st
End

Theorem const_computations_related_eq:
  const_computations_related $= f g st <=> f st = g st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_result_lists_related_cons:
  const_result_lists_related roots cx (ty::tys) (p::ps) (q::qs) <=>
  const_results_related roots cx ty p q /\
  const_result_lists_related roots cx tys ps qs
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_subst_expr_observe:
  const_subst_context roots cx env E mods art /\
  const_subst_expr_ok roots cx env E e /\ well_typed_expr env e /\
  const_cells_agree roots st ==>
  bind (eval_expr cx e) (read_result cx) st =
  bind (eval_expr cx (subst_consts_expr E e)) (read_result cx) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem const_subst_exprs_from_elements:
  !es. const_subst_context roots cx env E mods art /\
    EVERY (const_subst_expr_ok roots cx env E) es ==>
    const_subst_exprs_ok roots cx env E es
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED





Theorem const_computations_related_ifexp_eval:
  const_computations_related (const_results_related roots cx ct) c c' st /\
  (!p s. c st = (INL p,s) ==> const_cells_agree roots s) /\
  (!s. const_cells_agree roots s ==>
    const_computations_related (const_results_related roots cx ty) f f' s /\
    const_computations_related (const_results_related roots cx ty) g g' s) /\
  (!p s. bind c (\v. switch_BoolV cx v f g) st = (INL p,s) ==>
    const_cells_agree roots s) ==>
  const_computations_related (const_results_related roots cx ty)
    (bind c (\v. bind (switch_BoolV cx v f g) (conditional_result cx)))
    (bind c' (\v. bind (switch_BoolV cx v f' g') (conditional_result cx))) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

(* Instantiate the five mutual predicates from the typed goal. *)
fun const_subst_structural_ind_tac (g as (_,w)) =
  let
    val cs = strip_conj w
    fun predicate c =
      let val (vs,b) = strip_forall c
      in
        if length vs = 2 then list_mk_abs (vs,b)
        else raise Fail "const_subst induction: expected two binders"
      end
    val ps = map predicate cs
    val ith =
      if length ps = 5 then
        BETA_RULE (ISPECL ps subst_consts_expr_ind)
      else raise Fail "const_subst induction: expected five conjuncts"
    val (_,conclusion) = dest_imp (concl ith)
  in
    if aconv conclusion w then MATCH_MP_TAC ith g
    else raise Fail "const_subst induction: specialized conclusion differs"
  end;

Theorem const_subst_structural:
  (!E e. const_subst_context roots cx env E mods art ==>
    const_subst_expr_ok roots cx env E e) /\
  (!E bt. const_subst_context roots cx env E mods art ==>
    const_subst_btarget_ok roots cx env E bt) /\
  (!E es. const_subst_context roots cx env E mods art ==>
    EVERY (const_subst_expr_ok roots cx env E) es) /\
  (!E opt. const_subst_context roots cx env E mods art ==>
    (case opt of NONE => T | SOME e => const_subst_expr_ok roots cx env E e)) /\
  (!E (fs : (string # expr) list). const_subst_context roots cx env E mods art ==>
    EVERY (const_subst_expr_ok roots cx env E) (MAP SND fs))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED


Theorem constant_lookup_footprint:
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  declared_constant mods NONE id /\
  constant_value mods (constant_machine_immutables am cx.txn.target)
    (TopLevelName ty (NONE,id)) = SOME v ==>
  ?roots. const_cells_agree roots (initial_state am sc) /\
    constant_roots_provenance mods cx.txn.target roots /\
    (!st. const_cells_agree roots st ==>
      lookup_global cx NONE id st = (INL (PlaceR (ImmutablePlace NONE id [])),st))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

(* Finite unions retain any observation monotone in the protected cells. *)
Theorem constant_observation_footprints_union:
  !ns. (!id. MEM id ns ==> ?xs.
    const_cells_agree xs st0 /\ constant_roots_provenance mods addr xs /\
    (!st. const_cells_agree xs st ==> P id st)) ==>
  ?roots. const_cells_agree roots st0 /\
    constant_roots_provenance mods addr roots /\
    (!id st. MEM id ns /\ const_cells_agree roots st ==> P id st)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_module_consts_lookup_footprint:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME tops /\
  (!vis e id ty slot n. MEM (VariableDecl vis (Constant e) id ty slot) tops /\
    int_literal_value e = SOME n ==> 0 <= n) /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  (!src. IS_SOME src ==>
    get_source_immutables src (constant_machine_immutables am cx.txn.target) =
    get_source_immutables src imms) /\
  (!id tv v. FLOOKUP A id = SOME (tv,v) ==>
    FLOOKUP (get_source_immutables NONE
      (constant_machine_immutables am cx.txn.target)) id = SOME (tv,v)) /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am ==>
  ?roots. const_cells_agree roots (initial_state am sc) /\
    constant_roots_provenance mods cx.txn.target roots /\
    (!id r st. ALOOKUP (module_consts_env tops []) id = SOME r /\
      const_cells_agree roots st ==>
      lookup_global cx NONE id st = (INL (PlaceR (ImmutablePlace NONE id [])),st))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_module_consts_subst_context:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME tops /\
  (!vis e id ty slot n. MEM (VariableDecl vis (Constant e) id ty slot) tops /\
    int_literal_value e = SOME n ==> 0 <= n) /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  (!id r. ALOOKUP (module_consts_env tops []) id = SOME r ==>
    no_sha256_expr r) /\
  (!src. IS_SOME src ==>
    get_source_immutables src (constant_machine_immutables am cx.txn.target) =
    get_source_immutables src imms) /\
  (!id tv v. FLOOKUP A id = SOME (tv,v) ==>
    FLOOKUP (get_source_immutables NONE
      (constant_machine_immutables am cx.txn.target)) id = SOME (tv,v)) /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am ==>
  ?roots. const_cells_agree roots (initial_state am sc) /\
    const_subst_context roots cx (artifact_env artifact mods current_src)
      (module_consts_env tops []) mods artifact
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem checked_module_consts_substitution:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME tops /\
  (!vis e id ty slot n. MEM (VariableDecl vis (Constant e) id ty slot) tops /\
    int_literal_value e = SOME n ==> 0 <= n) /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  (!id r. ALOOKUP (module_consts_env tops []) id = SOME r ==>
    no_sha256_expr r) /\
  (!src. IS_SOME src ==>
    get_source_immutables src (constant_machine_immutables am cx.txn.target) =
    get_source_immutables src imms) /\
  (!id tv v. FLOOKUP A id = SOME (tv,v) ==>
    FLOOKUP (get_source_immutables NONE
      (constant_machine_immutables am cx.txn.target)) id = SOME (tv,v)) /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
  well_typed_expr (artifact_env artifact mods current_src) e ==>
  bind (eval_expr cx (subst_consts_expr (module_consts_env tops []) e))
    (read_result cx) (initial_state am sc) =
  bind (eval_expr cx e) (read_result cx) (initial_state am sc)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED
