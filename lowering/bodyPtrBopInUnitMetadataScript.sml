Theory bodyPtrBopInUnitMetadata
Ancestors
  bodyPtrBopInLocalSuffix bodyPtrBopInSourceFrame supportedProgram
  compileVyper vyperCompiler

(* Closed source/package fixtures cache finite metadata, not runtime semantics. *)
Definition equality_tops_def:
  equality_tops = [FunctionDecl External View F F "probe" [] [] (BaseT BoolT)
    [Return (SOME equality_fixture)]]
End

Theorem equality_tops_supported:
  supported_program equality_tops
Proof
  EVAL_TAC
QED

Theorem equality_policy_accepted:
  lowering_policy_ok probe_policy
Proof
  EVAL_TAC
QED

Theorem equality_classification:
  classify_functions equality_tops =
    ([(View,F,F,"probe",[],[],BaseT BoolT,[Return (SOME equality_fixture)])],
     [],NONE,NONE)
Proof
  simp[equality_tops_def, classify_functions_def, classify_function_def]
QED

Theorem equality_nkeys:
  assign_nkeys equality_tops 0 = K 0
Proof
  EVAL_TAC
QED

(* Keep the cryptographic selector atomic: it is irrelevant to the body EQ.
   Expanding Keccak via EVAL exceeds the fixed per-step budget. *)
Theorem equality_selectors:
  build_selectors (type_env equality_tops)
    [(View,F,F,"probe",[],[],BaseT BoolT,[Return (SOME equality_fixture)])] =
    [compute_selector (type_env equality_tops) "probe" []]
Proof
  simp[build_selectors_def]
QED

Definition equality_external_package_def:
  equality_external_package = package_external_fn equality_tops F (K 0)
    (View,F,F,"probe",[],([]:expr list),BaseT BoolT,[Return (SOME equality_fixture)])
End

Theorem equality_external_package_fields:
  (case equality_external_package of
   (lbl,ce,argv,min_cds,pay,nr,nkey,trans,isview,stmts,rty) =>
   lbl = "fn_probe" /\ argv = [] /\ min_cds = 4 /\
   pay = F /\ nr = F /\ nkey = 0 /\ trans = F /\ isview = T /\
   stmts = [Return (SOME equality_fixture)] /\ rty = SOME (BaseT BoolT))
Proof
  simp[equality_external_package_def, package_external_fn_def,
       build_positional_args_def, min_calldata_size_def]
QED

Theorem equality_external_package_target:
  set_external_package_target probe_policy.rpol_target equality_external_package =
    equality_external_package
Proof
  simp[probe_policy_def, equality_external_package_def]
QED
