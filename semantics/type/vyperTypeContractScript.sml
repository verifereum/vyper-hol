(*
 * Whole-contract static type checking for Vyper.
 *
 * This theory packages the expression/statement type checker from
 * vyperTypeSystem into a contract-level checker.  The checker constructs the
 * global static maps used by typing environments and checks callable bodies and
 * top-level declarations against the current static rules.
 *
 * Soundness theorems connecting this checker to the proof-facing invariants in
 * prop/vyperTypeInvariants are proved separately.
 *)

Theory vyperTypeContract
Ancestors
  list rich_list arithmetic finite_map option pair pred_set
  vyperAST vyperValue vyperMisc vyperContext vyperState vyperInterpreter
  vyperEvent vyperTypeSystem vyperTypeCallGraph
Libs
  wordsLib

(* ===== Contract typing artifacts ===== *)

Datatype:
  contract_type_artifact = <|
    cta_fn_sigs                  : (nsid |-> fn_sig);
    cta_bare_globals             : (nsid |-> type);
    cta_bare_global_assignable   : (nsid |-> type);
    cta_toplevel_vtypes          : (nsid |-> value_type);
    cta_flag_members             : (nsid |-> string list)
  |>
End

Definition empty_contract_type_artifact_def:
  empty_contract_type_artifact =
    <| cta_fn_sigs := FEMPTY;
       cta_bare_globals := FEMPTY;
       cta_bare_global_assignable := FEMPTY;
       cta_toplevel_vtypes := FEMPTY;
       cta_flag_members := FEMPTY |>
End

Definition artifact_env_def:
  artifact_env art mods src =
    <| current_src := src;
       var_types := FEMPTY;
       var_assignable := FEMPTY;
       bare_globals := art.cta_bare_globals;
       bare_global_assignable := art.cta_bare_global_assignable;
       toplevel_vtypes := art.cta_toplevel_vtypes;
       type_defs := type_env_all_modules mods;
       fn_sigs := art.cta_fn_sigs;
       flag_members := art.cta_flag_members |>
End

Definition function_entry_env_def:
  function_entry_env art mods src args =
    FOLDL (\env (id,ty). extend_local env id ty T)
      (artifact_env art mods src) args
End

(* ===== Static map construction ===== *)

Definition fn_sig_of_def:
  fn_sig_of args dflts ret =
    <| param_types := MAP SND args;
       num_defaults := LENGTH dflts;
       ret_ty := ret |>
End

Definition include_fn_sig_def:
  include_fn_sig in_deploy Internal = T /\
  include_fn_sig in_deploy Deploy = in_deploy /\
  include_fn_sig in_deploy External = F
End

Definition add_toplevel_static_maps_def:
  add_toplevel_static_maps in_deploy src tl art =
    case tl of
    | FunctionDecl vis _ _ _ id args dflts ret _ =>
        if include_fn_sig in_deploy vis then
          art with cta_fn_sigs updated_by
            (flip FUPDATE ((src,id), fn_sig_of args dflts ret))
        else art
    | VariableDecl _ Immutable id typ _ =>
        art with <| cta_bare_globals updated_by
                    (flip FUPDATE ((src,id), typ));
                    cta_bare_global_assignable updated_by
                    (flip FUPDATE ((src,id), typ));
                    cta_toplevel_vtypes updated_by
                    (flip FUPDATE ((src,id), Type typ)) |>
    | VariableDecl _ (Constant e) id typ _ =>
        art with <| cta_bare_globals updated_by
                    (flip FUPDATE ((src,id), typ));
                    cta_toplevel_vtypes updated_by
                    (flip FUPDATE ((src,id), Type typ)) |>
    | VariableDecl _ Storage id typ _ =>
        art with cta_toplevel_vtypes updated_by
          (flip FUPDATE ((src,id), Type typ))
    | VariableDecl _ Transient id typ _ =>
        art with cta_toplevel_vtypes updated_by
          (flip FUPDATE ((src,id), Type typ))
    | HashMapDecl _ _ id kt vt _ =>
        art with cta_toplevel_vtypes updated_by
          (flip FUPDATE ((src,id), HashMapT kt vt))
    | FlagDecl fid members =>
        art with cta_flag_members updated_by
          (flip FUPDATE ((src,fid), members))
    | _ => art
End

Definition add_module_static_maps_def:
  add_module_static_maps in_deploy src tls art =
    FOLDL (\art tl. add_toplevel_static_maps in_deploy src tl art) art tls
End

Definition build_contract_type_artifact_def:
  build_contract_type_artifact in_deploy mods =
    FOLDL (\art (src,tls). add_module_static_maps in_deploy src tls art)
      empty_contract_type_artifact mods
End

(* ===== Namespace/duplicate checks ===== *)

Definition fn_sig_keys_toplevel_def:
  fn_sig_keys_toplevel in_deploy src (FunctionDecl vis _ _ _ id _ _ _ _) =
    (if include_fn_sig in_deploy vis then [(src,id)] else []) /\
  fn_sig_keys_toplevel _ _ _ = []
End

Definition toplevel_vtype_keys_toplevel_def:
  toplevel_vtype_keys_toplevel src (VariableDecl _ _ id _ _) = [(src,id)] /\
  toplevel_vtype_keys_toplevel src (HashMapDecl _ _ id _ _ _) = [(src,id)] /\
  toplevel_vtype_keys_toplevel _ _ = []
End

Definition flag_member_keys_toplevel_def:
  flag_member_keys_toplevel src (FlagDecl fid _) = [(src,fid)] /\
  flag_member_keys_toplevel _ _ = []
End

Definition error_sig_keys_toplevel_def:
  error_sig_keys_toplevel src (ErrorDecl id _) = [(src,id)] /\
  error_sig_keys_toplevel _ _ = []
End

Definition type_def_keys_toplevel_def:
  type_def_keys_toplevel src (StructDecl id _) = [(src,id)] /\
  type_def_keys_toplevel src (FlagDecl id _) = [(src,id)] /\
  type_def_keys_toplevel src (InterfaceDecl id _) = [(src,id)] /\
  type_def_keys_toplevel _ _ = []
End

Definition contract_keys_def:
  contract_keys f mods = FLAT (MAP (\(src,tls). FLAT (MAP (f src) tls)) mods)
End

Definition contract_namespaces_ok_def:
  contract_namespaces_ok in_deploy mods <=>
    ALL_DISTINCT (MAP FST mods) /\
    ALL_DISTINCT (contract_keys (fn_sig_keys_toplevel in_deploy) mods) /\
    ALL_DISTINCT (contract_keys toplevel_vtype_keys_toplevel mods) /\
    ALL_DISTINCT (contract_keys flag_member_keys_toplevel mods) /\
    ALL_DISTINCT (contract_keys error_sig_keys_toplevel mods) /\
    ALL_DISTINCT (contract_keys type_def_keys_toplevel mods)
End

Definition custom_error_resolved_def:
  custom_error_resolved mods (CustomError (src,name) positional kwargs) =
    case ALOOKUP mods src of
    | NONE => F
    | SOME tops =>
        case lookup_custom_error_args_in name tops of
        | NONE => F
        | SOME params =>
            case order_custom_error_args params
                   (CustomError (src,name) positional kwargs) of
            | NONE => F
            | SOME es => MAP expr_type es = MAP SND params
End

Definition custom_errors_stmt_ok_def:
  custom_errors_stmt_ok mods (Raise (RaiseCustomError err)) =
    custom_error_resolved mods err ∧
  custom_errors_stmt_ok mods (Assert e (AssertCustomError err)) =
    custom_error_resolved mods err ∧
  custom_errors_stmt_ok mods (If e yes no) =
    (custom_errors_stmts_ok mods yes ∧ custom_errors_stmts_ok mods no) ∧
  custom_errors_stmt_ok mods (For id ty it n body) =
    custom_errors_stmts_ok mods body ∧
  custom_errors_stmt_ok mods (Raise RaiseBare) = T ∧
  custom_errors_stmt_ok mods (Raise RaiseUnreachable) = T ∧
  custom_errors_stmt_ok mods (Raise (RaiseReason e)) = T ∧
  custom_errors_stmt_ok mods (Assert e AssertBare) = T ∧
  custom_errors_stmt_ok mods (Assert e AssertUnreachable) = T ∧
  custom_errors_stmt_ok mods (Assert e (AssertReason r)) = T ∧
  custom_errors_stmt_ok mods Pass = T ∧
  custom_errors_stmt_ok mods Continue = T ∧
  custom_errors_stmt_ok mods Break = T ∧
  custom_errors_stmt_ok mods (Expr e) = T ∧
  custom_errors_stmt_ok mods (Log id es) = T ∧
  custom_errors_stmt_ok mods (Return eo) = T ∧
  custom_errors_stmt_ok mods (Assign tgt e) = T ∧
  custom_errors_stmt_ok mods (AugAssign ty tgt bop e) = T ∧
  custom_errors_stmt_ok mods (Append tgt e) = T ∧
  custom_errors_stmt_ok mods (AnnAssign id ty e) = T ∧
  custom_errors_stmts_ok mods [] = T ∧
  custom_errors_stmts_ok mods (stmt::rest) =
    (custom_errors_stmt_ok mods stmt ∧ custom_errors_stmts_ok mods rest)
Termination
  WF_REL_TAC `measure (λx.
    case x of INL(_,stmt) => stmt_size stmt
            | INR(_,stmts) => list_size stmt_size stmts)` >> simp[]
End


Definition params_ok_def:
  params_ok tenv args <=>
    ALL_DISTINCT (MAP FST args) /\
    EVERY (\(_,ty). assignable_type tenv ty) args
End

(* ===== Declaration checks ===== *)

(* Vyper accepts constant initializers only from its compile-time-constant
   expression class.  This is deliberately narrower than pure_expr: in
   particular, runtime environment/account reads and all function calls are
   excluded, and top-level reads must name another declared constant. *)
Definition constant_binop_def:
  constant_binop Add = T /\
  constant_binop Sub = T /\
  constant_binop Mul = T /\
  constant_binop Div = T /\
  constant_binop Mod = T /\
  constant_binop Exp = T /\
  constant_binop And = T /\
  constant_binop Or = T /\
  constant_binop XOr = T /\
  constant_binop ShL = T /\
  constant_binop ShR = T /\
  constant_binop In = T /\
  constant_binop NotIn = T /\
  constant_binop Eq = T /\
  constant_binop NotEq = T /\
  constant_binop Lt = T /\
  constant_binop LtE = T /\
  constant_binop Gt = T /\
  constant_binop GtE = T /\
  constant_binop Min = T /\
  constant_binop Max = T /\
  constant_binop _ = F
End

Definition constant_builtin_def:
  constant_builtin Len = T /\
  constant_builtin Not = T /\
  constant_builtin Neg = T /\
  constant_builtin Abs = T /\
  constant_builtin Keccak256 = T /\
  constant_builtin Sha256 = T /\
  constant_builtin (AsWeiValue _) = T /\
  constant_builtin (Uint2Str _) = T /\
  constant_builtin (MakeArray _ _) = T /\
  constant_builtin Ceil = T /\
  constant_builtin Floor = T /\
  constant_builtin AddMod = T /\
  constant_builtin MulMod = T /\
  constant_builtin (Bop op) = constant_binop op /\
  constant_builtin MethodId = T /\
  constant_builtin PowMod256 = T /\
  constant_builtin _ = F
End

Definition constant_type_builtin_def:
  constant_type_builtin Empty = T /\
  constant_type_builtin MaxValue = T /\
  constant_type_builtin MinValue = T /\
  constant_type_builtin Epsilon = T /\
  constant_type_builtin _ = F
End

Definition declared_constant_def:
  declared_constant mods src id <=>
    ?tls vis e ty init.
      MEM (src,tls) mods /\
      MEM (VariableDecl vis (Constant e) id ty init) tls
End

Definition constant_expr_def:
  constant_expr mods (TopLevelName _ (src,id)) = declared_constant mods src id /\
  constant_expr mods (Literal _ _) = T /\
  constant_expr mods (StructLit _ _ kes) =
    EVERY (constant_expr mods) (MAP SND kes) /\
  constant_expr mods (Subscript _ e1 e2) =
    (constant_expr mods e1 /\ constant_expr mods e2) /\
  constant_expr mods (Attribute _ e _) = constant_expr mods e /\
  constant_expr mods (Builtin _ bt es) =
    (constant_builtin bt /\ EVERY (constant_expr mods) es) /\
  constant_expr mods (TypeBuiltin _ tb _ es) =
    (constant_type_builtin tb /\ EVERY (constant_expr mods) es) /\
  constant_expr mods _ = F
Termination
  WF_REL_TAC `measure (\(_,e). expr_size e)` >>
  rw[] >>
  Induct_on `kes` >> rw[] >>
  PairCases_on `h` >> rw[] >>
  res_tac >> simp[]
End

(* ===== Constant folding ===== *)

(* Vyper folds constant initializers at compile time and rejects a contract
   whose initializer fails to evaluate, e.g. `1 // 0` or `max_value(uint256) +
   1`.  The checker mirrors this by running the deployment-time constants fold
   (evaluate_all_constants) without a context or machine.  constant_value
   computes what eval_expr returns on a constant initializer: top-level names
   are read as lookup_global reads them, from the module code in mods and the
   contract's immutables imms, and builtins are evaluated in
   constant_context mods, which fixes only the type environment the constant
   builtins read.  Soundness against eval_expr is proved in
   prop/vyperTypeConstantFold. *)
Definition constant_context_def:
  constant_context mods =
    empty_evaluation_context with
      sources := [(empty_evaluation_context.txn.target, mods)]
End

Definition constant_length_def:
  constant_length (ArrayV (DynArrayV vs)) = SOME (LENGTH vs) /\
  constant_length (ArrayV (SArrayV sparse)) = SOME (LENGTH sparse) /\
  constant_length (ArrayV (TupleV vs)) = SOME (LENGTH vs) /\
  constant_length (BytesV ls) = SOME (LENGTH ls) /\
  constant_length (StringV ls) = SOME (LENGTH ls) /\
  constant_length _ = NONE
End

Definition constant_value_def:
  constant_value mods imms (TopLevelName _ (src,id)) =
    (case ALOOKUP mods src of
     | NONE => NONE
     | SOME ts =>
         if IS_SOME (find_var_decl_by_name id ts) then NONE
         else OPTION_MAP SND (FLOOKUP (get_source_immutables src imms) id)) /\
  constant_value mods imms (Literal _ l) = SOME (evaluate_literal l) /\
  constant_value mods imms (StructLit _ _ kes) =
    OPTION_MAP (\vs. StructV (ZIP (MAP FST kes, vs)))
      (constant_values mods imms (MAP SND kes)) /\
  constant_value mods imms (Subscript _ e1 e2) =
    (case (constant_value mods imms e1, constant_value mods imms e2) of
     | (SOME v1, SOME v2) =>
         (case evaluate_type (type_env_all_modules mods) (expr_type e1) of
          | NONE => NONE
          | SOME arr_tv =>
              case evaluate_subscripts arr_tv v1 [ValueSubscript v2] of
              | INL v => SOME v
              | INR _ => NONE)
     | _ => NONE) /\
  constant_value mods imms (Attribute _ e id) =
    (case constant_value mods imms e of
     | NONE => NONE
     | SOME v =>
         case evaluate_attribute v id of
         | INL v' => SOME v'
         | INR _ => NONE) /\
  constant_value mods imms (Builtin ty bt es) =
    (if ~constant_builtin bt \/ ~builtin_args_length_ok bt (LENGTH es) then NONE
     else
       case constant_values mods imms es of
       | NONE => NONE
       | SOME vs =>
           if bt = Len then
             (case vs of
              | [v] => OPTION_MAP (\n. IntV (&n)) (constant_length v)
              | _ => NONE)
           else if bt = Bop In \/ bt = Bop NotIn then
             (case vs of
              | [v1;v2] =>
                  (case evaluate_type (type_env_all_modules mods)
                           (expr_type (EL 1 es)) of
                   | NONE => NONE
                   | SOME tv =>
                       (case evaluate_membership tv (bt = Bop NotIn) v1 v2 of
                        | INL v => SOME v
                        | INR _ => NONE))
              | _ => NONE)
           else
             case evaluate_builtin (constant_context mods) empty_accounts
                    ty bt (MAP expr_type es) vs of
             | INL v => SOME v
             | INR _ => NONE) /\
  constant_value mods imms (TypeBuiltin _ tb typ es) =
    (if ~constant_type_builtin tb \/
        ~type_builtin_args_length_ok tb (LENGTH es) then NONE
     else
       case constant_values mods imms es of
       | NONE => NONE
       | SOME vs =>
           case evaluate_type_builtin (constant_context mods) tb typ (MAP expr_type es) vs of
           | INL v => SOME v
           | INR _ => NONE) /\
  constant_value mods imms _ = NONE /\
  constant_values mods imms [] = SOME [] /\
  constant_values mods imms (e::es) =
    (case constant_value mods imms e of
     | NONE => NONE
     | SOME v =>
         case constant_values mods imms es of
         | NONE => NONE
         | SOME vs => SOME (v::vs))
Termination
  WF_REL_TAC `measure (\x. case x of
                           | INL (_,_,e) => expr_size e
                           | INR (_,_,es) => list_size expr_size es)` >>
  rw[] >>
  Induct_on `kes` >> rw[] >>
  PairCases_on `h` >> rw[]
End

(* The immutables of the contract's address after merging cenv into module
   src, as merge_constants does on the machine. *)
Definition merge_constant_imms_def:
  merge_constant_imms src cenv imms =
    set_source_immutables src (FUNION cenv (get_source_immutables src imms))
      imms
End

(* constants_env and evaluate_module_constants over the contract's immutables;
   contract_constants_ok applies constants_fold to constants_order mods, as
   evaluate_all_constants does. *)
Definition constants_fold_module_def:
  constants_fold_module mods imms src [] acc = SOME acc /\
  constants_fold_module mods imms src
      (VariableDecl _ (Constant e) id typ _ :: ts) acc =
    (case evaluate_type (type_env_all_modules mods) typ of
     | NONE => NONE
     | SOME tv =>
         case constant_value mods (merge_constant_imms src acc imms) e of
         | NONE => NONE
         | SOME v =>
             constants_fold_module mods imms src ts (acc |+ (id,(tv,v)))) /\
  constants_fold_module mods imms src (_ :: ts) acc =
    constants_fold_module mods imms src ts acc
End

Definition constants_fold_def:
  constants_fold mods imms [] = SOME imms /\
  constants_fold mods imms ((src,ts)::rest) =
    case constants_fold_module mods imms src ts FEMPTY of
    | NONE => NONE
    | SOME cenv =>
        constants_fold mods (merge_constant_imms src cenv imms) rest
End

(* Every constant initializer evaluates, folding in the order the deployment
   fold uses: modules in constants_order (imports first, the main module
   last), declarations in source order, starting from the immutables
   load_contract installs.  A forward reference between constants is
   rejected, as that order cannot evaluate it. *)
Definition contract_constants_ok_def:
  contract_constants_ok mods <=>
    case initial_immutables (type_env_all_modules mods) mods of
    | NONE => F
    | SOME imms => IS_SOME (constants_fold mods imms (constants_order mods))
End

(* Vyper accepts a default argument only from its RUNTIME_CONSTANT class
   (check_modifiability in vyper/semantics/analysis/utils.py, required by
   _parse_args in vyper/semantics/types/function.py).  Folded values arrive as
   literals.  It admits operators (BinOp/Compare/UnaryOp, and BoolOp, which the
   frontend turns into an IfExp with a literal branch), tuple, list and struct
   literals, environment reads other than `self`, account reads of such an
   address, constants, immutables and their subscripts and fields, and
   empty(T).  Storage, transient and HashMap reads, flag members, ternaries and
   all other calls are excluded; for example `self.x`, `self.balance`,
   `len(msg.data)`, `max(block.number, 3)` and
   `block.number if msg.value > 0 else 2` are rejected by Vyper and here. *)
Definition declared_immutable_def:
  declared_immutable mods src id <=>
    ?tls vis ty init.
      MEM (src,tls) mods /\
      MEM (VariableDecl vis Immutable id ty init) tls
End

Definition runtime_constant_builtin_def:
  runtime_constant_builtin Not = T /\
  runtime_constant_builtin Neg = T /\
  runtime_constant_builtin (MakeArray _ _) = T /\
  runtime_constant_builtin (Bop op) =
    (constant_binop op /\ op <> Min /\ op <> Max) /\
  runtime_constant_builtin (Env item) = (item <> SelfAddr) /\
  runtime_constant_builtin (Acc item) = (item <> Code) /\
  runtime_constant_builtin _ = F
End

Definition bool_literal_expr_def:
  bool_literal_expr (Literal _ (BoolL _)) = T /\
  bool_literal_expr _ = F
End

Definition runtime_constant_expr_def:
  runtime_constant_expr mods (TopLevelName _ (src,id)) =
    (declared_constant mods src id \/ declared_immutable mods src id) /\
  runtime_constant_expr mods (Literal _ _) = T /\
  runtime_constant_expr mods (StructLit _ _ kes) =
    EVERY (runtime_constant_expr mods) (MAP SND kes) /\
  runtime_constant_expr mods (Subscript _ e1 e2) =
    (runtime_constant_expr mods e1 /\ runtime_constant_expr mods e2) /\
  runtime_constant_expr mods (Attribute _ e _) = runtime_constant_expr mods e /\
  runtime_constant_expr mods (IfExp _ c a b) =
    ((bool_literal_expr a \/ bool_literal_expr b) /\
     runtime_constant_expr mods c /\ runtime_constant_expr mods a /\
     runtime_constant_expr mods b) /\
  runtime_constant_expr mods (Builtin _ bt es) =
    (runtime_constant_builtin bt /\ EVERY (runtime_constant_expr mods) es) /\
  runtime_constant_expr mods (TypeBuiltin _ tb _ es) =
    (constant_type_builtin tb /\ EVERY (runtime_constant_expr mods) es) /\
  runtime_constant_expr mods _ = F
Termination
  WF_REL_TAC `measure (\(_,e). expr_size e)` >>
  rw[] >>
  Induct_on `kes` >> rw[] >>
  PairCases_on `h` >> rw[] >>
  res_tac >> simp[]
End

Definition lookup_var_slot_in_layouts_def:
  lookup_var_slot_in_layouts layouts addr is_transient src var_name =
    case ALOOKUP layouts addr of
    | NONE => NONE
    | SOME (storage_lay, transient_lay) =>
        ALOOKUP (if is_transient then transient_lay else storage_lay) (src,var_name)
End

(* ===== Allocated storage and live functions ===== *)

(* Vyper allocates storage only for the modules a compilation initializes;
   the layout shows which.  A function is live if its module is allocated,
   or if a live function calls it. *)
Definition toplevel_allocated_def:
  toplevel_allocated layouts addr src (VariableDecl _ Storage id _ _) =
    IS_SOME (lookup_var_slot_in_layouts layouts addr F src id) /\
  toplevel_allocated layouts addr src (VariableDecl _ Transient id _ _) =
    IS_SOME (lookup_var_slot_in_layouts layouts addr T src id) /\
  toplevel_allocated layouts addr src (HashMapDecl _ is_transient id _ _ _) =
    IS_SOME (lookup_var_slot_in_layouts layouts addr is_transient src id) /\
  toplevel_allocated _ _ _ _ = T
End

Definition module_allocated_def:
  module_allocated layouts addr src tls <=>
    EVERY (toplevel_allocated layouts addr src) tls
End

Definition main_module_allocated_def:
  main_module_allocated layouts addr mods <=>
    case ALOOKUP mods NONE of
    | NONE => T
    | SOME tls => module_allocated layouts addr NONE tls
End

(* A storage, transient or HashMap variable with a slot; T for any other
   name. *)
Definition var_allocated_def:
  var_allocated layouts addr mods (src,id) =
    case ALOOKUP mods src of
    | NONE => T
    | SOME tls =>
        case find_var_decl_by_name id tls of
        | NONE => T
        | SOME (StorageVarDecl is_transient _, vid) =>
            IS_SOME (lookup_var_slot_in_layouts layouts addr is_transient src vid)
        | SOME (HashMapVarDecl is_transient _ _, vid) =>
            IS_SOME (lookup_var_slot_in_layouts layouts addr is_transient src vid)
End

Definition toplevel_function_keys_def:
  toplevel_function_keys src (FunctionDecl _ _ _ _ fn _ _ _ _) = [(src,fn)] /\
  toplevel_function_keys _ _ = []
End

Definition live_roots_def:
  live_roots layouts addr mods =
    FLAT (MAP (\(src,tls).
                 if module_allocated layouts addr src tls
                 then FLAT (MAP (toplevel_function_keys src) tls) else [])
              mods)
End

(* Worklist closure of todo under the call edges.  Each step consumes one
   item, and only a newly seen node adds items (its out-edges), so
   LENGTH todo + LENGTH edges steps reach the fixpoint. *)
Definition call_closure_def:
  call_closure edges 0 seen todo = seen /\
  call_closure edges (SUC n) seen [] = seen /\
  call_closure edges (SUC n) seen (k::todo) =
    if MEM k seen then call_closure edges n seen todo
    else call_closure edges n (k::seen) (direct_callees edges k ++ todo)
End

Definition live_functions_def:
  live_functions layouts addr mods =
    let edges = contract_call_edges mods in
    let roots = live_roots layouts addr mods in
      call_closure edges (LENGTH roots + LENGTH edges) [] roots
End

(* live is live_functions layouts addr mods, computed once.  Soundness needs
   no fact about it: a function in an allocated module is live by the first
   disjunct, and a checked body can only call a function in fn_sigs. *)
Definition function_live_def:
  function_live layouts addr mods live (src,fn) <=>
    (case ALOOKUP mods src of
     | NONE => F
     | SOME tls => module_allocated layouts addr src tls) \/
    MEM (src,fn) live
End

Definition context_function_live_def:
  context_function_live cx k <=>
    case ALOOKUP cx.sources cx.txn.target of
    | NONE => F
    | SOME mods =>
        function_live cx.layouts cx.txn.target mods
          (live_functions cx.layouts cx.txn.target mods) k
End

Definition live_artifact_def:
  live_artifact layouts addr mods live art =
    art with <| cta_fn_sigs :=
                  DRESTRICT art.cta_fn_sigs (function_live layouts addr mods live);
                cta_toplevel_vtypes :=
                  DRESTRICT art.cta_toplevel_vtypes (var_allocated layouts addr mods) |>
End

Theorem live_artifact_fields[simp]:
  (live_artifact layouts addr mods live art).cta_fn_sigs =
    DRESTRICT art.cta_fn_sigs (function_live layouts addr mods live) /\
  (live_artifact layouts addr mods live art).cta_toplevel_vtypes =
    DRESTRICT art.cta_toplevel_vtypes (var_allocated layouts addr mods) /\
  (live_artifact layouts addr mods live art).cta_bare_globals =
    art.cta_bare_globals /\
  (live_artifact layouts addr mods live art).cta_bare_global_assignable =
    art.cta_bare_global_assignable /\
  (live_artifact layouts addr mods live art).cta_flag_members =
    art.cta_flag_members
Proof
  simp[live_artifact_def]
QED

(* Membership in the two restriction sets, for evaluation. *)
Theorem IN_function_live[simp]:
  k IN function_live layouts addr mods live <=>
  function_live layouts addr mods live k
Proof
  simp[IN_DEF]
QED

Theorem IN_var_allocated[simp]:
  k IN var_allocated layouts addr mods <=> var_allocated layouts addr mods k
Proof
  simp[IN_DEF]
QED

Definition check_value_type_def:
  check_value_type tenv (Type ty) = assignable_type tenv ty /\
  check_value_type tenv (HashMapT kt vt) =
    (well_formed_type tenv kt /\ hashmap_key_type kt /\ check_value_type tenv vt)
Termination
  WF_REL_TAC `measure (\(_,vt). value_type_size vt)` >>
  simp[value_type_size_def]
End

Definition check_toplevel_decl_def:
  check_toplevel_decl mods art src tl =
    let tenv = type_env_all_modules mods in
    let env = artifact_env art mods src in
    case tl of
    | VariableDecl _ Storage id typ _ =>
        assignable_type tenv typ
    | VariableDecl _ Transient id typ _ =>
        assignable_type tenv typ
    | VariableDecl _ Immutable id typ _ =>
        assignable_type tenv typ
    | VariableDecl _ (Constant e) id typ _ =>
        assignable_type tenv typ /\ well_typed_expr env e /\ expr_type e = typ /\
        constant_expr mods e
    | HashMapDecl _ is_transient id kt vt _ =>
        well_formed_type tenv kt /\ hashmap_key_type kt /\ check_value_type tenv vt
    | StructDecl id fields =>
        ALL_DISTINCT (MAP FST fields) /\
        EVERY (\(_,ty). assignable_type tenv ty) fields
    | FlagDecl id members => T
    | InterfaceDecl id funcs =>
        EVERY (\(fn,args,ret,mut).
          params_ok tenv args /\ well_formed_type tenv ret) funcs
    | EventDecl id fields =>
        EVERY (\((_,ty),indexed). assignable_type tenv ty) fields
    | ErrorDecl id args => params_ok tenv args
    | FunctionDecl vis _ _ _ _ args dflts ret _ =>
        params_ok tenv args /\ well_formed_type tenv ret /\
        (* Vyper: "Constructor may not use default arguments" *)
        (vis = Deploy ==> dflts = [])
End

(* ===== Callable-body checks ===== *)

Definition check_function_body_def:
  check_function_body layouts addr mods art src mut nr args dflts ret body =
    let tenv = type_env_all_modules mods in
    let env = function_entry_env art mods src args in
      params_ok tenv args /\
      (nr ==> IS_SOME (lookup_nonreentrant_slot layouts addr)) /\
      IS_SOME (evaluate_type tenv ret) /\
      IS_SOME (type_stmts env ret body) /\
      custom_errors_stmts_ok mods body /\
      (ret = NoneT \/ stmts_no_fallthrough body) /\
      stmts_no_control_escape body /\
      well_typed_exprs (defaults_env env) dflts /\
      EVERY (runtime_constant_expr mods) dflts /\
      MAP expr_type dflts = MAP SND (DROP (LENGTH args - LENGTH dflts) args)
End

Definition check_function_body_in_mode_def:
  check_function_body_in_mode in_deploy vis <=>
    vis <> Deploy \/ in_deploy
End

Definition check_toplevel_body_def:
  check_toplevel_body in_deploy layouts addr mods live art src tl =
    case tl of
    | FunctionDecl vis mut nr _ fn args dflts ret body =>
        function_live layouts addr mods live (src,fn) /\
        check_function_body_in_mode in_deploy vis ==>
        check_function_body layouts addr mods art src mut nr args dflts ret body
    | _ => T
End

Definition check_module_def:
  check_module in_deploy layouts addr mods live art (src,tls) =
    (EVERY (check_toplevel_decl mods art src) tls /\
     EVERY (check_toplevel_body in_deploy layouts addr mods live art src) tls)
End

(* Only live functions are checked, and the typing environment holds only the
   live functions and the storage variables that have a slot.  So a checked
   body that reads a variable without a slot, or calls a function that isn't
   checked, is ill-typed.  The main module must be allocated, so every
   function of it is checked.

   Vyper type-checks every function body (analyze_functions in
   vyper/semantics/analysis/local.py).  Here a function of an uninitialized
   module that no live function calls is not checked at all, so such dead
   code is accepted even when Vyper would reject it.

   Two more differences from Vyper.  A live function may read an immutable
   of an uninitialized module, which Vyper rejects without `uses:`; its
   value is the default.  And exports_ok rejects exporting any function of
   an uninitialized module, while Vyper accepts exporting one that uses no
   state. *)
Definition check_contract_def:
  check_contract in_deploy layouts addr mods =
    let live = live_functions layouts addr mods in
    let art = live_artifact layouts addr mods live
                (build_contract_type_artifact in_deploy mods) in
      if contract_namespaces_ok in_deploy mods /\
         contract_call_graph_acyclic mods /\
         main_module_allocated layouts addr mods /\
         EVERY (check_module in_deploy layouts addr mods live art) mods /\
         contract_constants_ok mods
      then SOME art else NONE
End

(* The exports map of load_contract names only functions of allocated
   modules.  An external function is never an internal callee, so it is live
   exactly when its module is allocated. *)
Definition exports_ok_def:
  exports_ok layouts addr mods exps <=>
    EVERY (\(fn,src).
             case ALOOKUP mods (SOME src) of
             | NONE => T
             | SOME tls => module_allocated layouts addr (SOME src) tls) exps
End

(* TOP-LEVEL: Successful checking guarantees distinct member names for every
   actual struct declaration, including declarations in imported modules. *)
Theorem check_contract_struct_fields_distinct:
  check_contract in_deploy layouts addr mods = SOME art /\
  MEM (src,tls) mods /\
  MEM (StructDecl id fields) tls ==>
  ALL_DISTINCT (MAP FST fields)
Proof
  strip_tac >>
  qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
  simp[check_contract_def, EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!x. MEM x mods ==> check_module _ _ _ _ _ _ x` drule >>
  simp[check_module_def, EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!x. MEM x tls ==> check_toplevel_decl _ _ _ x` drule >>
  simp[check_toplevel_decl_def]
QED
