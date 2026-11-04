(* Pinned compiler parity: direct immutable read-modify-write is rejected;
   constructor projections are accepted. Exercise the sealed checker too. *)
Theory vyperImmutableMutationTest
Ancestors
  finite_map vyperAST vyperTypeSystem vyperTypeContract
Libs
  vyperCheckContractLib

Definition immutable_mutation_env_def:
  immutable_mutation_env = <|
    current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
    bare_globals := FEMPTY |+ ((NONE,"a"),ArrayT (BaseT BoolT) (Dynamic 2));
    bare_global_assignable := FEMPTY |+ ((NONE,"a"),ArrayT (BaseT BoolT) (Dynamic 2));
    toplevel_vtypes := FEMPTY |+ ((NONE,"a"),Type (ArrayT (BaseT BoolT) (Dynamic 2)));
    type_defs := FEMPTY; fn_sigs := FEMPTY; flag_members := FEMPTY |>
End

Theorem immutable_direct_initialization_accepted:
  type_stmt immutable_mutation_env NoneT
    (Assign (BaseTarget (TopLevelNameTarget (NONE,"a")))
      (TypeBuiltin (ArrayT (BaseT BoolT) (Dynamic 2)) Empty
        (ArrayT (BaseT BoolT) (Dynamic 2)) [])) = SOME immutable_mutation_env
Proof
  EVAL_TAC
QED

Theorem immutable_direct_mutations_rejected:
  ~well_typed_expr immutable_mutation_env
    (Pop (BaseT BoolT) (TopLevelNameTarget (NONE,"a"))) /\
  type_stmt immutable_mutation_env NoneT
    (Append (TopLevelNameTarget (NONE,"a")) (Literal (BaseT BoolT) (BoolL T))) = NONE
Proof
  EVAL_TAC
QED

Theorem immutable_constructor_projection_accepted:
  type_stmt immutable_mutation_env NoneT
    (Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"a"))
      (Literal (BaseT (UintT 256)) (IntL 0))))
      (Literal (BaseT BoolT) (BoolL T))) = SOME immutable_mutation_env
Proof
  EVAL_TAC
QED

Theorem immutable_projection_permission_not_root_inherited:
  target_mutable immutable_mutation_env
    (AttributeTarget (SubscriptTarget (TopLevelNameTarget (NONE,"a")) idx) field_id) /\
  ~target_mutable immutable_mutation_env (TopLevelNameTarget (NONE,"a"))
Proof
  EVAL_TAC
QED

val bool_ty = ``BaseT BoolT``;
val uint_ty = ``BaseT (UintT 256)``;
val array_ty = ``ArrayT ^bool_ty (Dynamic 2)``;
val nested_ty = ``ArrayT ^array_ty (Dynamic 2)``;
val root = ``TopLevelNameTarget (NONE,"a")``;
val index = ``Literal ^uint_ty (IntL 0)``;
val elem = ``Literal ^bool_ty (BoolL T)``;
fun empty ty = ``TypeBuiltin ^ty Empty ^ty []``;
fun initialize ty = ``Assign (BaseTarget ^root) ^(empty ty)``;
fun check mode visibility ty body =
  vyperCheckContractLib.check_contract_conv
    (vyperCheckContractLib.mk_check_contract
      {in_deploy = mode, address = ``0w : address``,
       layouts = ``[] : (address # (storage_layout # storage_layout)) list``,
       modules = ``[(NONE,[VariableDecl Private Immutable "a" ^ty NONE;
         FunctionDecl ^visibility Nonpayable F F "__init__" [] [] NoneT ^body])]
         : (num option # toplevel list) list``});
val checked_count = ref 0;
fun expect label accepted th = let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  val closed = null (Thm.hyp th) andalso null axioms andalso
    List.all (fn s => s = "DISK_THM") oracles
  in
    if closed andalso
       (if accepted then optionSyntax.is_some else optionSyntax.is_none) (rhs (concl th))
    then checked_count := !checked_count + 1
    else raise Fail ("immutable mutation checker: " ^ label)
  end;
fun reject label ty mutation = (
  expect (label ^ " deploy") false
    (check true ``Deploy`` ty ``[^(initialize ty); ^mutation]``);
  expect (label ^ " runtime constructor skipped") true
    (check false ``Deploy`` ty ``[^(initialize ty); ^mutation]``));

val init_checked = check true ``Deploy`` array_ty ``[^(initialize array_ty)]``;
val () = expect "whole immutable initialization" true init_checked;
val _ = save_thm ("immutable_constructor_initialization_checked", init_checked);
val () = reject "pop" array_ty ``Expr (Pop ^bool_ty ^root)``;
val () = reject "ABI pop" array_ty
  ``Expr (TypeBuiltin (BaseT (BytesT (Dynamic 32))) (AbiEncode F NONE)
      (TupleT [^bool_ty]) [Pop ^bool_ty ^root])``;
val () = reject "append" array_ty ``Append ^root ^elem``;
val () = reject "augmented assignment" uint_ty
  ``AugAssign ^uint_ty ^root Add (Literal ^uint_ty (IntL 1))``;
fun accept_projection label ty mutation = (
  expect (label ^ " deploy") true
    (check true ``Deploy`` ty ``[^(initialize ty); ^mutation]``);
  expect (label ^ " runtime constructor skipped") true
    (check false ``Deploy`` ty ``[^(initialize ty); ^mutation]``));
val () = accept_projection "subscript assignment" array_ty
  ``Assign (BaseTarget (SubscriptTarget ^root ^index)) ^elem``;
val () = accept_projection "nested pop" nested_ty
  ``Expr (Pop ^bool_ty (SubscriptTarget ^root ^index))``;
val () = accept_projection "nested ABI pop" nested_ty
  ``Expr (TypeBuiltin (BaseT (BytesT (Dynamic 32))) (AbiEncode F NONE)
      (TupleT [^bool_ty]) [Pop ^bool_ty (SubscriptTarget ^root ^index)])``;
val () = accept_projection "nested append" nested_ty
  ``Append (SubscriptTarget ^root ^index) ^elem``;
val () = accept_projection "nested replacement" nested_ty
  ``Assign (BaseTarget (SubscriptTarget ^root ^index)) ^(empty array_ty)``;
val () = accept_projection "projected augmented assignment"
  ``ArrayT ^uint_ty (Dynamic 2)``
  ``AugAssign ^uint_ty (SubscriptTarget ^root ^index) Add
    (Literal ^uint_ty (IntL 1))``;

val struct_ty = ``StructT (NONE,"Record")``;
val struct_modules = ``[(NONE,[
  StructDecl "Record" [("flag",^bool_ty)];
  VariableDecl Private Immutable "a" ^struct_ty NONE;
  FunctionDecl Deploy Nonpayable F F "__init__" [] [] NoneT
    [^(initialize struct_ty);
     Assign (BaseTarget (AttributeTarget ^root "flag")) ^elem]])]
  : (num option # toplevel list) list``;
val () = expect "immutable attribute assignment in deploy" true
  (vyperCheckContractLib.check_contract_conv
    (vyperCheckContractLib.mk_check_contract
      {in_deploy = true, address = ``0w : address``,
       layouts = ``[] : (address # (storage_layout # storage_layout)) list``,
       modules = struct_modules}));

(* Runtime immutable writes are forbidden even though deploy projections are
   accepted. Check both whole-contract modes, including external bodies while
   constructors are enabled, and internal functions (not constructors). *)
fun runtime_reject label ty mutation =
  List.app (fn mode => List.app (fn vis =>
    expect (label ^ " runtime body") false
      (vyperCheckContractLib.check_contract_conv
        (vyperCheckContractLib.mk_check_contract
          {in_deploy = mode, address = ``0w : address``,
           layouts = ``[] : (address # (storage_layout # storage_layout)) list``,
           modules = ``[(NONE,[VariableDecl Private Immutable "a" ^ty NONE;
             FunctionDecl Deploy Nonpayable F F "__init__" [] [] NoneT
               [^(initialize ty)];
             FunctionDecl ^vis Nonpayable F F "test" [] [] NoneT [^mutation]])]
             : (num option # toplevel list) list``})))
    [``External``, ``Internal``]) [false, true];
val () = runtime_reject "direct replacement" array_ty (initialize array_ty);
val () = runtime_reject "direct augmented assignment" uint_ty
  ``AugAssign ^uint_ty ^root Add (Literal ^uint_ty (IntL 1))``;
val () = runtime_reject "direct pop" array_ty ``Expr (Pop ^bool_ty ^root)``;
val () = runtime_reject "direct append" array_ty ``Append ^root ^elem``;
val () = runtime_reject "subscript assignment" array_ty
  ``Assign (BaseTarget (SubscriptTarget ^root ^index)) ^elem``;
val () = runtime_reject "nested pop" nested_ty
  ``Expr (Pop ^bool_ty (SubscriptTarget ^root ^index))``;
val () = runtime_reject "nested ABI pop" nested_ty
  ``Expr (TypeBuiltin (BaseT (BytesT (Dynamic 32))) (AbiEncode F NONE)
      (TupleT [^bool_ty]) [Pop ^bool_ty (SubscriptTarget ^root ^index)])``;
val () = runtime_reject "nested append" nested_ty
  ``Append (SubscriptTarget ^root ^index) ^elem``;
val () = runtime_reject "nested replacement" nested_ty
  ``Assign (BaseTarget (SubscriptTarget ^root ^index)) ^(empty array_ty)``;
val () = runtime_reject "projected augmented assignment"
  ``ArrayT ^uint_ty (Dynamic 2)``
  ``AugAssign ^uint_ty (SubscriptTarget ^root ^index) Add
    (Literal ^uint_ty (IntL 1))``;

(* Struct fields follow the same projection rule, including ABI operands. *)
val array_record_ty = ``StructT (NONE,"ArrayRecord")``;
val field_target = ``AttributeTarget ^root "items"``;
fun field_check mode vis ty mutation =
  vyperCheckContractLib.check_contract_conv
    (vyperCheckContractLib.mk_check_contract
      {in_deploy = mode, address = ``0w : address``,
       layouts = ``[] : (address # (storage_layout # storage_layout)) list``,
       modules = ``[(NONE,[StructDecl "Record" [("flag",^bool_ty)];
         StructDecl "ArrayRecord" [("items",^array_ty)];
         VariableDecl Private Immutable "a" ^ty NONE;
         FunctionDecl ^vis Nonpayable F F "test" [] [] NoneT
           ^(if aconv vis ``Deploy`` then ``[^(initialize ty); ^mutation]``
             else ``[^mutation]``)])]
         : (num option # toplevel list) list``});
val () = List.app (fn mutation =>
  (expect "immutable array field mutation deploy" true
     (field_check true ``Deploy`` array_record_ty mutation);
   List.app (fn mode => List.app (fn vis =>
     expect "immutable array field mutation runtime" false
       (field_check mode vis array_record_ty mutation))
     [``External``, ``Internal``]) [false, true]))
  [``Expr (Pop ^bool_ty ^field_target)``,
   ``Expr (TypeBuiltin (BaseT (BytesT (Dynamic 32))) (AbiEncode F NONE)
       (TupleT [^bool_ty]) [Pop ^bool_ty ^field_target])``];
val () = List.app (fn mode => List.app (fn vis =>
  expect "immutable field assignment runtime" false
    (field_check mode vis struct_ty
      ``Assign (BaseTarget (AttributeTarget ^root "flag")) ^elem``))
    [``External``, ``Internal``]) [false, true];

(* Mutable locals retain all the same operations. *)
val local_modules = ``[(NONE,[FunctionDecl External Nonpayable F F "test" [] [] NoneT
  [AnnAssign "a" ^array_ty ^(empty array_ty);
   Append (NameTarget "a") ^elem;
   Assign (BaseTarget (SubscriptTarget (NameTarget "a") ^index)) ^elem;
   Expr (Pop ^bool_ty (NameTarget "a"));
   AnnAssign "n" ^uint_ty (Literal ^uint_ty (IntL 0));
   AugAssign ^uint_ty (NameTarget "n") Add (Literal ^uint_ty (IntL 1))]])]
  : (num option # toplevel list) list``;
val () = expect "mutable local controls" true
  (vyperCheckContractLib.check_contract_conv
    (vyperCheckContractLib.mk_check_contract
      {in_deploy = false, address = ``0w : address``,
       layouts = ``[] : (address # (storage_layout # storage_layout)) list``,
       modules = local_modules}));

val storage_modules = ``[(NONE,[
  VariableDecl Private Storage "a" ^array_ty (SOME 0);
  FunctionDecl External Nonpayable F F "test" [] [] NoneT
    [Append ^root ^elem;
     Assign (BaseTarget (SubscriptTarget ^root ^index)) ^elem;
     Expr (Pop ^bool_ty ^root)]])]
  : (num option # toplevel list) list``;
val () = expect "mutable storage controls" true
  (vyperCheckContractLib.check_contract_conv
    (vyperCheckContractLib.mk_check_contract
      {in_deploy = false, address = ``0w : address``,
       layouts = ``[(0w : address, ([((NONE,"a"),0)] : storage_layout,
                    [] : storage_layout))]``,
       modules = storage_modules}));

val mutable_projection_modules = ``[(NONE,[
  StructDecl "Record" [("flag",^bool_ty)];
  FunctionDecl External Nonpayable F F "test" [] [] NoneT
    [AnnAssign "r" ^struct_ty ^(empty struct_ty);
     Assign (BaseTarget (AttributeTarget (NameTarget "r") "flag")) ^elem;
     AnnAssign "a" ^nested_ty ^(empty nested_ty);
     Append (NameTarget "a") ^(empty array_ty);
     Append (SubscriptTarget (NameTarget "a") ^index) ^elem;
     Expr (Pop ^bool_ty (SubscriptTarget (NameTarget "a") ^index));
     Assign (BaseTarget (SubscriptTarget (NameTarget "a") ^index)) ^(empty array_ty)]])]
  : (num option # toplevel list) list``;
val () = expect "mutable struct and nested array projections" true
  (vyperCheckContractLib.check_contract_conv
    (vyperCheckContractLib.mk_check_contract
      {in_deploy = false, address = ``0w : address``,
       layouts = ``[] : (address # (storage_layout # storage_layout)) list``,
       modules = mutable_projection_modules}));

val () = print ("PIN_IMMUTABLE_MUTATION_CHECKER_KERNEL_CLOSED: " ^
  Int.toString (!checked_count) ^ " checks\n");
