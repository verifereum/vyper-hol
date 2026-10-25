Theory vyperExternalHeadersTest
Ancestors
  vyperTypeContract vyperABIEntries vyperAST vyperContext
  jsonToVyperTopLevel
Libs
  vyperCheckContractLib vyperCheckContractFrontendLib cv_transLib
  jsonASTLib JSONDecode

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../lowering/defs/bytecode/external-entries"]

(* Mutate the real sanitized AST, preserving the frontend's expression types
   and layout, including its global transient lock slot. *)
val uint256 = ``BaseT (UintT 256)``;
val bytes10 = ``BaseT (BytesT (Dynamic 10))``;
val zero = ``Literal ^uint256 (IntL 0)``;
val one = ``Literal ^uint256 (IntL 1)``;
val mutation_ast_path =
  "../lowering/defs/bytecode/external-entries/ast/base_dom1.json";
val mutation_input = vyperCheckContractFrontendLib.prepare_check_input
  {in_deploy = false, address = ``0w : address``,
   annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast mutation_ast_path,
   storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout mutation_ast_path};
val base_dom1 = case #1 (listSyntax.dest_list (#modules mutation_input)) of
    [module] => #2 (pairSyntax.dest_pair module)
  | _ => raise Fail "base_dom1 must contain exactly its main module";
val layouts = #layouts mutation_input;
val base_declarations = #1 (listSyntax.dest_list base_dom1);
fun named_declaration constructor index name =
  case List.filter (fn decl => let val (h,args) = strip_comb decl in
    is_const h andalso #Name (dest_thy_const h) = constructor andalso
    stringSyntax.fromHOLstring (List.nth (args,index)) = name
  end) base_declarations of
    [decl] => decl
  | _ => raise Fail ("missing or ambiguous base declaration: " ^ name);
val stored = named_declaration "VariableDecl" 2 "x";
val guarded = named_declaration "FunctionDecl" 4 "g";
val external_f = named_declaration "FunctionDecl" 4 "f";
val burn = named_declaration "FunctionDecl" 4 "burn";
val cps = named_declaration "FunctionDecl" 4 "cps";
val pure_fn = named_declaration "FunctionDecl" 4 "p";
val fallback = named_declaration "FunctionDecl" 4 "__default__";
val ctor = named_declaration "FunctionDecl" 4 "__init__";
val internal_h = named_declaration "FunctionDecl" 4 "h";
val external_k = named_declaration "FunctionDecl" 4 "k";

(* Change one field of a FunctionDecl without changing its body, or any other
   header field. The caller explicitly names both the declaration and field. *)
fun header field replacement decl = let
  val (constructor, fields) = strip_comb decl
  fun replace_at 0 (_::rest) = replacement::rest
    | replace_at n (tm::rest) = tm::replace_at (n-1) rest
    | replace_at _ [] = raise Fail "invalid FunctionDecl header field"
in
  list_mk_comb (constructor, replace_at field fields)
end;
fun mutate decl field replacement =
  subst [decl |-> header field replacement decl] base_dom1;

fun check_with_layouts layouts label accepts tops in_deploy = let
  val input = vyperCheckContractLib.mk_check_contract
    {in_deploy = in_deploy, layouts = layouts,
     address = ``0w : address``,
     modules = ``[(NONE,^tops)] : (num option # toplevel list) list``}
  val theorem = vyperCheckContractLib.check_contract_conv input
  val result = rhs (concl theorem)
  val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
  val closed = List.null (hyp theorem) andalso List.null axioms andalso
    List.all (fn name => name = "DISK_THM") oracles
  val expected = if accepts then optionSyntax.is_some result
                 else optionSyntax.is_none result
in
  if closed andalso aconv input (lhs (concl theorem)) andalso expected then ()
  else raise Fail (label ^ ": " ^ term_to_string result)
end handle e => raise Fail (label ^ ": " ^ General.exnMessage e);
fun check label accepts tops = check_with_layouts layouts label accepts tops;
fun both label accepts tops =
  List.app (check label accepts tops) [false,true];

val () = both "base_dom1" true base_dom1;
val () = both "selector_collision" false
  (mutate cps 4 ``"collate_propagate_storage"``);
val () = both "dup_ext_name" false (mutate pure_fn 4 ``"f"``);
val () = both "raw_return_nonbytes" false (mutate pure_fn 3 ``T``);
val () = both "raw_return_bytes" true (mutate external_k 3 ``T``);
val () = both "pure_explicit_nonreentrant" false (mutate pure_fn 2 ``T``);
val () = both "fallback_arguments" false
  (mutate fallback 5 ``[("a",^uint256)]``);
val () = both "constructor_value_return" false
  (subst [ctor |-> ``FunctionDecl Deploy Nonpayable F F "__init__"
    [] [] ^uint256 [Return (SOME ^one)]``] base_dom1);
val () = both "constructor_guard_with_lock_layout" true (mutate ctor 2 ``T``);
val () = both "nested_nonreentrant_calls" true (mutate external_f 2 ``T``);
val () = both "internal_raw_return_bytes" true (mutate internal_h 3 ``T``);
val () = both "private_x_function_name" true (mutate burn 4 ``"x"``);
val () = both "internal_external_same_name" true (mutate pure_fn 4 ``"h"``);
val () = both "constructor_view_guard" true
  (subst [ctor |-> ``FunctionDecl Deploy View T F "__init__"
    [] [] NoneT [Pass]``] base_dom1);
val () = both "internal_fallback_name" true
  (subst [internal_h |-> header 4 ``"__default__"`` internal_h,
    external_k |-> ``FunctionDecl External Nonpayable F F "k" [] [] ^bytes10
      [Return (SOME (Call ^bytes10 (IntCall (NONE,"__default__")) [] NONE))]``]
    base_dom1);
val () = both "event_function_same_name" true (mutate burn 4 ``"E1"``);
val () = both "event_storage_same_name" true
  ``EventDecl "x" [] :: ^base_dom1``;
val () = both "argument_named_self" true
  (subst [pure_fn |-> ``FunctionDecl External Pure F F "p"
    [("self",^uint256)] [] ^uint256
    [Return (SOME (Name ^uint256 "self"))]``] base_dom1);
val () = both "local_named_self" true
  (subst [pure_fn |-> ``FunctionDecl External Pure F F "p"
    [] [] ^uint256 [AnnAssign "self" ^uint256 ^one;
      Return (SOME (Name ^uint256 "self"))]``] base_dom1);

(* Record current admission of the branch-local witness that the task's older
   checker rejected. This issue adds no identifier restriction for it. *)
val () = both "nm_dup_local_types" true
  (subst [pure_fn |-> ``FunctionDecl External Nonpayable F F "p"
    [("c",BaseT BoolT)] [] ^uint256
    [If (Name (BaseT BoolT) "c")
       [AnnAssign "y" ^uint256 ^one;
        Return (SOME (Name ^uint256 "y"))]
       [AnnAssign "y" (BaseT BoolT) (Literal (BaseT BoolT) (BoolL T));
        If (Name (BaseT BoolT) "y")
          [Return (SOME (Literal ^uint256 (IntL 5)))] []];
     Return (SOME ^zero)]``] base_dom1);

(* Public getter/function name collision, with the getter declared first. *)
val public_x = subst [stored |-> ``VariableDecl Public Storage "x"
  ^uint256 (SOME 0)``] base_dom1;
val () = both "public_x_function_collision" false
  (subst [burn |-> header 4 ``"x"`` burn] public_x);
val () = both "public_x_baseline" true public_x;

(* A selector collision against a mapping getter must be checked together with
   explicit functions. Both variants have valid storage layouts. *)
val mapping = ``HashMapDecl Public F "cmap" (BaseT (BytesT (Fixed 16)))
  (Type ^uint256) (SOME 1)``;
val mapping_layouts = ``[(0w : address,
  ([((NONE,"x"),0);((NONE,"cmap"),1);
    ((NONE,"collate_propagate_storage"),1)] : storage_layout,
   [((NONE,"$.nonreentrant_key"),0)] : storage_layout))]``;
val () = List.app
  (check_with_layouts mapping_layouts "mapping_getter_baseline" true
    ``^mapping :: ^base_dom1``) [false,true];
val collision_mapping = ``HashMapDecl Public F "collate_propagate_storage"
  (BaseT (BytesT (Fixed 16))) (Type ^uint256) (SOME 1)``;
val () = List.app
  (check_with_layouts mapping_layouts "mapping_getter_selector_collision" false
    ``^collision_mapping :: ^base_dom1``) [false,true];

(* p15x: mutate an otherwise valid uint8 constructor, retaining its body. *)
val ctor8 = ``FunctionDecl Deploy Nonpayable F F "__init__"
  [("a",BaseT (UintT 8))] [] NoneT [Pass]``;
val p03 = subst [ctor |-> ctor8] base_dom1;
val () = both "p03_init_arg_uint8" true p03;
val () = both "p15x_constructor_default" false
  (subst [ctor8 |-> header 6
    ``[Literal (BaseT (UintT 8)) (IntL 5)]`` ctor8] p03);

(* Prefix signatures intentionally repeat the function name. Check both their
   admission and collisions that occur only at an omitted-default prefix. *)
val defaults_f = ``FunctionDecl External Nonpayable F F "f"
  [("a",^uint256);("b",BaseT BoolT);("c",BaseT AddressT)]
  [Literal (BaseT BoolT) (BoolL T);
   TypeBuiltin (BaseT AddressT) Empty (BaseT AddressT) []] NoneT [Pass]``;
val default_tops = subst [external_f |-> defaults_f] base_dom1;
val () = both "default_prefixes" true default_tops;
val duplicate_prefix = ``FunctionDecl External Nonpayable F F
  "collate_propagate_storage" [("a",BaseT (BytesT (Fixed 16)));
    ("b",^uint256)] [^zero] NoneT [Pass]``;
val () = both "omitted_prefix_selector_collision" false
  (subst [cps |-> duplicate_prefix] base_dom1);

(* Typed defaults may observe the actual call state and retain effects. These
   checks must not restore the obsolete runtime-constant admission restriction. *)
val state_default_f = ``FunctionDecl External Nonpayable F F "f"
  [("a",^uint256)] [TopLevelName ^uint256 (NONE,"x")] NoneT [Pass]``;
val () = both "storage_read_default" true
  (subst [external_f |-> state_default_f] base_dom1);
val effectful_h = ``FunctionDecl Internal Nonpayable F F "h" [] [] ^uint256
  [Assign (BaseTarget (TopLevelNameTarget (NONE,"x"))) ^one;
   Return (SOME ^one)]``;
val effectful_f = ``FunctionDecl External Nonpayable F F "f"
  [("a",^uint256)]
  [Call ^uint256 (IntCall (NONE,"h")) [] NONE] NoneT [Pass]``;
val () = both "effectful_internal_call_default" true
  (subst [external_f |-> effectful_f, internal_h |-> effectful_h,
          external_k |-> ``FunctionDecl External Pure F F "k" [] [] NoneT [Pass]``]
    base_dom1);

(* The task's independent pinned-Python AST/layout fixtures and the additional
   explicit-return regressions must also
   survive the actual frontend and both contract-checker modes. Bytecode
   equality is a separate compiler proof obligation. *)
val () = List.app (fn name => List.app (fn in_deploy =>
  ignore (vyperCheckContractFrontendLib.check_contract_file
    {in_deploy = in_deploy, address = ``0w : address``,
     path = "../lowering/defs/bytecode/external-entries/ast/" ^ name ^ ".json"}))
  [false,true])
  ["nr_ext_nonpayable", "nr_multi", "nr_internal", "nr_pragma",
   "dflt_one_lit", "dflt_multi", "dflt_bytes", "dflt_sender",
   "nr_internal_return", "nr_internal_early_return",
   "base_dom1", "nr_ext_payable", "nr_ext_view", "nr_internal_view",
   "nr_default_fn", "nr_early_return", "nr_no_storage", "nr_transient_var",
   "nr_pragma_default", "nr_pragma_init", "nr_pragma_reentrant", "nr_pragma_pure",
   "dflt_only", "dflt_const", "dflt_payable", "dflt_internal_full",
   "c28_const_in_default_arg", "g37_pub_nonreentrancy_pragma", "rr_nr",
   "nr_fallback_early_return", "dflt_balance_after_transfer",
   "dflt_effectful_constant_index"];

Theorem pragma_pure_header:
  effective_decorators T ["external";"pure"] = ["external";"pure"] /\
  effective_decorators T ["external";"view"] =
    ["external";"view";"nonreentrant"] /\
  effective_decorators T ["external";"reentrant"] =
    ["external";"reentrant"]
Proof
  EVAL_TAC
QED

(* A bare source `self` is always translated as the contract address. A
   same-named local/argument cannot redirect that translated expression. *)
Theorem frontend_self_reads_contract_address:
  translate_expr cx (JE_Name "self" tc src ty) =
    Builtin (BaseT AddressT) (Env SelfAddr) []
Proof
  simp[jsonToVyperExprTheory.translate_expr_def]
QED
