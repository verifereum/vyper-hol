Theory vyperEventRegression
Ancestors vyperCheckContractLibTest vyperEvent vyperInterpreter
Libs vyperCheckContractLib

(* Whole-contract tests, not just compatibility-relation tests. Each case is
   checked in both runtime and deployment mode by the certified conversion. *)
val u256 = ``BaseT (UintT 256)``;
val b20 = ``BaseT (BytesT (Fixed 20))``;
fun event_program fty aty indexed mutability id =
  ``[(NONE,[EventDecl "E" [(("a",^fty),^indexed)];
     FunctionDecl External ^mutability F F "f" [("x",^aty)] [] NoneT
       [Log (^id : num option # string) [Name ^aty "x"]]])]
    : (num option # toplevel list) list``;
fun regression label accept mods = List.app (fn mode =>
  let val layouts = if label = "e87_storage_bytes20" then
        ``[(0w : address, ([((NONE,"v"),0)] : storage_layout, [] : storage_layout))]``
        else ``[] : (address # (storage_layout # storage_layout)) list``
      val th = vyperCheckContractLib.check_contract_conv
        ``check_contract ^mode ^layouts 0w ^mods``
      val result = rhs (concl th)
  in if (optionSyntax.is_some result) = accept then
       print ("EVENT " ^ label ^ " deploy=" ^ term_to_string mode ^
              (if accept then " ACCEPT\n" else " REJECT\n"))
     else raise Fail (label ^ ": unexpected " ^ term_to_string result)
  end) [``F``,``T``];
val eid = ``(NONE,"E") : num option # string``;
val () = List.app (fn (label,fty,aty) =>
  regression label true (event_program fty aty ``F`` ``Nonpayable`` eid))
  [("e02_bytes20",b20,b20),
   ("e24_string",``BaseT (StringT 10)``,``BaseT (StringT 5)``),
   ("widen_dynarray",``ArrayT ^u256 (Dynamic 5)``,``ArrayT ^u256 (Dynamic 3)``),
   ("widen_nested_string",``ArrayT (BaseT (StringT 5)) (Dynamic 2)``,
       ``ArrayT (BaseT (StringT 3)) (Dynamic 2)``),
   ("widen_tuple",``TupleT [^u256; BaseT (BytesT (Dynamic 5))]``,
       ``TupleT [^u256; BaseT (BytesT (Dynamic 3))]``),
   ("widen_fixed_dynamic",``ArrayT (ArrayT ^u256 (Dynamic 5)) (Fixed 2)``,
       ``ArrayT (ArrayT ^u256 (Dynamic 3)) (Fixed 2)``),
   ("e07_nested",``ArrayT (ArrayT ^u256 (Fixed 2)) (Dynamic 2)``,
       ``ArrayT (ArrayT ^u256 (Fixed 2)) (Dynamic 2)``),
   ("e28_dyn_str",``ArrayT (BaseT (StringT 5)) (Dynamic 2)``,
       ``ArrayT (BaseT (StringT 5)) (Dynamic 2)``)];
val () = List.app (fn (label,fty,aty,id) =>
  regression label false (event_program fty aty ``T`` ``Nonpayable`` id))
  [("MISMATCH",u256,``BaseT (BytesT (Dynamic 40))``,eid),
   ("uint8_into_uint256",u256,``BaseT (UintT 8)``,eid),
   ("UNDECLARED",u256,u256,``(NONE,"Nope") : num option # string``),
   ("e62_single_module",u256,u256,``(SOME 0,"Transfer")``),
   ("m14_single_module",u256,u256,``(SOME 0,"Ev")``),
   ("m49_single_module",u256,u256,``(SOME 0,"Approval")``),
   ("e11_indexed_array",``ArrayT ^u256 (Fixed 2)``,
       ``ArrayT ^u256 (Fixed 2)``,eid)];
val () = List.app (fn (label,mut) =>
  regression label false (event_program u256 u256 ``F`` mut eid))
  [("LOG_VIEW",``View``),("LOG_PURE",``Pure``)];

val () = regression "ARITY" false
  ``[(NONE,[EventDecl "E" [(("a",^u256),F); (("b",^u256),F);
                          (("c",^u256),F); (("d",^u256),F)];
     FunctionDecl External Nonpayable F F "f" [("x",^u256)] [] NoneT
       [Log (NONE,"E") [Name ^u256 "x"]]])] : (num option # toplevel list) list``;
val () = regression "DUP_EVENT" false
  ``[(NONE,[EventDecl "E" [(("a",^u256),F)];
     EventDecl "E" [(("b",^u256),T)];
     FunctionDecl External Nonpayable F F "f" [("x",^u256)] [] NoneT
       [Log (NONE,"E") [Name ^u256 "x"]]])] : (num option # toplevel list) list``;
fun mixed_topic_program second_field fourth_indexed =
  ``[(NONE,[EventDecl "E"
       [(("a",BaseT (BytesT (Fixed 32))),T); ((^second_field,BaseT AddressT),T);
        (("c",BaseT (UintT 8)),T); (("d",BaseT BoolT),^fourth_indexed)];
     FunctionDecl External Nonpayable F F "f"
       [("x",BaseT (BytesT (Fixed 32))); ("y",BaseT AddressT);
        ("z",BaseT (UintT 8)); ("w",BaseT BoolT)] [] NoneT
       [Log (NONE,"E") [Name (BaseT (BytesT (Fixed 32))) "x";
         Name (BaseT AddressT) "y"; Name (BaseT (UintT 8)) "z";
         Name (BaseT BoolT) "w"]]])] : (num option # toplevel list) list``;
val () = regression "e10_idx3" true (mixed_topic_program ``"b"`` ``F``);
val () = regression "e87_storage_bytes20" true
  ``[(NONE,[EventDecl "E" [(("a",^b20),T); (("b",^b20),F)];
     VariableDecl Private Storage "v" ^b20 (SOME 0);
     FunctionDecl External Nonpayable F F "f" [] [] NoneT
       [Log (NONE,"E") [TopLevelName ^b20 (NONE,"v");
                         TopLevelName ^b20 (NONE,"v")]]])] : (num option # toplevel list) list``;
val () = regression "e102_flag" true
  ``[(NONE,[FlagDecl "F" ["A";"B"];
     EventDecl "E" [(("a",FlagT (NONE,"F")),T);
                    (("b",FlagT (NONE,"F")),F)];
     FunctionDecl External Nonpayable F F "f" [("x",FlagT (NONE,"F"))] [] NoneT
       [Log (NONE,"E") [Name (FlagT (NONE,"F")) "x";
         FlagMember (FlagT (NONE,"F")) (NONE,"F") "B"]]])]
    : (num option # toplevel list) list``;
val () = regression "e26_interface_decl" true
  ``[(NONE,[InterfaceDecl "I" [("g",[],^u256,View)];
     EventDecl "E" [(("a",BaseT AddressT),F)];
     FunctionDecl External Nonpayable F F "f" [("x",BaseT AddressT)] [] NoneT
       [Log (NONE,"E") [Name (BaseT AddressT) "x"]]])]
    : (num option # toplevel list) list``;
val () = List.app (fn (label,ty) => regression label true
  (event_program ty ty ``T`` ``Nonpayable`` eid))
  [("e26_interface_address",``BaseT AddressT``),
   ("e41_bytes4",``BaseT (BytesT (Fixed 4))``),
   ("e08_string",``BaseT (StringT 10)``),
   ("e09_bytes",``BaseT (BytesT (Dynamic 40))``),
   ("e15_int8",``BaseT (IntT 8)``)];

(* The concrete e02 source encoder has the hash followed by the left-aligned
   value. Keeping the hash symbolic avoids conflating ABI-signature hashing
   with the padding regression. *)
Theorem e02_source_event_topics:
  encode_source_event tenv [(target,[(NONE,
      [EventDecl "E" [(("a",BaseT (BytesT (Fixed 20))),T)]])])]
    target (NONE,"E") [BytesV (1w :: REPLICATE 19 0w)] =
  SOME <| logger := target;
          topics := [n2w (event_hash tenv "E" [BaseT (BytesT (Fixed 20))]);
                     1w << 248]; data := [] |>
Proof
  simp[encode_source_event_def, lookup_event_metadata_def,
       lookup_event_metadata_in_def, encode_vyper_event_metadata_def,
       encode_indexed_event_topics_def, encode_event_topic_bytes20,
       non_indexed_event_args_def, vyperABITheory.vyper_to_abi_def,
       vyperABITheory.vyper_to_abi_type_def,
       contractABITheory.enc_def] >> EVAL_TAC
QED

(* Exercise the actual Log interpreter branch after expression evaluation. *)
Theorem e02_eval_stmt_log:
  cx.sources = [(cx.txn.target,[(NONE,
    [EventDecl "E" [(("a",BaseT (BytesT (Fixed 20))),T)]])])] /\
  eval_exprs cx es st = (INL [BytesV (1w :: REPLICATE 19 0w)], st') ==>
  eval_stmt cx (Log (NONE,"E") es) st =
    if cx.txn.is_static then
      (INR (Error (RuntimeError "write in static context")), st')
    else
      push_log <| logger := cx.txn.target;
        topics := [n2w (event_hash (get_tenv cx) "E" [BaseT (BytesT (Fixed 20))]);
                   1w << 248]; data := [] |> st'
Proof
  strip_tac >> Cases_on `cx.txn.is_static` >>
  simp[Once evaluate_def, e02_source_event_topics,
    vyperStateTheory.bind_def, vyperStateTheory.lift_option_def,
    vyperStateTheory.return_def, vyperStateTheory.ignore_bind_def,
    vyperStateTheory.check_def, vyperStateTheory.assert_def,
    vyperStateTheory.raise_def]
QED

val () = regression "e12_literal_uint8" true
  ``[(NONE,[EventDecl "E" [(("a",BaseT (UintT 8)),F)];
     FunctionDecl External Nonpayable F F "f" [] [] NoneT
       [Log (NONE,"E") [Literal (BaseT (UintT 8)) (IntL 1)]]])]
    : (num option # toplevel list) list``;

Definition e02_name_state_def:
  e02_name_state entry st = st with scopes :=
    [FEMPTY |+ ("x",entry with value := BytesV (1w :: REPLICATE 19 0w))]
End

Theorem e02_name_argument_eval:
  eval_exprs cx [Name (BaseT (BytesT (Fixed 20))) "x"]
    (e02_name_state entry st) =
  (INL [BytesV (1w :: REPLICATE 19 0w)], e02_name_state entry st)
Proof
  simp[Once evaluate_def] >>
  simp[Once evaluate_def, e02_name_state_def,
       vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.get_scopes_def, vyperStateTheory.lookup_scopes_val_def,
       vyperStateTheory.lift_option_type_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[Once evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE,
       vyperStateTheory.read_result_def, vyperStateTheory.read_place_def,
       vyperStateTheory.get_scopes_def, vyperStateTheory.lift_option_type_def,
       vyperStateTheory.lift_sum_def, vyperStateTheory.read_memory_path_def,
       vyperStateTheory.evaluate_subscripts_def]
QED

Theorem e02_eval_stmt_name:
  cx.sources = [(cx.txn.target,[(NONE,
    [EventDecl "E" [(("a",BaseT (BytesT (Fixed 20))),T)]])])] ==>
  eval_stmt cx (Log (NONE,"E") [Name (BaseT (BytesT (Fixed 20))) "x"])
    (e02_name_state entry st) =
  if cx.txn.is_static then
    (INR (Error (RuntimeError "write in static context")), e02_name_state entry st)
  else
  (INL (), (e02_name_state entry st) with logs := st.logs ++
    [<|logger := cx.txn.target;
       topics := [n2w (event_hash (get_tenv cx) "E" [BaseT (BytesT (Fixed 20))]);
                  1w << 248]; data := []|>])
Proof
  strip_tac >> Cases_on `cx.txn.is_static` >>
  mp_tac (e02_eval_stmt_log |> Q.INST
    [`es` |-> `[Name (BaseT (BytesT (Fixed 20))) "x"]`,
     `st` |-> `e02_name_state entry st`, `st'` |-> `e02_name_state entry st`]) >>
  simp[e02_name_argument_eval, vyperStateTheory.push_log_def,
       vyperStateTheory.return_def, e02_name_state_def]
QED
val () = regression "e68_literal_and_bool" true
  ``[(NONE,[EventDecl "E" [(("a",^u256),T); (("b",BaseT BoolT),F)];
     FunctionDecl External Nonpayable F F "f" [("x",^u256)] [] NoneT
       [Log (NONE,"E") [Literal ^u256 (IntL 42);
         Builtin (BaseT BoolT) (Bop Gt) [Name ^u256 "x"; Literal ^u256 (IntL 1)]]]])]
    : (num option # toplevel list) list``;
val () = regression "e20_internal_log" true
  ``[(NONE,[EventDecl "E" [(("a",^u256),F)];
     FunctionDecl Internal Nonpayable F F "g" [("x",^u256)] [] NoneT
       [Log (NONE,"E") [Name ^u256 "x"]];
     FunctionDecl External Nonpayable F F "f" [("x",^u256)] [] NoneT
       [Expr (Call NoneT (IntCall (NONE,"g")) [Name ^u256 "x"] NONE)]])]
    : (num option # toplevel list) list``;
val () = List.app (fn (label,ty,fields) => regression label true
  ``[(NONE,[StructDecl "S" ^fields;
       EventDecl "E" [(("a",^ty),F)];
       FunctionDecl External Nonpayable F F "f" [("x",^ty)] [] NoneT
         [Log (NONE,"E") [Name ^ty "x"]]])]
      : (num option # toplevel list) list``)
  [("e07d_dyn_struct",``ArrayT (StructT (NONE,"S")) (Dynamic 2)``,
     ``[("p",^u256); ("q",^u256)]``),
   ("e49_struct_dyn",``StructT (NONE,"S")``,
     ``[("p",^u256); ("s",BaseT (StringT 5))]``)];

val () = regression "e15_negative_literals" true
  ``[(NONE,[EventDecl "E"
      [(("a",BaseT (IntT 8)),T); (("b",BaseT (IntT 16)),F)];
     FunctionDecl External Nonpayable F F "f" [] [] NoneT
       [Log (NONE,"E") [Literal (BaseT (IntT 8)) (IntL (-3));
         Literal (BaseT (IntT 16)) (IntL (-300))]]])]
    : (num option # toplevel list) list``;
val () = regression "e13_ordered_keywords" true
  ``[(NONE,[EventDecl "E" [(("a",^u256),F); (("b",BaseT AddressT),F)];
     FunctionDecl External Nonpayable F F "f" [("x",^u256)] [] NoneT
       [Log (NONE,"E") [Name ^u256 "x";
         Builtin (BaseT AddressT) (Env Sender) []]]])]
    : (num option # toplevel list) list``;
val () = regression "e50_positional" true
  ``[(NONE,[EventDecl "E" [(("a",^u256),F); (("b",BaseT BoolT),F)];
     FunctionDecl External Nonpayable F F "f" [("x",^u256)] [] NoneT
       [Log (NONE,"E") [Name ^u256 "x";
         Literal (BaseT BoolT) (BoolL T)]]])]
    : (num option # toplevel list) list``;
val () = regression "e41_bytes4_and_bool_topics" true
  ``[(NONE,[EventDecl "E"
      [(("a",BaseT (BytesT (Fixed 4))),T); (("b",BaseT BoolT),T)];
     FunctionDecl External Nonpayable F F "f"
       [("x",BaseT (BytesT (Fixed 4))); ("y",BaseT BoolT)] [] NoneT
       [Log (NONE,"E") [Name (BaseT (BytesT (Fixed 4))) "x";
         Name (BaseT BoolT) "y"]]])]
    : (num option # toplevel list) list``;

(* Literal and empty-value programs remain in the checker domain even when
   their bytecode parity depends on the separate aggregate-lowering fixes. *)
val fixed_array_ty = ``ArrayT ^u256 (Fixed 2)``;
val array_literal = ``Builtin ^fixed_array_ty (MakeArray (SOME ^u256) (Fixed 2))
  [Name ^u256 "x"; Literal ^u256 (IntL 2)]``;
fun array_log_program args body =
  ``[(NONE,[EventDecl "E" [(("a",^fixed_array_ty),F)];
     FunctionDecl External Nonpayable F F "f" ^args [] NoneT ^body])]
    : (num option # toplevel list) list``;
val () = regression "e31_arr_literal" true (array_log_program ``[("x",^u256)]``
  ``[Log (NONE,"E") [^array_literal]]``);
val empty_array = ``TypeBuiltin ^fixed_array_ty Empty ^fixed_array_ty []``;
val () = regression "e57_empty_arr" true (array_log_program ``[] : (string # type) list``
  ``[Log (NONE,"E") [^empty_array]]``);
val dirty_array = ``Builtin ^fixed_array_ty (MakeArray (SOME ^u256) (Fixed 2))
  [Name ^u256 "x"; Name ^u256 "x"]``;
val () = regression "e57b_empty_garbage" true (array_log_program ``[("x",^u256)]``
  ``[Log (NONE,"E") [^dirty_array]; Log (NONE,"E") [^empty_array]]``);
val () = regression "e57c_empty_string" true
  ``[(NONE,[EventDecl "E" [(("a",BaseT (StringT 5)),F)];
     FunctionDecl External Nonpayable F F "f" [("s",BaseT (StringT 5))] [] NoneT
       [Log (NONE,"E") [Name (BaseT (StringT 5)) "s"];
        Log (NONE,"E") [TypeBuiltin (BaseT (StringT 5)) Empty (BaseT (StringT 5)) []]]])]
    : (num option # toplevel list) list``;
val () = regression "e58_struct_lit" true
  ``[(NONE,[StructDecl "S" [("p",^u256); ("q",BaseT BoolT)];
     EventDecl "E" [(("a",StructT (NONE,"S")),F)];
     FunctionDecl External Nonpayable F F "f" [("x",^u256)] [] NoneT
       [Log (NONE,"E") [StructLit (StructT (NONE,"S")) (NONE,"S")
         [("p",Name ^u256 "x"); ("q",Literal (BaseT BoolT) (BoolL T))]]]])]
    : (num option # toplevel list) list``;
val () = regression "e89_empty_ret" true
  ``[(NONE,[FunctionDecl External Nonpayable F F "f" [("x",^u256)] []
      ^fixed_array_ty [AnnAssign "a" ^fixed_array_ty ^dirty_array;
                      Return (SOME ^empty_array)]])]
    : (num option # toplevel list) list``;
