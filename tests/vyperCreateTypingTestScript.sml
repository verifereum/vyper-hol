(* Create typing regression: exercise the production checker conversion. *)
Theory vyperCreateTypingTest
Ancestors
  vyperTypeContract
Libs
  vyperCheckContractLib

val value = ``Literal (BaseT (UintT 256)) (IntL 0)``;
val salt = rhs (concl (EVAL
  ``Literal (BaseT (BytesT (Fixed 32))) (BytesL (REPLICATE 32 0w))``));
val target = rhs (concl (EVAL
  ``Literal (BaseT AddressT) (BytesL (REPLICATE 20 0w))``));

fun check_create label accepted kind has_salt payload_ty args =
  List.app (fn in_deploy => let
    val expression = ``Call (BaseT AddressT)
      (CreateTarget ^kind ^has_salt T) ^args NONE``
    val result = vyperCheckContractLib.check_contract_conv
      (vyperCheckContractLib.mk_check_contract
        {in_deploy = in_deploy, address = ``0w : address``,
         layouts = ``[] : (address # (storage_layout # storage_layout)) list``,
         modules = ``[(NONE, [FunctionDecl External Nonpayable F F "create"
           [("payload", ^payload_ty)] [] (BaseT AddressT)
           [Return (SOME ^expression)]])] : (num option # toplevel list) list``})
    val answer = rhs (concl result)
  in
    if (if accepted then optionSyntax.is_some answer
        else optionSyntax.is_none answer) then ()
    else raise Fail ("create checker regression: " ^ label)
  end) [false, true];

fun raw_case label accepted ty salted ctor_args = let
  val payload = ``Name ^ty "payload"``
  val has_salt = if salted then ``T`` else ``F``
  val suffix = if salted then [salt] else []
  val args = listSyntax.mk_list (payload :: value :: ctor_args @ suffix,
                               type_of value)
in check_create label accepted ``RawCreate`` has_salt ty args end;

val () = List.app (fn salted => (
  raw_case "fixed bytecode" false ``BaseT (BytesT (Fixed 32))`` salted [];
  raw_case "below cap" true ``BaseT (BytesT (Dynamic 49151))`` salted [];
  raw_case "at cap" true ``BaseT (BytesT (Dynamic 49152))`` salted [];
  raw_case "above cap" false ``BaseT (BytesT (Dynamic 49153))`` salted [];
  raw_case "ABI fixed constructor tail" true
    ``BaseT (BytesT (Dynamic 32))`` salted [salt])) [false, true];

fun blueprint_case label accepted raw_args ty salted = let
  val payload = ``Name ^ty "payload"``
  val has_salt = if salted then ``T`` else ``F``
  val prefix = if salted then [target, value, salt, value]
               else [target, value, value]
  val args = listSyntax.mk_list (prefix @ [payload], type_of value)
in check_create label accepted ``CreateFromBlueprint ^raw_args`` has_salt ty args end;

val () = List.app (fn salted => (
  blueprint_case "raw blueprint fixed" false ``T``
    ``BaseT (BytesT (Fixed 32))`` salted;
  blueprint_case "raw blueprint dynamic" true ``T``
    ``BaseT (BytesT (Dynamic 32))`` salted;
  blueprint_case "raw blueprint uncapped" true ``T``
    ``BaseT (BytesT (Dynamic 49153))`` salted;
  blueprint_case "ordinary ABI fixed" true ``F``
    ``BaseT (BytesT (Fixed 32))`` salted)) [false, true];

(* Zero capacity is permitted by the operand predicate, independently of
   any declared-type policy. *)
val () = List.app (fn (tm, expected) =>
  if aconv (rhs (concl (simpLib.SIMP_CONV (srw_ss())
       [vyperTypeSystemTheory.create_arg_types_ok_compute] tm))) expected
  then () else raise Fail "create compute boundary regression")
  [(``create_arg_types_ok RawCreate F
       [BaseT (BytesT (Dynamic 0)); BaseT (UintT 256)]``, ``T``),
   (``create_arg_types_ok RawCreate T
       [BaseT (BytesT (Dynamic 0)); BaseT (UintT 256);
        BaseT (BytesT (Fixed 32))]``, ``T``)];
