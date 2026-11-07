(*
 * Expression simulation: the account reads (#636, Builtins row 6)
 *
 * x.balance, x.codesize, x.codehash, x.is_contract and x.address of an
 * address x.  The lowering (compile_acc) lowers x as an address, then reads
 * the account with BALANCE, EXTCODESIZE, EXTCODEHASH, or EXTCODESIZE and
 * GT 0, or hands out x itself for .address.  The source reads the account
 * at the same address from its accounts, which state_rel's accounts_rel
 * makes Venom's: exprSimUnop's compile_unop_sim with the address operand.
 * The account opcodes are no fresh_write_op, so their code is no
 * straight_fresh action: unop_frag_read_then runs the read by
 * emit_op_frag, then straight-line code on its result.
 *
 * TOP-LEVEL:
 *   compile_acc_read_case  — expr_vv_case of an account read other than
 *                            .code
 *   lower_value_acc        — how an account read lowers
 *   compile_acc_frag       — unop_frag of each read's code
 *   compile_acc_stack      — an account read compiles to a StackValue
 *
 * Helpers: unop_frag_read_then (unop_frag of one account read, then
 *   straight-line code), unop_frag_read (the read alone),
 *   comp_bind_comp_return, address_word_w2w (the account address Venom
 *   reads from the address's word), account_item_type_word.
 *
 * .code is not here: the lowering emits INVALID for it (compile_acc), so
 * the read's simulation does not hold; exprSimBuiltins leaves it cheated.
 * A .code operand is only meant for slice, whose lowering copies the code
 * itself.
 *)

Theory exprSimAccounts
Ancestors
  exprUnopSimDefs exprUnopStraight exprSimUnopCompose
  exprSimUnopProps
  exprSimSource
  exprSimHypsDefs
  loweringPosts
  list rich_list words integer_word byte
  fragExec freshWrites varsExt loweringSlice  exprSimHyps exprSimUnop
  exprSimOperators exprSimWordBuiltins exprBopLowering exprLowering
  emitHelper emitHelperProps compileEnv exprLoweringProps accountsRelProps
  valueEncoding
  valueEncodingProofs venomExecSemantics venomInst venomState venomMemProps
  vyperAST vyperInterpreter vyperContext vyperValue vyperTyping
  vyperTypeSystem vyperTypeInvariants vyperTypeBytesCrypto vfmState
Libs
  pairLib wordsLib

(* ===== The fragment ===== *)

(* The account address Venom reads (w2w of the operand) is the source's
   (word_of_bytes_be of the address's bytes). *)
Theorem address_word_w2w:
  !bs. LENGTH bs = 20 ==>
       (w2w (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) : address) =
       word_of_bytes_be bs
Proof
  cheat
QED

Theorem emit_op_extends_next_var:
  !opc ops sa v sb.
    emit_op opc ops sa = (v, sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  cheat
QED


(* The account reads are no fresh_write_op (they read the accounts), so
   their code is no straight_fresh action: one read by emit_op_frag, then
   straight-line code g on its result. *)
Theorem unop_frag_read_then:
  !ctx func cenv cx opc g w1 r t v w es0.
    opc <> INVOKE /\ ~is_terminator opc /\ is_word_type t /\
    (!c. straight_fresh (g c)) /\
    (!tv. evaluate_type (get_tenv cx) t = SOME tv ==>
          w = typed_val_to_w256 tv v) /\
    (!x ss n out.
       eval_operand x ss = SOME w1 /\ stmt_state_rel ctx func cenv cx es0 ss ==>
       step_inst_base (mk_inst n opc [x] [out]) ss =
         OK (update_var out r ss)) /\
    (!c sa sb op ss.
       g c sa = (op, sb) /\ fresh_vars_wrt sa ss /\
       eval_operand c ss = SOME r ==>
       ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
             eval_operand op ss' = SOME w) ==>
    unop_frag ctx func cenv cx (\x. comp_bind (emit_op opc [x]) g) w1 t
      (INL v) es0
Proof
  cheat
QED

Theorem comp_bind_comp_return:
  !m. comp_bind m comp_return = m
Proof
  cheat
QED

(* unop_frag_read_then with nothing after the read. *)
Theorem unop_frag_read:
  !ctx func cenv cx opc w1 r t v es0.
    opc <> INVOKE /\ ~is_terminator opc /\ is_word_type t /\
    (!tv. evaluate_type (get_tenv cx) t = SOME tv ==>
          r = typed_val_to_w256 tv v) /\
    (!x ss n out.
       eval_operand x ss = SOME w1 /\ stmt_state_rel ctx func cenv cx es0 ss ==>
       step_inst_base (mk_inst n opc [x] [out]) ss =
         OK (update_var out r ss)) ==>
    unop_frag ctx func cenv cx (\x. emit_op opc [x]) w1 t (INL v) es0
Proof
  cheat
QED

(* Each read but .code: its code from the address's word, against the
   source's evaluate_account_op on the account at the address. *)
Theorem compile_acc_frag:
  !ctx func cenv cx item bs es0.
    item <> Code /\ LENGTH bs = 20 /\ accounts_well_typed es0.accounts ==>
    unop_frag ctx func cenv cx
      (\x. case item of
             Balance => emit_op BALANCE [x]
           | Codesize => emit_op EXTCODESIZE [x]
           | Codehash => emit_op EXTCODEHASH [x]
           | IsContract =>
               comp_bind (emit_op EXTCODESIZE [x])
                 (\c. emit_op GT [c; Lit 0w])
           | Address => comp_return x
           | Code => comp_return x)
      (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))
      (account_item_type item)
      (unop_result cx (account_item_type item) (Acc item) [BaseT AddressT]
         (BytesV bs) es0) es0
Proof
  cheat
QED

(* ===== The lowering ===== *)

Theorem lower_value_acc:
  !cenv ty ann item e1 sa op sb.
    lower_value compile_expr cenv ty (Builtin ann (Acc item) [e1]) sa =
      (op, sb) /\ item <> Code ==>
    ?x s1.
      lower_value compile_expr cenv (BaseT AddressT) e1 sa = (x, s1) /\
      (case item of
         Balance => emit_op BALANCE [x]
       | Codesize => emit_op EXTCODESIZE [x]
       | Codehash => emit_op EXTCODEHASH [x]
       | IsContract =>
           comp_bind (emit_op EXTCODESIZE [x]) (\c. emit_op GT [c; Lit 0w])
       | Address => comp_return x
       | Code => comp_return x) s1 = (op, sb)
Proof
  cheat
QED

Theorem names_builtin_acc[local]:
  !item args. ~names_builtin (Acc item) args
Proof
  cheat
QED

Theorem compile_acc_stack:
  !cenv ty ann item args sa.
    ?t op sb. compile_expr cenv ty (Builtin ann (Acc item) args) sa =
              (StackValue t op, sb)
Proof
  cheat
QED

Theorem account_item_type_word:
  !item. item <> Code ==> is_word_type (account_item_type item)
Proof
  cheat
QED

(* ===== The case lemma ===== *)

(* An account read other than .code: compile_unop_sim with the address
   operand lowered as an address, and compile_acc_frag. *)
Theorem compile_acc_read_case:
  !nocalls ctx func cenv cx ann item args.
    item <> Code /\ exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Acc item) args)
Proof
  cheat
QED
