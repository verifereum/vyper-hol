(*
 * Statement simulation: an augmented assignment to a word field of a local
 * struct (#637)
 *
 * x.f op= e for a local x of struct type held through its pointer p and f
 * a field of a word_value_type.  The source takes the place x.f, reads
 * x.f's value, evaluates e, runs the operator on the two and writes the
 * result at x.f.  The lowering adds f's byte offset to p (dst), loads dst,
 * lowers e at f's type, runs compile_binop and stores the result at dst.
 *
 * x.f op e is no expression whose lowering this is: dst is computed before
 * e's code and used again after the operator's, so it has to survive both.
 * The pieces therefore run one after the other, each from the state the
 * previous one leaves (augassign_attr_bop_frag): the ADD and the MLOAD,
 * then e's expr_sim and the operator's binop_frag, which keep every
 * variable defined before them, dst among them.  The part after the load
 * is augassign_load_bop_frag, for any load fragment, which
 * stmtSimAugAssignAttrStorage reuses with SLOAD/TLOAD.
 *
 * TOP-LEVEL:
 *   compile_augassign_attr_local_case — x.f op= e, every outcome, e's
 *                                      simulation a premise
 *   compile_augassign_attr_local_stmt_frag — the same for an e with no
 *                                      internal call
 *   augassign_attr_local_place       — x.f's place, value and type are read
 *                                      where expr_sim_inv holds
 *
 * Helpers: struct_has_type_field, eval_augassign_attr_local,
 *   augassign_attr_local_code_parts, stmt_state_rel_field_word,
 *   attr_load_frag, augassign_load_bop_frag, augassign_attr_bop_frag,
 *   write_attr_local_typed,
 *   augassign_attr_local_frag
 *)

Theory stmtSimAugAssignAttr
Ancestors
  exprBopSimDefs exprBopSimProps
  exprSimFieldLayout
  exprSimSource
  stmtSimProps
  exprSimProps
  exprSimHypsDefs
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set alist
  fragExec freshWrites loweringSlice  exprSimHyps exprSimOps
  exprSimBinopFrag exprSimOperators exprSimLeaves exprSimBuffer
  exprSimAttributeFields
   stmtSimDecl stmtSimDeclMem stmtSimDeclStore stmtSimAssign
  stmtSimAugAssign stmtSimAssignAttr
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding valueEncodingProps
  vyperInterpreter vyperState vyperValue vyperValueOperation vyperTyping
  vyperTypeEnv vyperTypeInvariants vyperTypeExprSoundness vyperTypeSystem
  vyperAST
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* ===== The source ===== *)

(* A struct value of its type has every field its type lists, at that
   field's type. *)
Theorem struct_has_type_field:
  !fs vals id ftv.
    struct_has_type fs vals /\ ALOOKUP fs id = SOME ftv ==>
    ?fv. ALOOKUP vals id = SOME fv /\ value_has_type ftv fv
Proof
  cheat
QED

(* x.f op= e, unless it fails with a type error: x.f's value fv is read
   and e evaluated, then the operator runs on the two, and its result is
   written at x.f. *)
Theorem eval_augassign_attr_local:
  !cx ty id fld bop e es res es' entry fs vals ftv fv.
    eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)
      es = (res, es') /\
    lookup_scopes id es.scopes = SOME entry /\
    entry.type = StructTV fs /\ entry.value = StructV vals /\
    ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
    (!m. res <> INR (Error (TypeError m))) ==>
    ?r1 es1.
      (do tv <- eval_expr cx e; read_result cx tv od) es = (r1, es1) /\
      case r1 of
        INR ex => res = INR ex /\ es' = es1
      | INL v =>
          case evaluate_binop
                 (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
                 ftv bop fv v of
            INR err => res = INR (Error err) /\ es' = es1
          | INL r =>
              write_place cx (MemoryPlace id [AttrSubscript fld]) r es1 =
                (res, es')
Proof
  cheat
QED

(* ===== The code ===== *)

(* x.f op= e on a local x held through its pointer p: the ADD of f's byte
   offset to p, an MLOAD of the sum, e lowered at the field's type, the
   operator and an MSTORE at the sum. *)
Theorem augassign_attr_local_code_parts:
  !cenv lctx ty0 ty id fld bop e sa c sf p sz sid.
    stmt_env cenv lctx ty0
      (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) sa =
      (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME (StructT sid) ==>
    c = cenv /\
    ?dst sn cur s1 rhs s2 res_op s3.
      emit_op ADD
        [Var p; Lit (n2w (struct_field_offset
           (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
           fld))] sa = (dst, sn) /\
      emit_op MLOAD [dst] sn = (cur, s1) /\
      lower_value compile_expr cenv ty e s1 = (rhs, s2) /\
      compile_binop bop cur rhs ty NONE
        (if bop = Exp then expr_int_literal e else NONE) s2 = (res_op, s3) /\
      emit_void MSTORE [dst; res_op] s3 = ((), sf)
Proof
  cheat
QED

(* ===== The load ===== *)

(* A word field of a local struct, at x's pointer plus the field's
   offset: the word the field's value is held in. *)
Theorem stmt_state_rel_field_word:
  !func cenv cx es s id p sz w0 entry fs vals flds fld ftv fv fty ctx.
    stmt_state_rel ctx func cenv cx es s /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w0 /\
    lookup_scopes id es.scopes = SOME entry /\
    entry.type = StructTV fs /\ entry.value = StructV vals /\
    fields_layout flds fs /\ struct_has_type fs vals /\
    ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
    is_word_type fty /\ evaluate_type (get_tenv cx) fty = SOME ftv /\
    value_has_type ftv fv ==>
    mload (w2n (w0 + n2w (struct_field_offset flds fld))) s =
      typed_val_to_w256 ftv fv
Proof
  cheat
QED

(* The ADD and the MLOAD of x.f op= e: dst holds x's pointer plus off, and
   cur the word at dst. *)
Theorem attr_load_frag:
  !ctx func cenv cx es p off sa dst sn cur s1 s0 w0 R.
    emit_op ADD [Var p; Lit (n2w off)] sa = (dst, sn) /\
    emit_op MLOAD [dst] sn = (cur, s1) /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
    lookup_var p s0 = SOME w0 ==>
    frag_exec ctx sa s1 (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. stmt_state_rel ctx func cenv cx es s /\
           eval_operand dst s = SOME (w0 + n2w off) /\
           eval_operand cur s = SOME (mload (w2n (w0 + n2w off)) s0) /\
           (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
                  lookup_var x s = SOME u) /\
           (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP s.vs_allocas aid = SOME b)) R
Proof
  cheat
QED

(* ===== x.f op e ===== *)

(* A load of the target's current word (sa to s1: dst holds its address a,
   cur its word), then e and the operator, one after the other: e's errors
   and the operator's exit, and on a value v of the operator the result
   holds v's word, dst still holds a, and the frame from before the load
   holds.  The local and storage fields' loads are its instances. *)
Theorem augassign_load_bop_frag:
  !ctx func cenv cx es ty bop e el sa dst cur s1 rhs s2 res_op s3 s0 a v1
   r1 es1.
    (!R. frag_exec ctx sa s1
           (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
           (\s. stmt_state_rel ctx func cenv cx es s /\
                eval_operand dst s = SOME a /\
                eval_operand cur s = SOME (val_to_w256 v1) /\
                (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
                       lookup_var x s = SOME u) /\
                (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                         FLOOKUP s.vs_allocas aid = SOME b)) R) /\
    cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
    (!z. dst = Var z ==> not_fresh_at s1 z) /\ (!l. dst <> Label l) /\
    (!z. cur = Var z ==> not_fresh_at s1 z) /\ (!l. cur <> Label l) /\
    lower_value compile_expr cenv ty e s1 = (rhs, s2) /\
    compile_binop bop cur rhs ty NONE el s2 = (res_op, s3) /\
    cs_extends s1 s2 /\ s1.cs_next_var <= s2.cs_next_var /\
    (!z. rhs = Var z ==> not_fresh_at s2 z) /\ (!l. rhs <> Label l) /\
    fn_has_code sa s3 func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    expr_sim ctx func cenv cx ty e es /\
    (do result <- eval_expr cx e; read_result cx result od) es = (r1, es1) /\
    expr_res_ok r1 /\
    (!v2. r1 = INL v2 ==>
          word_value v2 /\ is_word_type (expr_type e) /\
          IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
          expr_res_ok (bop_result cx ty bop [ty; expr_type e] v1 v2 es1) /\
          binop_frag ctx func cenv cx bop ty ty NONE el [ty; expr_type e]
            v1 v2 es1) ==>
    frag_exec ctx sa s3 (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. ?v2 v. r1 = INL v2 /\
                  bop_result cx ty bop [ty; expr_type e] v1 v2 es1 = INL v /\
                  word_value v /\ stmt_state_rel ctx func cenv cx es1 s /\
                  eval_operand res_op s = SOME (val_to_w256 v) /\
                  eval_operand dst s = SOME a /\
                  (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
                         lookup_var x s = SOME u) /\
                  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                           FLOOKUP s.vs_allocas aid = SOME b))
      (expr_exit (case r1 of
                    INL v2 => bop_result cx ty bop [ty; expr_type e] v1 v2 es1
                  | INR ex => INR ex))
Proof
  cheat
QED

(* The ADD, the MLOAD, e and the operator, one after the other: e's errors
   and the operator's exit, and on a value v of the operator the result
   holds v's word, dst still holds the field's address, and the frame from
   before the ADD holds. *)
Theorem augassign_attr_bop_frag:
  !ctx func cenv cx es ty bop e el p off sa dst sn cur s1 rhs s2 res_op s3
   s0 w0 v1 r1 es1.
    emit_op ADD [Var p; Lit (n2w off)] sa = (dst, sn) /\
    emit_op MLOAD [dst] sn = (cur, s1) /\
    lower_value compile_expr cenv ty e s1 = (rhs, s2) /\
    compile_binop bop cur rhs ty NONE el s2 = (res_op, s3) /\
    cs_extends s1 s2 /\ s1.cs_next_var <= s2.cs_next_var /\
    (!z. rhs = Var z ==> not_fresh_at s2 z) /\ (!l. rhs <> Label l) /\
    fn_has_code sa s3 func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
    lookup_var p s0 = SOME w0 /\
    mload (w2n (w0 + n2w off)) s0 = val_to_w256 v1 /\
    expr_sim ctx func cenv cx ty e es /\
    (do result <- eval_expr cx e; read_result cx result od) es = (r1, es1) /\
    expr_res_ok r1 /\
    (!v2. r1 = INL v2 ==>
          word_value v2 /\ is_word_type (expr_type e) /\
          IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
          expr_res_ok (bop_result cx ty bop [ty; expr_type e] v1 v2 es1) /\
          binop_frag ctx func cenv cx bop ty ty NONE el [ty; expr_type e]
            v1 v2 es1) ==>
    frag_exec ctx sa s3 (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. ?v2 v. r1 = INL v2 /\
                  bop_result cx ty bop [ty; expr_type e] v1 v2 es1 = INL v /\
                  word_value v /\ stmt_state_rel ctx func cenv cx es1 s /\
                  eval_operand res_op s = SOME (val_to_w256 v) /\
                  eval_operand dst s = SOME (w0 + n2w off) /\
                  (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
                         lookup_var x s = SOME u) /\
                  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                           FLOOKUP s.vs_allocas aid = SOME b))
      (expr_exit (case r1 of
                    INL v2 => bop_result cx ty bop [ty; expr_type e] v1 v2 es1
                  | INR ex => INR ex))
Proof
  cheat
QED

(* ===== The statement ===== *)

(* Writing v at x.f for x a local of struct type sid in a state the
   expression invariant holds of, f one of sid's fields: unless it fails
   with a type error, x's value gets v at f, x's struct being laid out as
   the lowering's struct table says. *)
Theorem write_attr_local_typed:
  !cx cenv env id fld sid fty fsz es1 v res es'.
    write_place cx (MemoryPlace id [AttrSubscript fld]) v es1 = (res, es') /\
    (!m. res <> INR (Error (TypeError m))) /\
    expr_sim_inv cenv cx env es1 /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) ==>
    res = INL () /\
    ?pre env1 entry rest fs vals ftv.
      find_containing_scope id es1.scopes = SOME (pre, env1, entry, rest) /\
      entry.type = StructTV fs /\ entry.value = StructV vals /\
      fields_layout (get_struct_fields cenv.ce_struct_fields
                       (nsid_to_string sid)) fs /\
      struct_has_type fs vals /\ ALOOKUP fs fld = SOME ftv /\
      evaluate_type (get_tenv cx) fty = SOME ftv /\
      es' = es1 with scopes :=
        pre ++ (env1 |+ (id, entry with
                  <|value := StructV (AFUPDKEY fld (K v) vals);
                    popped := []|>)) :: rest
Proof
  cheat
QED

(* x.f for x a local of struct type sid in a state the expression invariant
   holds of, f one of sid's fields: its place, value and type are read. *)
Theorem augassign_attr_local_place:
  !cx cenv env es id fld sid fty fsz.
    expr_sim_inv cenv cx env es /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) ==>
    ?cur ptv.
      eval_target_place cx (AttributeTarget (NameTarget id) fld) es =
        (INL (MemoryPlace id [AttrSubscript fld]), es) /\
      read_place cx (MemoryPlace id [AttrSubscript fld]) es = (INL cur, es) /\
      place_type_value cx (MemoryPlace id [AttrSubscript fld]) es =
        (INL ptv, es)
Proof
  cheat
QED

(* x.f op= e as one fragment: e's errors and the operator's exit, and on
   a value of the operator the MSTORE writes it at x.f, related at the
   scopes write_place leaves. *)
Theorem augassign_attr_local_frag:
  !ctx func cenv cx es ty bop e el id fld p sz flds ftv sa dst sn cur s1 rhs
   s2 res_op s3 sf s0 v1 r1 es1 res es'.
    emit_op ADD [Var p; Lit (n2w (struct_field_offset flds fld))] sa =
      (dst, sn) /\
    emit_op MLOAD [dst] sn = (cur, s1) /\
    lower_value compile_expr cenv ty e s1 = (rhs, s2) /\
    compile_binop bop cur rhs ty NONE el s2 = (res_op, s3) /\
    emit_void MSTORE [dst; res_op] s3 = ((), sf) /\
    cs_extends s1 s2 /\ s1.cs_next_var <= s2.cs_next_var /\
    (!z. rhs = Var z ==> not_fresh_at s2 z) /\ (!l. rhs <> Label l) /\
    fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    (!s. stmt_state_rel ctx func cenv cx es s ==>
         ?w0. lookup_var p s = SOME w0 /\
              mload (w2n (w0 + n2w (struct_field_offset flds fld))) s =
                val_to_w256 v1) /\
    expr_sim ctx func cenv cx ty e es /\
    (do result <- eval_expr cx e; read_result cx result od) es = (r1, es1) /\
    expr_res_ok r1 /\
    (!v2. r1 = INL v2 ==>
          word_value v2 /\ is_word_type (expr_type e) /\
          IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
          expr_res_ok (bop_result cx ty bop [ty; expr_type e] v1 v2 es1) /\
          binop_frag ctx func cenv cx bop ty ty NONE el [ty; expr_type e]
            v1 v2 es1) /\
    is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME ftv /\
    type_memory_size ftv = 32 /\
    (!v2 v. r1 = INL v2 /\
            bop_result cx ty bop [ty; expr_type e] v1 v2 es1 = INL v ==>
            res = INL () /\
            ?pre env1 entry rest fs vals.
              find_containing_scope id es1.scopes =
                SOME (pre, env1, entry, rest) /\
              entry.type = StructTV fs /\ entry.value = StructV vals /\
              fields_layout flds fs /\ struct_has_type fs vals /\
              ALOOKUP fs fld = SOME ftv /\
              es' = es1 with scopes :=
                pre ++ (env1 |+ (id, entry with
                          <|value := StructV (AFUPDKEY fld (K v) vals);
                            popped := []|>)) :: rest) ==>
    frag_exec ctx sa sf (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\t. res = INL () /\ stmt_state_rel ctx func cenv cx es' t /\
           (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
                  lookup_var x t = SOME u) /\
           (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP t.vs_allocas aid = SOME b))
      (expr_exit (case r1 of
                    INL v2 => bop_result cx ty bop [ty; expr_type e] v1 v2 es1
                  | INR ex => INR ex))
Proof
  cheat
QED

(* x.f op= e for a local x of struct type sid and f a field of sid of type
   ty, ty a word_value_type, for every outcome: e's errors and the
   operator's (overflow, division by zero) exit, and on a value the MSTORE
   writes it at f's offset in x's region.  e may call internal functions:
   its simulation at f's type is a premise. *)
Theorem compile_augassign_attr_local_case:
  !ctx func cx lctx RetQ cenv ty0 env ty id fld sid fsz bop e es.
    expr_sim ctx func cenv cx ty e es /\ expr_body_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (ty, fsz) /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0
         (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
      (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
      es
Proof
  cheat
QED



(* compile_augassign_attr_local_case for an e with no internal call. *)
Theorem compile_augassign_attr_local_stmt_frag:
  !ctx func cx lctx RetQ cenv ty0 env ty id fld sid fsz bop e es.
    expr_sim_ok cenv e /\ expr_sim_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (ty, fsz) /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0
         (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
      (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
      es
Proof
  cheat
QED
