(*
 * Statement simulation: an augmented assignment to a word field of a
 * storage or transient struct (#637)
 *
 * self.x.f op= e for a module variable x in storage or transient storage
 * of a struct type and a field f of a word type.  The source looks up
 * x.f's place (a StoragePlace at x's layout slot plus f's slot offset),
 * reads it, evaluates e, runs the operator and writes the slot.  The
 * lowering ADDs f's slot offset to x's slot into dst, loads dst (SLOAD or
 * TLOAD), lowers e at f's type, runs compile_binop and stores the result
 * at dst (SSTORE or TSTORE).  This is no assignment's code (self.x.f =
 * self.x.f op e would ADD twice), so the proof composes the pieces as
 * stmtSimAugAssignAttr does for a field of a local struct.  As there, **
 * and the narrow or negative shifts rest on exprSimBinopFrag's cheats
 * (#572).
 *
 * TOP-LEVEL:
 *   compile_augassign_attr_storage_case — self.x.f op= e, every outcome,
 *                                         given e's simulation
 *
 *   augassign_attr_storage_place        — x.f's place, value and type are
 *                                         read where expr_sim_inv holds
 *
 * Helpers: eval_target_place_attr_toplevel_field,
 *   augassign_storage_field_place, augassign_storage_field_read,
 *   eval_augassign_attr_storage, augassign_attr_storage_source,
 *   augassign_attr_storage_code_parts, augassign_storage_load_frag,
 *   augassign_attr_storage_frag
 *)

Theory stmtSimAugAssignAttrStorage
Ancestors
  exprBopSimDefs
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
  exprSimBinopFrag exprSimOperators exprSimLeaves exprSimAttributeFields
  exprSimUnwrap
   stmtSimDeclMem stmtSimAssign stmtSimAssignStorage stmtSimAugAssign
  stmtSimAssignAttr stmtSimAssignAttrStorage stmtSimAugAssignAttr
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding accountsRelProps
  vyperInterpreter vyperState vyperStorage vyperValue vyperValueOperation
  vyperTyping vyperTypeEnv vyperTypeInvariants vyperTypeExprSoundness
  vyperTypeSystem vyperAST
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* x.f's place for a storage or transient struct x: x's slot plus f's slot
   offset, at f's type. *)
Theorem eval_target_place_attr_toplevel_field:
  !cx src id fld es ts tr typ id_str slot fs off ftv.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
    struct_field_slot fs fld = SOME (off, ftv) ==>
    eval_target_place cx (AttributeTarget (TopLevelNameTarget (src, id)) fld)
      es = (INL (StoragePlace tr (n2w slot + n2w off) ftv), es) /\
    place_type_value cx (StoragePlace tr (n2w slot + n2w off) ftv) es =
      (INL ftv, es)
Proof
  cheat
QED

(* A non-type-error AugAssign has successfully resolved its target. *)
Theorem augassign_storage_field_place[local]:
  !cx ty src id fld bop e es res es' ts tr sid id_str slot.
    eval_stmt cx
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop e)
      es = (res, es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts =
      SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    (!m. res <> INR (Error (TypeError m))) ==>
    ?fs off ftv.
      evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
      struct_field_slot fs fld = SOME (off, ftv)
Proof
  cheat
QED

(* A declared struct's field read carries the canonical-slot and live-byte
   facts needed by the backend load, independently of RHS evaluation. *)
Theorem augassign_storage_field_read[local]:
  !cx es src id ts tr sid id_str slot fs fld off ftv ty.
    contract_storage_well_formed cx es /\ storage_layout_safe cx /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts =
      SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    struct_field_slot fs fld = SOME (off, ftv) /\
    evaluate_type (get_tenv cx) ty = SOME ftv ==>
    ?cur. read_storage_slot cx tr (n2w slot + n2w off) ftv es =
            (INL cur, es) /\
          !ctx func cenv s.
            stmt_state_rel ctx func cenv cx es s ==>
            storage_holds cx tr ty (Value cur) (n2w slot + n2w off) es s
Proof
  cheat
QED

(* The saved field is read before the RHS; its address and type are kept
   even if the RHS changes storage. *)
Theorem eval_augassign_attr_storage[local]:
  !cx ty src id fld bop e es res es' ts tr sid id_str slot fs off ftv cur.
    eval_stmt cx
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop e)
      es = (res, es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts =
      SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    struct_field_slot fs fld = SOME (off, ftv) /\
    read_storage_slot cx tr (n2w slot + n2w off) ftv es = (INL cur, es) ==>
    ?r1 es1.
      (do tv <- eval_expr cx e; read_result cx tv od) es = (r1, es1) /\
      case r1 of
        INR ex => res = INR ex /\ es' = es1
      | INL v2 =>
          case evaluate_binop
                 (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
                 ftv bop cur v2 of
            INR err => res = INR (Error err) /\ es' = es1
          | INL v => write_storage_slot cx tr (n2w slot + n2w off) ftv v es1 =
                      (res, es')
Proof
  cheat
QED

Theorem augassign_attr_storage_source[local]:
  !cx cenv env lctx ty src id fld sid fsz bop e es res es' ts tr id_str slot.
    eval_stmt cx
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop e)
      es = (res, es') /\
    stmt_res_ok lctx res /\ expr_body_pre cenv cx env e es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts =
      SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (ty, fsz) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    ?fs off ftv cur r1 es1.
      evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
      struct_field_slot fs fld = SOME (off, ftv) /\
      struct_field_offset_slots
        (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld =
      off /\
      evaluate_type (get_tenv cx) ty = SOME ftv /\
      value_has_type ftv cur /\ word_value cur /\
      (!ctx func s.
         stmt_state_rel ctx func cenv cx es s ==>
         storage_holds cx tr ty (Value cur) (n2w slot + n2w off) es s) /\
      (do tv <- eval_expr cx e; read_result cx tv od) es = (r1, es1) /\
      expr_res_ok r1 /\
      (!v2. r1 = INL v2 ==> ?tv2.
        evaluate_type (get_tenv cx) (expr_type e) = SOME tv2 /\
        value_has_type tv2 v2 /\ word_value v2) /\
      (case r1 of
         INR ex => res = INR ex /\ es' = es1
       | INL v2 =>
           case bop_result cx ty bop [ty; expr_type e] cur v2 es1 of
             INR ex => res = INR ex /\ es' = es1
           | INL v => write_storage_slot cx tr (n2w slot + n2w off) ftv v es1 =
                       (res, es')) /\
      (!v2 v. r1 = INL v2 /\
        bop_result cx ty bop [ty; expr_type e] cur v2 es1 = INL v ==>
        encode_value ftv v = SOME [(0, val_to_w256 v)]) /\
      (!u st. storage_dead cx tr
        (update_storage (n2w slot + n2w off) u st) = storage_dead cx tr st)
Proof
  cheat
QED

Theorem augassign_attr_storage_code_parts[local]:
  !cenv lctx ty0 ty src id fld sid fty fsz bop e sa c sf tr slot.
    stmt_env cenv lctx ty0
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop e)
      sa = (c, sf) /\
    FLOOKUP cenv.ce_module_vars (src, id) =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) ==>
    c = cenv /\
    ?dst sn cur s1 rhs s2 res_op s3.
      emit_op ADD
        [Lit slot; Lit (n2w (struct_field_offset_slots
          (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))]
        sa = (dst, sn) /\
      emit_op (if tr then TLOAD else SLOAD) [dst] sn = (cur, s1) /\
      lower_value compile_expr cenv ty e s1 = (rhs, s2) /\
      compile_binop bop cur rhs ty NONE
        (if bop = Exp then expr_int_literal e else NONE) s2 = (res_op, s3) /\
      emit_void (if tr then TSTORE else SSTORE) [dst; res_op] s3 = ((), sf)
Proof
  cheat
QED

Theorem augassign_storage_load_frag[local]:
  !ctx func cenv cx es sa sn s1 dst cur s0 tr slot off ty ftv v R.
    emit_op ADD [Lit slot; Lit (n2w off)] sa = (dst, sn) /\
    emit_op (if tr then TLOAD else SLOAD) [dst] sn = (cur, s1) /\
    local_ptrs_reserved cenv sa /\ is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME ftv /\ word_value v /\
    (!s. stmt_state_rel ctx func cenv cx es s ==>
         storage_holds cx tr ty (Value v) (slot + n2w off) es s) ==>
    frag_exec ctx sa s1 (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. stmt_state_rel ctx func cenv cx es s /\
           eval_operand dst s = SOME (slot + n2w off) /\
           eval_operand cur s = SOME (val_to_w256 v) /\
           (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
                  lookup_var x s = SOME u) /\
           (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP s.vs_allocas aid = SOME b)) R
Proof
  cheat
QED

Theorem augassign_attr_storage_frag[local]:
  !ctx func cenv cx es ty bop e el sa sn dst cur s1 rhs s2 res_op s3 sf s0
   tr slot off ftv v1 r1 es1 res es'.
    emit_op ADD [Lit slot; Lit (n2w off)] sa = (dst, sn) /\
    emit_op (if tr then TLOAD else SLOAD) [dst] sn = (cur, s1) /\
    lower_value compile_expr cenv ty e s1 = (rhs, s2) /\
    compile_binop bop cur rhs ty NONE el s2 = (res_op, s3) /\
    emit_void (if tr then TSTORE else SSTORE) [dst; res_op] s3 = ((), sf) /\
    cs_extends s1 s2 /\ s1.cs_next_var <= s2.cs_next_var /\
    (!z. rhs = Var z ==> not_fresh_at s2 z) /\ (!l. rhs <> Label l) /\
    fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME ftv /\ word_value v1 /\
    (!s. stmt_state_rel ctx func cenv cx es s ==>
         storage_holds cx tr ty (Value v1) (slot + n2w off) es s) /\
    expr_sim ctx func cenv cx ty e es /\
    (do result <- eval_expr cx e; read_result cx result od) es = (r1, es1) /\
    expr_res_ok r1 /\
    (!v2. r1 = INL v2 ==>
      word_value v2 /\ is_word_type (expr_type e) /\
      IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
      expr_res_ok (bop_result cx ty bop [ty; expr_type e] v1 v2 es1) /\
      binop_frag ctx func cenv cx bop ty ty NONE el [ty; expr_type e]
        v1 v2 es1) /\
    (!v2 v. r1 = INL v2 /\
      bop_result cx ty bop [ty; expr_type e] v1 v2 es1 = INL v ==>
      encode_value ftv v = SOME [(0, val_to_w256 v)] /\
      write_storage_slot cx tr (slot + n2w off) ftv v es1 = (res, es')) /\
    (!u st. storage_dead cx tr (update_storage (slot + n2w off) u st) =
      storage_dead cx tr st) ==>
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

(* x.f's place, value and type are read for a storage or transient struct
   x where expr_sim_inv holds: the read decodes x's whole value. *)
Theorem augassign_attr_storage_place:
  !cx cenv env es src id fld ts tr sid id_str slot fty fsz.
    expr_sim_inv cenv cx env es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts =
      SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    IS_SOME (evaluate_type (get_tenv cx) (StructT sid)) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) ==>
    ?p cur ptv.
      eval_target_place cx (AttributeTarget (TopLevelNameTarget (src, id)) fld)
        es = (INL p, es) /\
      read_place cx p es = (INL cur, es) /\
      place_type_value cx p es = (INL ptv, es)
Proof
  cheat
QED

(* self.x.f op= e for a storage or transient struct x the lowering holds by
   slot (no hashmap) and a field f of x's struct of a word type ty, for
   every outcome: e's errors and the operator's (overflow, division by
   zero) exit, and on a value of the operator its word is stored at f's
   slot.  e may call internal functions: its simulation at ty is a
   premise. *)
Theorem compile_augassign_attr_storage_case:
  !ctx func cx lctx RetQ cenv ty0 env src id fld sid ty fsz bop e es
   ts tr id_str slot.
    expr_sim ctx func cenv cx ty e es /\ expr_body_pre cenv cx env e es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts =
      SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (ty, fsz) /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0
         (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld)
            bop e))
      (eval_stmt cx
         (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld)
            bop e)) es
Proof
  cheat
QED
