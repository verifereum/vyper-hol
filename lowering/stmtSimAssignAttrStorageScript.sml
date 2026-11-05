(*
 * Statement simulation: Assign to a word field of a storage struct (#637)
 *
 * self.x.f = e for a module variable x of struct type in storage or
 * transient storage, f a field of a word type, and e of f's type.  The
 * source evaluates e, takes the place self.x.f (x's slot plus f's slot
 * offset, struct_field_slot), reads e's value and writes its encoding at
 * f's type there.  The lowering evaluates e, adds f's slot offset
 * (struct_field_offset_slots) to x's slot, unwraps the value and stores it
 * with one SSTORE or TSTORE.  The two offsets agree by fields_layout.
 *
 * TOP-LEVEL:
 *   eval_assign_attr_toplevel          — the source run: e's forced
 *                                        value, then write_storage_slot at
 *                                        the field's slot
 *   compile_assign_attr_storage_case  — self.x.f = e, every outcome, e's
 *                                        simulation a premise
 *   compile_assign_attr_storage_stmt_frag — the same for an e with no
 *                                        internal call
 *
 * Helpers: struct_field_slot_alookup, extend_storage_place_attr,
 *   eval_target_place_attr_toplevel, assign_attr_storage_source,
 *   assign_attr_storage_code_parts, store_var_frag, assign_attr_storage_frag
 *)

Theory stmtSimAssignAttrStorage
Ancestors
  exprSimFieldLayout
  exprSimSource
  stmtSimProps
  exprSimHypsDefs
  stmtSimDefs
  loweringPosts
  list rich_list finite_map pred_set alist
  fragExec exprSimHyps exprSimLeaves exprSimAttributeFields stmtSimDecl stmtSimDeclMem stmtSimAssign stmtSimAssignMem storageStoreFrame
  stmtSimAssignStorage stmtSimAssignAttr
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding accountsRelProps
  vyperInterpreter vyperState vyperStorage vyperValue vyperTyping
  vyperTypeEnv vyperTypeInvariants vyperTypeExprSoundness vyperTypeExprResult
  vyperExprNoControl
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* ===== The source ===== *)

Theorem struct_field_slot_alookup[local]:
  !fs id off ftv.
    struct_field_slot fs id = SOME (off, ftv) ==> ALOOKUP fs id = SOME ftv
Proof
  cheat
QED

(* A field of a storage struct: the slot plus the field's slot offset, at
   the field's type; any other case is a type error. *)
Theorem extend_storage_place_attr:
  !cx tr slot tv fld es r es'.
    extend_storage_place cx tr slot tv (AttrSubscript fld) es = (r, es') /\
    (!m. r <> INR (Error (TypeError m))) ==>
    es' = es /\
    ?fs off ftv. tv = StructTV fs /\ struct_field_slot fs fld = SOME (off, ftv) /\
                 r = INL (StoragePlace tr (slot + n2w off) ftv)
Proof
  cheat
QED

Theorem eval_target_place_attr_toplevel:
  !cx src id fld ts tr typ id_str slot es r es'.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    eval_target_place cx (AttributeTarget (TopLevelNameTarget (src, id)) fld)
      es = (r, es') /\
    (!m. r <> INR (Error (TypeError m))) ==>
    es' = es /\
    ?fs off ftv.
      evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
      struct_field_slot fs fld = SOME (off, ftv) /\
      r = INL (StoragePlace tr (n2w slot + n2w off) ftv)
Proof
  cheat
QED

(* self.x.f = e, unless it fails with a type error: e's forced value r,
   and on an error that error, on a value v the write of v at f's slot. *)
Theorem eval_assign_attr_toplevel:
  !cx src id fld e es res es' ts tr typ id_str slot.
    eval_stmt cx
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) es = (res, es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    (!m. res <> INR (Error (TypeError m))) ==>
    ?r es1.
      (do result <- eval_expr cx e; read_result cx result od) es = (r, es1) /\
      (!ex. r = INR ex ==> res = INR ex /\ es' = es1) /\
      (!v. r = INL v ==>
           ?fs off ftv.
             evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
             struct_field_slot fs fld = SOME (off, ftv) /\
             write_storage_slot cx tr (n2w slot + n2w off) ftv v es1 =
               (res, es'))
Proof
  cheat
QED

(* What self.x.f = e does on each outcome of e, with the typing that makes
   the write a one-slot store: f's slot is x's slot plus the offset the
   lowering's struct table gives, and e's value encodes there as its typed
   word. *)
Theorem assign_attr_storage_source:
  !cx cenv env lctx src id fld sid fty fsz e es res es' ts tr id_str slot.
    eval_stmt cx
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) es = (res, es') /\
    stmt_res_ok lctx res /\ expr_body_pre cenv cx env e es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ expr_type e = fty ==>
    ?r es1.
      (do result <- eval_expr cx e; read_result cx result od) es = (r, es1) /\
      expr_res_ok r /\
      (!ex. r = INR ex ==> res = INR ex /\ es' = es1) /\
      (!v. r = INL v ==>
           ?ftv. evaluate_type (get_tenv cx) fty = SOME ftv /\
                 encode_value ftv v = SOME [(0, typed_val_to_w256 ftv v)] /\
                 write_storage_slot cx tr
                   (n2w slot + n2w (struct_field_offset_slots
                      (get_struct_fields cenv.ce_struct_fields
                         (nsid_to_string sid)) fld))
                   ftv v es1 = (res, es') /\
                 !u st.
                   storage_dead cx tr
                     (update_storage
                        (n2w slot + n2w (struct_field_offset_slots
                           (get_struct_fields cenv.ce_struct_fields
                              (nsid_to_string sid)) fld)) u st) =
                   storage_dead cx tr st)
Proof
  cheat
QED

(* ===== The code ===== *)

(* The code of self.x.f = e for a storage or transient struct x and f of
   a word type: e's code, the ADD of f's slot offset to x's slot, e's
   unwrap, then one SSTORE or TSTORE at the field's slot. *)
Theorem assign_attr_storage_code_parts:
  !cenv lctx ty src id fld e sa c sf tr slot sid fty fsz.
    stmt_env cenv lctx ty
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) sa = (c, sf) /\
    FLOOKUP cenv.ce_module_vars (src, id) =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ is_word_type (expr_type e) ==>
    c = cenv /\
    ?vv sm dst sn op su.
      compile_expr cenv (expr_type e) e sa = (vv, sm) /\
      emit_op ADD
        [Lit slot; Lit (n2w (struct_field_offset_slots
           (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
           fld))] sm = (dst, sn) /\
      unwrap_value cenv vv sn = (op, su) /\
      emit_void (if tr then TSTORE else SSTORE) [dst; op] su = ((), sf)
Proof
  cheat
QED

(* An SSTORE or TSTORE at a variable holding a slot, run. *)
Theorem store_var_frag:
  !ctx func cenv cx es' s1 tr d a op w st st' R.
    emit_void (if tr then TSTORE else SSTORE) [Var d; op] st = ((), st') /\
    lookup_var d s1 = SOME a /\ eval_operand op s1 = SOME w /\
    stmt_state_rel ctx func cenv cx es'
      (if tr then tstore a w s1 else sstore a w s1) ==>
    frag_exec ctx st st' (\t. t = s1)
      (\t. stmt_state_rel ctx func cenv cx es' t /\
           (!x. lookup_var x t = lookup_var x s1) /\
           (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
                    FLOOKUP t.vs_allocas aid = SOME b)) R
Proof
  cheat
QED

(* self.x.f = e as one fragment: e's errors exit, and on a value it reaches
   its end related at the state the slot write leaves. *)
Theorem assign_attr_storage_frag:
  !ctx func cenv cx e es res es' r es1 sa vv sm dst sn op su sf tr slot off
   s0.
    compile_expr cenv (expr_type e) e sa = (vv, sm) /\
    emit_op ADD [Lit (n2w slot); Lit (n2w off)] sm = (dst, sn) /\
    unwrap_value cenv vv sn = (op, su) /\
    emit_void (if tr then TSTORE else SSTORE) [dst; op] su = ((), sf) /\
    fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    is_word_type (expr_type e) /\
    (do result <- eval_expr cx e; read_result cx result od) es = (r, es1) /\
    expr_res_ok r /\
    (!v. r = INL v ==>
         ?ftv. evaluate_type (get_tenv cx) (expr_type e) = SOME ftv /\
               encode_value ftv v = SOME [(0, typed_val_to_w256 ftv v)] /\
               write_storage_slot cx tr (n2w slot + n2w off) ftv v es1 =
                 (res, es') /\
               !u st.
                 storage_dead cx tr (update_storage (n2w slot + n2w off) u st) =
                 storage_dead cx tr st) ==>
    frag_exec ctx sa sf (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\t. res = INL () /\ stmt_state_rel ctx func cenv cx es' t /\
           (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
                  lookup_var x t = SOME u) /\
           (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP t.vs_allocas aid = SOME b))
      (expr_exit r)
Proof
  cheat
QED

(* self.x.f = e for a storage or transient struct x the lowering holds by
   slot (no hashmap) and a field f of a word type that e has, for every
   outcome: e's errors exit, and on a value its word is stored at the
   field's slot.  e may call internal functions: its simulation is a
   premise. *)
Theorem compile_assign_attr_storage_case:
  !ctx func cx lctx RetQ cenv ty env src id fld sid fty fsz e es ts
   tr id_str slot.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ expr_type e = fty /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    expr_body_pre cenv cx env e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e))
      (eval_stmt cx
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e))
      es
Proof
  cheat
QED

(* compile_assign_attr_storage_case for an e with no internal call. *)
Theorem compile_assign_attr_storage_stmt_frag:
  !ctx func cx lctx RetQ cenv ty env src id fld sid fty fsz e es ts
   tr id_str slot.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ expr_type e = fty /\
    expr_vv_ok cenv e /\ expr_sim_pre cenv cx env e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e))
      (eval_stmt cx
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e))
      es
Proof
  cheat
QED
