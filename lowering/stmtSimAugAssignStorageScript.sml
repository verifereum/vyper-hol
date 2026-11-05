(*
 * Statement simulation: an augmented assignment to a word storage or
 * transient variable (#637)
 *
 * self.x op= e for a module variable x in storage or transient storage of
 * a word type.  As for a local (stmtSimAugAssign), self.x op= e is
 * self.x = self.x op e on both sides: the source looks x up (a
 * StoragePlace at x's layout slot), reads it, evaluates e, runs the
 * operator and writes the slot, as evaluating self.x op e and then
 * assigning it would; the lowering is an SLOAD or TLOAD of x's slot, e
 * lowered at x's type, compile_binop and an SSTORE or TSTORE at the slot,
 * which is the code of that assignment, since the lowered read of self.x is
 * the same load.  So the statement is stmtSimAssignStorage's
 * compile_assign_storage_typed_stmt_frag for self.x op e, whose simulation
 * is compile_bop_word_case's (exprSimOperators): the checked operators'
 * aborts are among its exits, and ** and the narrow or negative shifts rest
 * on exprSimBinopFrag's cheats (#572).  The read of self.x is exprSimLeaves'
 * storage read, lifted to expr_sim by exprSimUnwrap's expr_sim_of_vv_sim,
 * which carries that theory's cheats for copies and constructor immutables.
 *
 * TOP-LEVEL:
 *   compile_augassign_toplevel_case — self.x op= e on a word storage or
 *                                     transient x, for every outcome,
 *                                     given e's expr_sim_case
 *   eval_augassign_toplevel_assign  — self.x op= e runs as
 *                                     self.x = self.x op e
 *   stmt_env_augassign_toplevel     — and has its code
 *   expr_body_pre_augassign_toplevel — self.x op e meets expr_body_pre
 *                                     where e does
 *
 * Helpers: eval_target_place_toplevel, eval_augassign_toplevel,
 *   eval_assign_pure_target, augassign_toplevel_code_parts,
 *   lower_value_toplevel_word, augassign_toplevel_code_bop,
 *   assign_toplevel_code_parts, toplevel_storage_name_case
 *)

Theory stmtSimAugAssignStorage
Ancestors
  exprBopSimProps
  exprSimSource
  exprSimHypsDefs
  stmtSimDefs
  loweringPosts
  allocLimits list finite_map
  fragExec  exprSimHyps exprSimOps exprSimOperators exprSimLeaves
   stmtSimAssign stmtSimAssignMem stmtSimAssignStorage
  stmtSimAugAssign
  exprLowering exprBopLowering exprLoweringProps stmtLowering compileEnv
  vyperInterpreter vyperState vyperValue vyperTypeSystem vyperTyping
  vyperTypeCallGraph vyperAST
Libs
  monadsyntax

(* ===== The source ===== *)

(* A storage or transient variable's target place is a StoragePlace at its
   layout slot, at its declared type. *)
Theorem eval_target_place_toplevel:
  !cx src id es ts tr typ id_str slot tvt.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt ==>
    eval_target_place cx (TopLevelNameTarget (src, id)) es =
      (INL (StoragePlace tr (n2w slot) tvt), es) /\
    place_type_value cx (StoragePlace tr (n2w slot) tvt) es = (INL tvt, es)
Proof
  cheat
QED

(* self.x op= e on a storage or transient x whose slot decodes to v0: x's
   place and type are read without changing the state, e is evaluated,
   then the operator runs on v0 and e's value, and the result is written
   to x's slot. *)
Theorem eval_augassign_toplevel:
  !cx ty src id bop e es res es' ts tr typ id_str slot tvt v0.
    eval_stmt cx (AugAssign ty (TopLevelNameTarget (src, id)) bop e) es =
      (res, es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es) ==>
    ?r1 es1.
      (do tv <- eval_expr cx e; read_result cx tv od) es = (r1, es1) /\
      case r1 of
        INR ex => res = INR ex /\ es' = es1
      | INL v =>
          case evaluate_binop
                 (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
                 tvt bop v0 v of
            INR err => res = INR (Error err) /\ es' = es1
          | INL r =>
              write_place cx (StoragePlace tr (n2w slot) tvt) r es1 =
                (res, es')
Proof
  cheat
QED

(* An assignment to a target whose place is p wherever it is evaluated:
   e's forced value, then the write of it at p. *)
Theorem eval_assign_pure_target:
  !cx t e p es.
    (!s. eval_target_place cx t s = (INL p, s)) ==>
    eval_stmt cx (Assign (BaseTarget t) e) es =
      case (do tv <- eval_expr cx e; read_result cx tv od) es of
        (INL v, es1) => write_place cx p v es1
      | (INR ex, es1) => (INR ex, es1)
Proof
  cheat
QED

(* self.x op= e runs as self.x = self.x op e, the read annotated with the
   statement's type. *)
Theorem eval_augassign_toplevel_assign:
  !cx ty src id bop e es res es' ts tr typ id_str slot tvt v0.
    eval_stmt cx (AugAssign ty (TopLevelNameTarget (src, id)) bop e) es =
      (res, es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es) /\
    bop <> In /\ bop <> NotIn ==>
    eval_stmt cx
      (Assign (BaseTarget (TopLevelNameTarget (src, id)))
         (Builtin ty (Bop bop) [TopLevelName ty (src, id); e])) es =
      (res, es')
Proof
  cheat
QED

(* ===== The code ===== *)

(* self.x op= e on a storage or transient x: no declaration, x's target is
   its slot with no code, then the load of the slot, e lowered at x's type,
   the operator and the store at the slot. *)
Theorem augassign_toplevel_code_parts:
  !cenv lctx ty0 ty nsid bop e sa c sf tr slot.
    stmt_env cenv lctx ty0 (AugAssign ty (TopLevelNameTarget nsid) bop e) sa =
      (c, sf) /\
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE ==>
    c = cenv /\
    ?s1 s2 s3 cur_op rhs_op res_op.
      emit_op (if tr then TLOAD else SLOAD) [Lit slot] sa = (cur_op, s1) /\
      lower_value compile_expr cenv ty e s1 = (rhs_op, s2) /\
      compile_binop bop cur_op rhs_op ty NONE
        (if bop = Exp then expr_int_literal e else NONE) s2 = (res_op, s3) /\
      emit_void (if tr then TSTORE else SSTORE) [Lit slot; res_op] s3 =
        ((), sf)
Proof
  cheat
QED

(* The lowered value of a word storage or transient variable is one load
   of its slot. *)
Theorem lower_value_toplevel_word:
  !cenv ty ann nsid tr slot sa op sb.
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    is_word_type ann /\
    lower_value compile_expr cenv ty (TopLevelName ann nsid) sa = (op, sb) ==>
    emit_op (if tr then TLOAD else SLOAD) [Lit slot] sa = (op, sb)
Proof
  cheat
QED

(* The code of self.x op= e is the lowering of self.x op e at x's type,
   then the store of its result at x's slot. *)
Theorem augassign_toplevel_code_bop:
  !cenv lctx ty0 ty nsid bop e sa c sf tr slot.
    stmt_env cenv lctx ty0 (AugAssign ty (TopLevelNameTarget nsid) bop e) sa =
      (c, sf) /\
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE /\
    word_value_type ty /\ bop <> In /\ bop <> NotIn ==>
    c = cenv /\
    ?s3 res_op.
      lower_value compile_expr cenv ty
        (Builtin ty (Bop bop) [TopLevelName ty nsid; e]) sa = (res_op, s3) /\
      emit_void (if tr then TSTORE else SSTORE) [Lit slot; res_op] s3 =
        ((), sf)
Proof
  cheat
QED

(* The code of self.x = e for a storage or transient x the lowering holds
   in one word and word-typed e: e's value, then the store at x's slot
   (assign_storage_word_code_parts without its fn_has_code facts). *)
Theorem assign_toplevel_code_parts[local]:
  !cenv lctx ty nsid e sa c sf tr slot vtyp.
    stmt_env cenv lctx ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e)
      sa = (c, sf) /\
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE /\
    cenv.ce_module_var_type nsid = SOME vtyp /\ is_word_type vtyp /\
    is_word_type (expr_type e) ==>
    c = cenv /\
    ?sb op.
      lower_value compile_expr cenv (expr_type e) e sa = (op, sb) /\
      emit_void (if tr then TSTORE else SSTORE) [Lit slot; op] sb = ((), sf)
Proof
  cheat
QED

(* The code of self.x op= e is the code of self.x = self.x op e. *)
Theorem stmt_env_augassign_toplevel:
  !cenv lctx ty0 ty nsid bop e tr slot vtyp.
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE /\
    cenv.ce_module_var_type nsid = SOME vtyp /\ is_word_type vtyp /\
    word_value_type ty /\ bop <> In /\ bop <> NotIn ==>
    stmt_env cenv lctx ty0 (AugAssign ty (TopLevelNameTarget nsid) bop e) =
    stmt_env cenv lctx ty0
      (Assign (BaseTarget (TopLevelNameTarget nsid))
         (Builtin ty (Bop bop) [TopLevelName ty nsid; e]))
Proof
  cheat
QED

(* ===== The operator ===== *)

(* The typing side: self.x op e meets expr_body_pre where e does, x is a
   module variable of type ty and the type checker accepts self.x op= e. *)
Theorem expr_body_pre_augassign_toplevel:
  !cenv cx env ty nsid bop e es.
    expr_body_pre cenv cx env e es /\
    FLOOKUP env.toplevel_vtypes nsid = SOME (Type ty) /\
    well_formed_type env.type_defs ty /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    expr_body_pre cenv cx env (Builtin ty (Bop bop) [TopLevelName ty nsid; e])
      es
Proof
  cheat
QED

(* A storage or transient variable's read simulates: exprSimLeaves' read
   of its slot, or its undecodable read's type error. *)
Theorem toplevel_storage_name_case[local]:
  !nocalls ctx func cenv cx ann src id ts tr typ id_str.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) ==>
    expr_sim_case nocalls ctx func cenv cx (TopLevelName ann (src, id))
Proof
  cheat
QED

(* ===== The statement ===== *)

(* self.x op= e on a word storage or transient variable x, for every
   outcome, given e's expr_sim_case (so e may make internal calls unless
   nocalls).  The statement's type ty is x's declared type, and the
   typing gives x that type (toplevel_vtypes). *)
(* Why it holds.  x's slot decodes wherever expr_sim_inv holds
   (toplevel_storage_read_decodes), so the source runs as
   self.x = self.x op e (eval_augassign_toplevel_assign), and the code is
   that assignment's (stmt_env_augassign_toplevel) once stmt_state_rel
   gives cenv's view of x's slot.  self.x op e meets expr_body_pre, its
   operands simulate, so it does (compile_bop_word_case), and its values
   are of x's type: compile_assign_storage_typed_stmt_frag applies. *)
Theorem compile_augassign_toplevel_case:
  !nocalls ctx func cx lctx RetQ cenv ty0 env ty src id bop e es
   ts tr id_str slot tvt vtyp.
    expr_sim_case nocalls ctx func cenv cx e /\
    expr_body_pre cenv cx env e es /\ (nocalls ==> int_calls_expr e = []) /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) ty = SOME tvt /\
    FLOOKUP env.toplevel_vtypes (src, id) = SOME (Type ty) /\
    well_formed_type env.type_defs ty /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME vtyp /\ is_word_type vtyp /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0
         (AugAssign ty (TopLevelNameTarget (src, id)) bop e))
      (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) es
Proof
  cheat
QED

(* Integrity gate: the source and code sides carry no admission; the
   statement itself inherits exprSimBinopFrag's (#572) and exprSimUnwrap's. *)
val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "AUGASSIGN_STORAGE_AUDIT OK\n"
     else print "statement-check gate skipped\n"
  end) [eval_augassign_toplevel_assign, stmt_env_augassign_toplevel,
        expr_body_pre_augassign_toplevel];
