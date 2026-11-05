(*
 * Statement simulation: Assign to a word field of a local struct (#637)
 *
 * x.f = e for a local x of struct type held in memory at its pointer, f a
 * field of a word type, and e of f's type.  The source evaluates e, takes
 * the place x.f (the field must be in x's value), reads e's value and
 * writes it into x's value at f (write_place on MemoryPlace x [f]).  The
 * lowering evaluates e, adds f's byte offset to x's pointer, unwraps the
 * value and stores it there with one MSTORE.  The ADD sits between e's
 * code and the unwrap, so e is taken through expr_vv_sim and
 * exprSimAggregateChildren's rebased unwrap, as a struct literal's
 * children are.
 *
 * TOP-LEVEL:
 *   eval_assign_attr_local           — the source run: e's forced value,
 *                                      then write_place on x.f
 *   stmt_state_rel_write_field       — an MSTORE at a word field's offset
 *                                      relates the scopes write_place leaves
 *   expr_add_unwrap_frag             — e's code, an ADD of an offset to a
 *                                      base, and e's unwrap, run
 *   attribute_type_struct_field      — a field the typing gives a struct is
 *                                      in the lowering's struct table
 *   compile_assign_attr_local_case   — x.f = e, every outcome, e's
 *                                      simulation a premise
 *   compile_assign_attr_local_stmt_frag — the same for an e with no
 *                                      internal call
 *
 * Helpers: eval_target_place_attr_local,
 *   write_place_attr_local, fields_in_memory_mstore_field,
 *   fields_val_wf_update, assign_attr_local_code_parts,
 *   assign_attr_local_source, mstore_var_frag, assign_attr_local_frag
 *)

Theory stmtSimAssignAttr
Ancestors
  exprSimFieldLayout exprSimProps
  exprSimSource
  stmtSimProps
  exprSimHypsDefs
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set alist
  fragExec localPtrsProps  exprSimHyps exprSimUnwrap exprSimBuffer
  exprSimAggregateChildren exprSimAttributeFields freshWrites
   stmtSimDecl stmtSimDeclMem stmtSimDeclStore stmtSimAssignStore
  stmtSimAssign
  stmtSimAssignMem stmtSimAugAssign
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  exprOperandVar compileEnv valueEncoding valueEncodingProps
  vyperInterpreter vyperState vyperValue vyperLookup vyperExprNoControl
  vyperTyping vyperTypeEnv vyperTypeInvariants vyperTypeExprSoundness
  vyperTypeExprResult
  venomInst venomState
Libs
  monadsyntax

(* ===== The source ===== *)

Theorem alookup_fields_args[local]:
  !fields args fld fty.
    MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args /\
    ALOOKUP args fld = SOME fty ==>
    ?fsz. ALOOKUP fields fld = SOME (fty, fsz)
Proof
  cheat
QED

(* A field the typing gives a struct is in the lowering's struct table,
   at the type the typing gives it. *)
Theorem attribute_type_struct_field:
  !cenv cx env es sid fld fty.
    expr_sim_inv cenv cx env es /\
    attribute_type (get_tenv cx) (StructT sid) fld = SOME fty ==>
    ?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields
                     (nsid_to_string sid)) fld = SOME (fty, fsz)
Proof
  cheat
QED

(* The place x.f for a local x in scope whose value has field f, and only
   then: any other case is a type error. *)
Theorem eval_target_place_attr_local:
  !cx id fld es r es'.
    eval_target_place cx (AttributeTarget (NameTarget id) fld) es =
      (r, es') /\
    (!m. r <> INR (Error (TypeError m))) ==>
    es' = es /\ r = INL (MemoryPlace id [AttrSubscript fld]) /\
    ?entry vals old.
      lookup_scopes id es.scopes = SOME entry /\
      entry.value = StructV vals /\ ALOOKUP vals fld = SOME old
Proof
  cheat
QED

(* Writing v at x.f, where x's value has field f: unless it fails with a
   type error (x not assignable), x's value gets v at f. *)
Theorem write_place_attr_local:
  !cx id fld v es res es' entry vals old.
    write_place cx (MemoryPlace id [AttrSubscript fld]) v es = (res, es') /\
    lookup_scopes id es.scopes = SOME entry /\
    entry.value = StructV vals /\ ALOOKUP vals fld = SOME old /\
    (!m. res <> INR (Error (TypeError m))) ==>
    ?pre env rest.
      find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
      res = INL () /\
      es' = es with scopes :=
              pre ++ (env |+ (id, entry with
                        <|value := StructV (AFUPDKEY fld (K v) vals);
                          popped := []|>)) :: rest
Proof
  cheat
QED

(* x.f = e, unless it fails with a type error: e's forced value r, and
   on an error that error, on a value v the write of v at x.f, where x's
   value has field f. *)
Theorem eval_assign_attr_local:
  !cx id fld e es res es'.
    eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
      es = (res, es') /\
    (!m. res <> INR (Error (TypeError m))) ==>
    ?r es1.
      (do result <- eval_expr cx e; read_result cx result od) es = (r, es1) /\
      (!ex. r = INR ex ==> res = INR ex /\ es' = es1) /\
      (!v. r = INL v ==>
           ?entry vals old.
             lookup_scopes id es1.scopes = SOME entry /\
             entry.value = StructV vals /\ ALOOKUP vals fld = SOME old /\
             write_place cx (MemoryPlace id [AttrSubscript fld]) v es1 =
               (res, es'))
Proof
  cheat
QED

(* ===== The struct in memory after a field store ===== *)

Theorem fields_in_memory_mstore_field:
  !vals fs flds off s fld v wd ftv.
    fields_layout flds fs /\ struct_has_type fs vals /\
    fields_val_wf vals fs /\ fields_in_memory vals fs off s.vs_memory /\
    ALOOKUP fs fld = SOME ftv /\ type_memory_size ftv = 32 /\
    val_in_memory ftv v (off + struct_field_offset flds fld)
      (mstore (off + struct_field_offset flds fld) wd s).vs_memory ==>
    fields_in_memory (AFUPDKEY fld (K v) vals) fs off
      (mstore (off + struct_field_offset flds fld) wd s).vs_memory
Proof
  cheat
QED

Theorem fields_val_wf_update:
  !vals fs fld v ftv.
    struct_has_type fs vals /\ fields_val_wf vals fs /\
    ALOOKUP fs fld = SOME ftv /\ val_wf ftv v ==>
    fields_val_wf (AFUPDKEY fld (K v) vals) fs
Proof
  cheat
QED

(* An MSTORE of the word that lays v out at field fld's offset in a
   local's region relates the scopes in which the local's value has v at
   fld. *)
Theorem stmt_state_rel_write_field:
  !func cenv cx es s id p sz w pre env entry rest fs vals flds fld ftv etv v ctx.
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\
    entry.type = StructTV fs /\ entry.value = StructV vals /\
    fields_layout flds fs /\ struct_has_type fs vals /\
    ALOOKUP fs fld = SOME ftv /\ store_lays_out etv ftv v ==>
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
         pre ++ (env |+ (id, entry with
                   <|value := StructV (AFUPDKEY fld (K v) vals);
                     popped := []|>)) :: rest)
      (mstore (w2n w + struct_field_offset flds fld)
         (typed_val_to_w256 etv v) s)
Proof
  cheat
QED

(* ===== The code ===== *)

(* The code of x.f = e for a local x of struct type and f of a word type:
   e's code, the ADD of f's byte offset to x's pointer, e's unwrap, then
   one MSTORE at the field. *)
Theorem assign_attr_local_code_parts:
  !cenv lctx ty id fld e sa c sf p sz sid fty fsz.
    stmt_env cenv lctx ty
      (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) sa =
      (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ is_word_type (expr_type e) ==>
    c = cenv /\
    ?vv sm dst sn op su.
      compile_expr cenv (expr_type e) e sa = (vv, sm) /\
      emit_op ADD
        [Var p; Lit (n2w (struct_field_offset
           (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
           fld))] sm = (dst, sn) /\
      unwrap_value cenv vv sn = (op, su) /\
      emit_void MSTORE [dst; op] su = ((), sf)
Proof
  cheat
QED

(* ===== e, an ADD, and e's unwrap ===== *)

(* After the ADD and the unwrap: e's value at op, the ADD's sum in dst,
   and the frame from before e. *)
Theorem add_unwrap_post[local]:
  !func cenv cx e es sa sm sn su s0 es1 tv vv r v op dst bw off s.
    emit_op ADD [bop; Lit (n2w off)] sm = (dst, sn) /\
    ci_mono sa sm /\
    vv_post ctx func cenv cx e es sa sn s0 es1 tv vv r /\
    eval_operand dst r = SOME (bw + n2w off) /\
    expr_post ctx func cenv cx e es1 (sa with cs_next_var := sn.cs_next_var)
      su r es1 v op s ==>
    stmt_state_rel ctx func cenv cx es1 s /\
    expr_val_rel cx (expr_type e) v op s /\
    eval_operand dst s = SOME (bw + n2w off) /\
    (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
           lookup_var x s = SOME u) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b)
Proof
  cheat
QED

(* e's code, an ADD of off to the base operand bop, then e's unwrap: on
   a value, op holds e's value and the ADD's output the base plus off, in
   a state related at the state after e; e's errors exit. *)
Theorem expr_add_unwrap_frag:
  !ctx func cenv cx e es res es1 sa vv sm bop off dst sn op su s0 bw.
    compile_expr cenv (expr_type e) e sa = (vv, sm) /\
    emit_op ADD [bop; Lit (n2w off)] sm = (dst, sn) /\
    unwrap_value cenv vv sn = (op, su) /\
    fn_has_code sa su func /\ fn_inst_ids_distinct func /\
    is_word_type (expr_type e) /\
    local_ptrs_reserved cenv sa /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    (do result <- eval_expr cx e; read_result cx result od) es = (res, es1) /\
    expr_res_ok res /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\ (!l. bop <> Label l) /\
    eval_operand bop s0 = SOME bw ==>
    frag_exec ctx sa su (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. ?v. res = INL v /\ stmt_state_rel ctx func cenv cx es1 s /\
               expr_val_rel cx (expr_type e) v op s /\
               eval_operand dst s = SOME (bw + n2w off) /\
               (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
                      lookup_var x s = SOME u) /\
               (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                        FLOOKUP s.vs_allocas aid = SOME b))
      (expr_exit res)
Proof
  cheat
QED





(* ===== x.f = e ===== *)

(* What x.f = e does on each outcome of e, with the typing that makes the
   write a field store: x's value is a struct laid out as the lowering's
   struct table says, its field f is of f's declared word type, and e's
   value is of that type. *)
Theorem assign_attr_local_source:
  !cx cenv env lctx id fld sid fty fsz e es res es'.
    eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
      es = (res, es') /\
    stmt_res_ok lctx res /\ expr_body_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ expr_type e = fty ==>
    ?r es1.
      (do result <- eval_expr cx e; read_result cx result od) es = (r, es1) /\
      expr_res_ok r /\
      (!ex. r = INR ex ==> res = INR ex /\ es' = es1) /\
      (!v. r = INL v ==>
           res = INL () /\
           ?pre env1 entry rest fs vals ftv.
             find_containing_scope id es1.scopes =
               SOME (pre, env1, entry, rest) /\
             entry.type = StructTV fs /\ entry.value = StructV vals /\
             fields_layout (get_struct_fields cenv.ce_struct_fields
                              (nsid_to_string sid)) fs /\
             struct_has_type fs vals /\ ALOOKUP fs fld = SOME ftv /\
             evaluate_type (get_tenv cx) fty = SOME ftv /\
             store_lays_out ftv ftv v /\
             es' = es1 with scopes :=
               pre ++ (env1 |+ (id, entry with
                         <|value := StructV (AFUPDKEY fld (K v) vals);
                           popped := []|>)) :: rest)
Proof
  cheat
QED

(* An MSTORE at a variable holding an address, run. *)
Theorem mstore_var_frag[local]:
  !ctx func cenv cx es' s1 d op wd a st st' R.
    emit_void MSTORE [Var d; op] st = ((), st') /\
    lookup_var d s1 = SOME a /\ eval_operand op s1 = SOME wd /\
    stmt_state_rel ctx func cenv cx es' (mstore (w2n a) wd s1) ==>
    frag_exec ctx st st' (\t. t = s1)
      (\t. stmt_state_rel ctx func cenv cx es' t /\
           (!x. lookup_var x t = lookup_var x s1) /\
           (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
                    FLOOKUP t.vs_allocas aid = SOME b)) R
Proof
  cheat
QED

(* The MSTORE of x.f = e, from the state e's unwrap leaves: the field's
   address is x's base plus f's offset, which does not wrap since x's
   region lies below the allocation frontier. *)
Theorem assign_attr_local_store:
  !ctx func cenv cx es1 t d op su sf p sz w0 off id pre env1 entry rest fs
   vals flds fld ftv v R.
    emit_void MSTORE [Var d; op] su = ((), sf) /\
    lookup_var d t = SOME (w0 + n2w off) /\ lookup_var p t = SOME w0 /\
    eval_operand op t = SOME (typed_val_to_w256 ftv v) /\
    stmt_state_rel ctx func cenv cx es1 t /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    find_containing_scope id es1.scopes = SOME (pre, env1, entry, rest) /\
    entry.type = StructTV fs /\ entry.value = StructV vals /\
    fields_layout flds fs /\ struct_has_type fs vals /\
    ALOOKUP fs fld = SOME ftv /\ store_lays_out ftv ftv v /\
    off = struct_field_offset flds fld ==>
    frag_exec ctx su sf (\s. s = t)
      (\t'. stmt_state_rel ctx func cenv cx
              (es1 with scopes :=
                 pre ++ (env1 |+ (id, entry with
                           <|value := StructV (AFUPDKEY fld (K v) vals);
                             popped := []|>)) :: rest) t' /\
            (!x. lookup_var x t' = lookup_var x t) /\
            (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
                     FLOOKUP t'.vs_allocas aid = SOME b)) R
Proof
  cheat
QED

(* x.f = e as one fragment: e's errors exit, and on a value it reaches
   its end related at the scopes write_place leaves. *)
Theorem assign_attr_local_frag:
  !ctx func cenv cx id fld sid e es res es' r es1 sa vv sm dst sn op su
   sf p sz entry0 s0.
    compile_expr cenv (expr_type e) e sa = (vv, sm) /\
    emit_op ADD
      [Var p; Lit (n2w (struct_field_offset
         (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
         fld))] sm = (dst, sn) /\
    unwrap_value cenv vv sn = (op, su) /\
    emit_void MSTORE [dst; op] su = ((), sf) /\
    fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_scopes id es.scopes = SOME entry0 /\
    is_word_type (expr_type e) /\
    (do result <- eval_expr cx e; read_result cx result od) es = (r, es1) /\
    expr_res_ok r /\
    (!v. r = INL v ==>
         res = INL () /\
         ?pre env1 entry rest fs vals ftv.
           find_containing_scope id es1.scopes =
             SOME (pre, env1, entry, rest) /\
           entry.type = StructTV fs /\ entry.value = StructV vals /\
           fields_layout (get_struct_fields cenv.ce_struct_fields
                            (nsid_to_string sid)) fs /\
           struct_has_type fs vals /\ ALOOKUP fs fld = SOME ftv /\
           evaluate_type (get_tenv cx) (expr_type e) = SOME ftv /\
           store_lays_out ftv ftv v /\
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
      (expr_exit r)
Proof
  cheat
QED

(* x.f = e for a local x of struct type sid, f a field of sid of a word
   type, and e of f's type, for every outcome: e's errors exit, and on a
   value its typed word is stored at f's offset in x's region.  e may call
   internal functions: its simulation is a premise. *)
Theorem compile_assign_attr_local_case:
  !ctx func cx lctx RetQ cenv ty env id fld sid fty fsz e es.
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    expr_body_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ expr_type e = fty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      es
Proof
  cheat
QED

(* compile_assign_attr_local_case for an e with no internal call. *)
Theorem compile_assign_attr_local_stmt_frag:
  !ctx func cx lctx RetQ cenv ty env id fld sid fty fsz e es.
    expr_vv_ok cenv e /\ expr_sim_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ expr_type e = fty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      es
Proof
  cheat
QED
