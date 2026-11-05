(*
 * Source writes of a tuple into locals and the code of the stores, shared
 * by the word-only and the memory-backed tuple assignment.
 *
 * TOP-LEVEL:
 *   assign_tuple_target_local, assign_tuple_target_list_local_cons,
 *     assign_tuple_target_list_length — the source writes
 *   lookup_scopes_write_local_type — a write keeps every name's type
 *   tuple_store_local_step, tuple_store_locals_grows,
 *     tuple_store_locals_extends — the code of the stores
 *)
Theory tupleLocalStoreProps
Ancestors
  list rich_list finite_map pred_set stmtSimAssignStore stmtSimDeclMem
  stmtLowering emitHelperProps exprLoweringProps vyperInterpreter vyperLookup
  vyperState vyperValue compileEnv emitHelper fragExec

Theorem assign_tuple_target_local:
  !cx id v es res es'.
    assign_tuple_targets cx (BaseTarget (NameTarget id)) v es = (res, es') /\
    (!m. res <> INR (Error (TypeError m))) ==>
    ?pre env entry rest.
      find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
      res = INL () /\
      es' = es with scopes :=
              pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) ::
              rest
Proof
  cheat
QED

Theorem assign_tuple_target_list_length:
  !gs cx vs es es'.
    assign_tuple_target_list cx gs vs es = (INL (), es') ==>
    LENGTH gs = LENGTH vs
Proof
  cheat
QED

Theorem lookup_scopes_write_local_type:
  !id sc pre env entry rest v n e'.
    find_containing_scope id sc = SOME (pre, env, entry, rest) /\
    lookup_scopes n
      (pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) =
      SOME e' ==>
    ?e. lookup_scopes n sc = SOME e /\ e.type = e'.type
Proof
  cheat
QED

Theorem tuple_store_local_step:
  !cenv ty tys id ids op ops st st' p sz vt.
    compile_tuple_store_all cenv (ty::tys)
      (BaseTarget (NameTarget id) :: MAP (BaseTarget o NameTarget) ids)
      (op::ops) st = ((), st') /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vt /\
    (is_word_type vt = is_word_type ty) ==>
    ?sm. (if is_word_type ty then emit_void MSTORE [Var p; op]
          else compile_store_memory cenv op (Var p) vt ty) st = ((), sm) /\
         compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids)
           ops sm = ((), st')
Proof
  cheat
QED

Theorem tuple_store_locals_grows:
  !ids tys ops cenv st st'.
    compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids) ops
      st = ((), st') /\
    (!i. i < LENGTH ids /\ i < LENGTH tys ==>
       ?p sz vt. FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) sz) /\
         cenv.ce_var_type (EL i ids) = SOME vt /\
         (is_word_type vt = is_word_type (EL i tys)) /\
         (~is_word_type vt ==> vt = EL i tys \/ is_bytestring_type vt)) ==>
    cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var
Proof
  cheat
QED

Theorem tuple_store_locals_extends:
  !ids tys ops cenv st st'.
    compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids) ops
      st = ((), st') /\
    (!i. i < LENGTH ids /\ i < LENGTH tys ==>
       ?p sz vt. FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) sz) /\
         cenv.ce_var_type (EL i ids) = SOME vt /\
         (is_word_type vt = is_word_type (EL i tys)) /\
         (~is_word_type vt ==> vt = EL i tys \/ is_bytestring_type vt)) ==>
    cs_extends st st'
Proof
  cheat
QED

Theorem assign_tuple_target_list_local_cons:
  !cx id ids v vs es es'.
    assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) (id::ids))
      (v::vs) es = (INL (), es') ==>
    ?pre env entry rest es1.
      find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
      es1 = es with scopes :=
        pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest /\
      assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) ids) vs es1 =
        (INL (), es')
Proof
  cheat
QED
