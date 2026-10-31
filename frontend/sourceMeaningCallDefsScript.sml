Theory sourceMeaningCallDefs
Ancestors
  sourceMeaningProgramDefs sourceMeaningStmtDefs sourceMeaningDefs sourceMeaningValue sourceModuleDecl
  sourceModuleEnv sourceModuleDefs sourceTypeDefs sourceSyntax sourceConstValue
  vyperInterpreter vyperState vyperContext vyperAST vyperValue alist list

(* Independent source declaration meanings. Function selection uses original
   names/decorators; defaults and bodies have source derivations, not code chosen
   from the elaborator. Public auto-getters and imported dispatch are not rules
   of this scalar, single-module instance. *)
Datatype:
  source_declaration_meaning =
    SDM_Function function_visibility function_mutability bool bool string (argument list)
      (source_meaning list) type (source_body_meaning list)
  | SDM_Constant string type literal
  | SDM_Aggregate string type source_const_value
End

Definition source_meaning_default_sources_def:
  source_meaning_default_sources types ctx params originals meanings <=>
    LIST_REL (\(ty,e) m. source_meaning_source types ctx.sm_scopes ctx.sm_table
      ctx.sm_constants ty e m)
      (ZIP (MAP SND (DROP (LENGTH params - LENGTH originals) params),originals)) meanings
End

Definition source_meaning_parameter_types_def:
  source_meaning_parameter_types ctx name args params =
    FOLDL (\types (arg,id,ty). (ctx.sm_owner ++ [name;id],ty)::types)
      [] (ZIP (args,params))
End

Inductive source_meaning_declaration:
[function:]
  source_module_decorators decorators = SM_Ok ds /\
  ~MEM (SX_Name "abstract") decorators /\
  source_module_args ctx args = SM_Ok params /\
  LENGTH defaults <= LENGTH args /\ ALL_DISTINCT (MAP FST params) /\
  source_module_return_type ctx return_annotation = SM_Ok ret /\
  source_meaning_default_sources [] ctx params defaults dms /\
  EVERY (\(arg,id,ty). case arg of SourceArg ignored (SOME a) =>
    source_module_interface_fields ctx a = NONE | _ => T) (ZIP (args,params)) /\
  source_meaning_bodies (source_meaning_parameter_types ctx name args params)
    (source_module_function_context ctx name args params)
    ret body bms next_types next ==>
  source_meaning_declaration ctx
    (SD_Function name decorators args defaults return_annotation body)
    (SDM_Function (source_module_visibility ds) (source_module_mutability ds)
      (MEM "nonreentrant" ds) (MEM "raw_return" ds) name params dms ret bms)
[constant:]
  source_module_resolve_type ctx annotation = SM_Ok resolution /\
  source_type_vtype resolution = Type ty /\
  MEM SCQ_Constant (source_type_qualifiers resolution) /\
  ~MEM SCQ_Public (source_type_qualifiers resolution) /\
  ~MEM SCQ_Indexed (source_type_qualifiers resolution) /\
  source_meaning_source [] ctx.sm_scopes ctx.sm_table ctx.sm_constants ty original
    (SM_Literal ty lit) ==>
  source_meaning_declaration ctx (SD_Variable name annotation (SOME original))
    (SDM_Constant name ty lit)
[aggregate:]
  source_module_resolve_type ctx annotation = SM_Ok resolution /\
  source_type_vtype resolution = Type ty /\
  MEM SCQ_Constant (source_type_qualifiers resolution) /\
  ~MEM SCQ_Public (source_type_qualifiers resolution) /\
  ~MEM SCQ_Indexed (source_type_qualifiers resolution) /\
  source_meaning_stage ctx.sm_scopes ctx.sm_table ctx.sm_constants original (SC_Value sv) /\
  source_const_value_literal sv = NONE ==>
  source_meaning_declaration ctx (SD_Variable name annotation (SOME original))
    (SDM_Aggregate name ty sv)
End

Definition source_meaning_module_def:
  source_meaning_module ctx syntax meanings <=>
    LIST_REL (source_meaning_declaration ctx) (source_module_declarations syntax) meanings
End

Definition source_meaning_lookup_def:
  source_meaning_lookup name Deploy [] =
    SOME (Payable,F,[],[],NoneT,[]) /\
  source_meaning_lookup name vis [] = NONE /\
  source_meaning_lookup name vis
    (SDM_Function fv mut nr raw id params dms ret bms::rest) =
      (if id = name /\ vis = fv then SOME (mut,nr,params,dms,ret,bms)
       else source_meaning_lookup name vis rest) /\
  source_meaning_lookup name vis (SDM_Constant id ty lit::rest) =
    source_meaning_lookup name vis rest /\
  source_meaning_lookup name vis (SDM_Aggregate id ty sv::rest) =
    source_meaning_lookup name vis rest
End

Definition source_meaning_defaults_def:
  source_meaning_defaults cx am [] = SOME [] /\
  source_meaning_defaults cx am (m::ms) =
    case FST ((do
      result <- source_meaning_eval cx (\p. source_meaning_local (LAST p)) m;
      read_result cx result
    od) (initial_state am [FEMPTY])) of
      INL v => OPTION_MAP (CONS v) (source_meaning_defaults cx am ms)
    | _ => NONE
End

(* Runtime constants are installed from source scalar denotations. No runtime
   expression evaluator or constant dependency resolver occurs in this phase. *)
Definition source_meaning_globals_def:
  source_meaning_globals tenv [] acc = SOME acc /\
  source_meaning_globals tenv (SDM_Constant id ty lit::rest) acc =
    (case evaluate_type tenv ty of NONE => NONE
     | SOME tv => source_meaning_globals tenv rest (acc |+ (id,(tv,evaluate_literal lit)))) /\
  source_meaning_globals tenv (SDM_Aggregate id ty sv::rest) acc =
    (case (evaluate_type tenv ty,source_meaning_value tenv ty sv) of
       (SOME tv,SOME v) => source_meaning_globals tenv rest (acc |+ (id,(tv,v)))
     | _ => NONE) /\
  source_meaning_globals tenv (SDM_Function fv mut nr raw id ps ds ret ss::rest) acc =
    source_meaning_globals tenv rest acc
End

Definition source_meaning_install_def:
  source_meaning_install cx am meanings =
    OPTION_MAP (\cenv. merge_constants cx.txn.target NONE cenv am)
      (source_meaning_globals (get_tenv cx) meanings FEMPTY)
End

(* The call protocol shares store/type/lock/value-transfer primitives with the
   runtime, but evaluates independent source defaults and body denotations.
   Both ordinary calls and constructors (including the synthetic empty one)
   use it. Return casts, errors, rollback and request traces are preserved. *)
Definition source_meaning_invoke_def:
  source_meaning_invoke orc am cx meanings nr mut all_mods args dms vals bms ret =
  let all_tenv = type_env_all_modules all_mods in
  let n_missing = LENGTH args - LENGTH vals in
  if LENGTH vals > LENGTH args \/ n_missing > LENGTH dms then
    (INR $ Error (RuntimeError "call args length"),am,[])
  else case source_meaning_defaults cx am (DROP (LENGTH dms - n_missing) dms) of
    NONE => (INR $ Error (RuntimeError "call evaluate_defaults"),am,[])
  | SOME dflt_vs =>
    case bind_arguments all_tenv args (vals ++ dflt_vs) of
      NONE => (INR $ Error (RuntimeError "call bind_arguments"),am,[])
    | SOME env =>
    case (if cx.in_deploy then source_meaning_install cx am meanings else SOME am) of
      NONE => (INR $ Error (RuntimeError "call constants_env"),am,[])
    | SOME am_c =>
    let st = initial_state am_c [env] with <| outcomes := orc; requests := [] |> in
    let is_view = (mut = View \/ mut = Pure) in
    let lock_action = if nr then
      case cx.nonreentrant_slot of
        NONE => raise (Error (TypeError "nonreentrant slot missing"))
      | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
      else return () in
    let unlock_action = if nr /\ ~is_view then
      case cx.nonreentrant_slot of NONE => return ()
      | SOME slot => release_nonreentrant_lock cx.txn.target slot
      else return () in
    case do lock_action; send_call_value mut cx;
            source_meaning_execute cx bms od st of
      (INL (),st) =>
        (case unlock_action st of
          (INL (),st) => (INL NoneV,
            abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st,st.requests)
        | (INR e,st) => (INR e,am,st.requests))
    | (INR (ReturnException v),st) =>
        (case unlock_action st of
          (INL (),st) =>
            (case evaluate_type all_tenv ret of
              NONE => (INR (Error (TypeError "eval ret")),am,st.requests)
            | SOME tv => case safe_cast tv v of
                NONE => (INR (Error (TypeError "ext cast ret")),am,st.requests)
              | SOME v => (INL v,
                  abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st,st.requests))
        | (INR e,st) => (INR e,am,st.requests))
    | (INR e,st) => (INR e,am,st.requests)
End
