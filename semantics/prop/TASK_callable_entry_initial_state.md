# TASK: Callable entry establishes type-soundness preconditions

## Meta
Status: planned
Priority: P0
Created: 2026-06-03
Location: semantics/prop

## Theorem Statement (FROZEN)

```sml
Theorem callable_entry_establishes_type_soundness_preconditions:
  functions_well_typed cx /\
  context_well_typed cx /\
  machine_well_typed am /\
  current_module cx = src /\
  fn_sigs_consistent fn_sigs cx /\
  fn_sigs_complete fn_sigs cx /\
  global_maps_consistent cx bare_globals toplevel_vtypes flag_members /\
  immutables_ready bare_globals toplevel_vtypes cx am.immutables /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (fm,nr,args,dflts,ret,body) /\
  bind_arguments (get_tenv cx) args vals = SOME scope /\
  args_values_typed (get_tenv cx) args vals ==>
  ?env_body env_after st.
    st = initial_state am [scope] /\
    accounts_well_typed st.accounts /\
    state_well_typed st /\
    env_consistent env_body cx st /\
    type_stmts env_body ret body = SOME env_after
Proof
  cheat
QED
```

Supporting definitions:

```sml
Definition machine_well_typed_def:
  machine_well_typed (am:abstract_machine) <=>
    accounts_well_typed am.accounts /\
    EVERY (\(addr, imms). imms_well_typed imms) am.immutables
End

Definition args_values_typed_def:
  args_values_typed tenv (args:(string # type) list) (vals:value list) <=>
    LENGTH args = LENGTH vals /\
    !i tv.
      i < LENGTH args /\
      evaluate_type tenv (SND (EL i args)) = SOME tv ==>
      value_has_type tv (EL i vals)
End

Definition global_maps_consistent_def:
  global_maps_consistent cx bare_globals toplevel_vtypes flag_members <=>
    (!src id ty. FLOOKUP bare_globals (src,id) = SOME ty ==>
       ?ts. get_module_code cx src = SOME ts /\
            FLOOKUP toplevel_vtypes (src,id) = SOME (Type ty) /\
            is_immutable_decl id ts /\
            find_var_decl_by_num id ts = NONE /\
            ty <> NoneT) /\
    (!src id vt ts.
       FLOOKUP toplevel_vtypes (src,id) = SOME vt /\
       get_module_code cx src = SOME ts ==>
       ((?ty. vt = Type ty /\
          ((!is_transient typ id_str.
              find_var_decl_by_num id ts =
                SOME (StorageVarDecl is_transient typ,id_str) ==> typ = ty) /\
           (!is_transient kt hv id_str.
              find_var_decl_by_num id ts =
                SOME (HashMapVarDecl is_transient kt hv,id_str) ==> F) /\
           (find_var_decl_by_num id ts = NONE ==>
              IS_SOME (evaluate_type (get_tenv cx) ty)))) \/
        (?kt hv. vt = HashMapT kt hv /\
           ?is_transient id_str.
             find_var_decl_by_num id ts =
               SOME (HashMapVarDecl is_transient kt hv,id_str)))) /\
    (!src fid ls.
       FLOOKUP flag_members (src,fid) = SOME ls ==>
       ?ts. get_module_code cx src = SOME ts /\
            lookup_flag fid ts = SOME ls /\
            FLOOKUP (get_tenv cx) (string_to_num fid) =
              SOME (FlagArgs (LENGTH ls)))
End

Definition immutables_ready_def:
  immutables_ready bare_globals toplevel_vtypes cx imms <=>
    (!src id ty. FLOOKUP bare_globals (src,id) = SOME ty ==>
       IS_SOME (FLOOKUP
         (get_source_immutables src
           (case ALOOKUP imms cx.txn.target of SOME m => m | NONE => []))
         id)) /\
    (!src id ty tv v.
       FLOOKUP bare_globals (src,id) = SOME ty /\
       FLOOKUP
         (get_source_immutables src
           (case ALOOKUP imms cx.txn.target of SOME m => m | NONE => []))
         id = SOME (tv,v) ==>
       evaluate_type (get_tenv cx) ty = SOME tv) /\
    (!src id ty ts.
       FLOOKUP toplevel_vtypes (src,id) = SOME (Type ty) /\
       get_module_code cx src = SOME ts ==>
       (!is_transient typ id_str.
          find_var_decl_by_num id ts =
            SOME (StorageVarDecl is_transient typ,id_str) ==> typ = ty) /\
       (!is_transient kt vt id_str.
          find_var_decl_by_num id ts =
            SOME (HashMapVarDecl is_transient kt vt,id_str) ==> F) /\
       (find_var_decl_by_num id ts = NONE ==>
        !tv v.
          FLOOKUP
            (get_source_immutables src
              (case ALOOKUP imms cx.txn.target of SOME m => m | NONE => []))
            id = SOME (tv,v) ==>
          evaluate_type (get_tenv cx) ty = SOME tv))
End
```

Also prove the corollaries in the same file:

```sml
Theorem callable_entry_no_type_error:
  functions_well_typed cx /\
  context_well_typed cx /\
  machine_well_typed am /\
  current_module cx = src /\
  fn_sigs_consistent fn_sigs cx /\
  fn_sigs_complete fn_sigs cx /\
  global_maps_consistent cx bare_globals toplevel_vtypes flag_members /\
  immutables_ready bare_globals toplevel_vtypes cx am.immutables /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (fm,nr,args,dflts,ret,body) /\
  bind_arguments (get_tenv cx) args vals = SOME scope /\
  args_values_typed (get_tenv cx) args vals ==>
  no_type_error_eval (eval_stmts cx body (initial_state am [scope]))
Proof
  cheat
QED

Theorem type_soundness_preconditions_satisfiable:
  ?cx am env_body env_after st.
    functions_well_typed cx /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    state_well_typed st /\
    env_consistent env_body cx st /\
    type_stmts env_body NoneT [] = SOME env_after
Proof
  cheat
QED
```

**Do not modify these statements.** Prove them as-is, or produce a counterexample.

(*
 ************************************************************
 * DO NOT START THIS PROOF until you have finished and
 * validated ALL the machinery you will need for it.
 * Especially machinery that can be generalized and shared
 * between proofs — write it in separate helper files
 * (e.g. <project>Lib.sml, <project>Script.sml) and
 * holbuild it first.
 *
 * Building generic, powerful abstractions (lemmas, tactics,
 * conversions, decision procedures) that help this proof
 * IS explicitly in scope — even if they take significant
 * effort. They amortize across the project.
 ************************************************************
 *)

## Completion Criteria

1. `holbuild` in `semantics/prop/` passes with zero CHEAT warnings and zero FAILs.
2. No duplicate or near-duplicate lemmas — each helper should exist once in its most general form.
3. `semantics/prop/vyperTypeInitialStateScript.sml` contains no `cheat` in the final proofs.

**If the theorem is false as stated:**
- Produce a HOL4 counterexample (e.g., `EVAL_TAC` on concrete values).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild build vyperTypeInitialStateTheory
```

## Commits

If you make commits to save progress at appropriate points, use --no-gpg-sign to avoid getting stuck with signature password prompt.

## Background

This task addresses #282. The existing type-soundness theorem for statements requires runtime preconditions such as `state_well_typed`, `env_consistent`, and `type_stmts ... = SOME ...`. This task proves that those preconditions are established at a generic callable-function entry point from independently meaningful setup assumptions: a well-typed context and machine, consistent static global maps, initialized immutables/constants, successful argument binding, and typed argument values.

The theorem intentionally works at a generic callable-entry level and assumes `current_module cx = src`. Integration with the concrete top-level `call_external`/`load_contract` entrypoints is separate follow-up work for #308.

## Domain Constraints

- This is HOL4 proof work in the vyper-hol repository. Follow the project HOL4 script style.
- Do not replace existing proofs with `cheat`. Remove the cheats introduced in `vyperTypeInitialStateScript.sml` by proving them.
- Use `holbuild`; do not use deprecated interactive MCP/HOL workflows.
- Keep helper lemmas reusable and general where practical.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| New target theory | `semantics/prop/vyperTypeInitialStateScript.sml` | Contains the cheated statements to prove. |
| Type system definitions | `semantics/prop/vyperTypeSystemScript.sml` | Defines `functions_well_typed`, `env_consistent`, `env_context_consistent`, `env_scopes_consistent`, `env_immutables_consistent`, `state_well_typed`, `scope_well_typed`, `type_stmts`, etc. |
| Public soundness surface | `semantics/prop/vyperTypeSoundnessScript.sml` | Contains `typed_stmts_no_type_error` and related public theorem wrappers. |
| Statement soundness | `semantics/prop/vyperTypeStmtSoundnessScript.sml` | Existing large proof; includes local lemmas that may inspire exported reusable variants, especially around `bind_arguments` and callable bodies. |
| Call soundness helpers | `semantics/prop/vyperTypeCallSoundnessScript.sml` | Contains `functions_well_typed_body` and call-related theorem shapes. |
| Interpreter definitions | `semantics/vyperInterpreterScript.sml` | Defines `bind_arguments`, `initial_state`, `call_external_function`, `call_external`, `load_contract`, and `abstract_machine`. |
| Context definitions | `semantics/vyperContextScript.sml` | Defines `get_tenv`, `get_module_code`, `current_module`, type environments, and source/module helpers. |
| Runtime typing | `semantics/prop/vyperTypingScript.sml` | Defines/proves runtime value typing facts such as `default_value_well_typed`, `safe_cast_well_typed`, `safe_cast_preserves_well_typed`. |
| Tests/top-level usage | `tests/vyperTestRunnerScript.sml` | Shows practical use of `call_external`, `load_contract`, `compute_vyper_args`, and trace execution. |
| Project proof lessons | `docs/HOL4_PROOF_CONTROL_LESSONS.md` | Project-specific proof engineering guidance. |
| Agent guide | `AGENTS.md` | Repository-specific proof/build/tooling instructions. |

## Notes

The main theorem is meant to be the generic callable-entry bridge. It does not try to prove that `call_external` sets `current_module` correctly for exported-module calls; that top-level integration is intentionally left for later #308 work.
