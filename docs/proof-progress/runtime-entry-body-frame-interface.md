# Runtime entry body-frame interface diagnostic (C1.1.2)

This is a diagnostic receipt, **not** proof credit for the runtime consumer or
for either S1 target. No frozen header, executable definition, frame predicate,
or entry certificate was changed. The implementation remains owned by C1.1.3.

## Evidence and scope

- Initial receiving build: `holbuild(["selectedExternalTraceBodyTheory",
  "loweringRuntimeCorrectTheory"], timeout=3600)` fails in
  `runtime_body_joint_from_start_with_shadow`, at the call of
  `drule_all (INST_TYPE [alpha |-> ``:expr``] external_body_frame)`.
  Evidence: `TO_seq3861_calldata_family-L0014-20261116T153551883017Z_m0003_t001`.
  There are **two** input goals. The displayed first goal is selected; the
  fallback goal is truncated. This output does not establish that the selected
  branch fails to match.
- A separate temporary theory importing `externalBodyFrame`,
  `runtimeEntryEndpoint`, `defaultDispatchFacts`, and `compileVyper` checked the
  selected-branch application below and the same-source package-environment
  projection below. Passing build:
  `TO_seq3861_calldata_family-L0014-20261116T153551883017Z_m0016_t001`.
  The temporary script is removed, to avoid publishing unused duplicate helpers.
  Both probe statements/proofs are reproduced below for reproducibility.
- Source signatures and field dependencies were inspected in the receiving
  checkout, not inferred from archived donor proofs. In particular,
  `package_fallback_fn_def` **already performs** `update_cenv_ret_abi` for a
  non-None return, just as `package_external_fn_def` does.

## The two complete frame subgoal shapes

Here is the common source/package context, in HOL notation. The use of
`([]:expr list)` is intentional; defaults are polymorphic in packaging.

```sml
lower_vyper_runtime_unit tops rpolicy = SOME unit /\
supported_program tops /\
source_typing_ok tops am tx /\
source_deployment_rel tops am tx /\
initial_venom_state_rel tops am tx vs /\
outcomes_accounts_typed (SOME vs.vs_outcomes) /\
lookup_function NONE tx.function_name External tops =
  SOME (mut,F,args,[],ret,fbody) /\
bind_arguments (type_env tops) args tx.args = SOME env /\
send_call_value mut
  (initial_evaluation_context am.sources am.layouts tx NONE)
  (initial_state am [env] with
    <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es0) /\
set_external_package_target rpolicy.rpol_target
  (package_external_fn tops T (K global_nonreentrant_slot)
    (mut,F,lookup_raw_return_or_F (NONE:num option)
      tx.function_name External tops,
     tx.function_name,args,([]:expr list),ret,fbody)) =
  (lbl,cenv_ext,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt) /\
compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa)
```

In the **selected** subgoal add these assumptions to that context:

```sml
cenv0 = cenv_ext /\
runtime_selected_body_start tops rpolicy
  (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt) st
```

In the **fallback** subgoal instead add:

```sml
tx.function_name = "__default__" /\ args = [] /\
pos_args = [] /\ min_cds = 4 /\
cenv_ext = (if ret <> NoneT then update_cenv_ret_abi cenv0 ret else cenv0) /\
runtime_fallback_body_start tops rpolicy
  (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt) st
```

In **each** case the full required conclusion at the actual registration
output, not at an ABI-updated substitute, is:

```sml
body_inv tops unit.cu_context cenv
  (initial_evaluation_context am.sources am.layouts tx NONE) /\
cenv.ce_return_pc = NONE /\
?bindings env_t env'.
  supported_stmts tops bindings fbody /\
  expr_sim_inv cenv
    (initial_evaluation_context am.sources am.layouts tx NONE) env_t es0 /\
  ce_locals_declared cenv env_t /\ locals_alloc_ok cenv env_t /\
  type_stmts env_t ret fbody = SOME env' /\
  stmts_exprs_ok cenv fbody /\
  call_evaluation_safe
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (int_calls_stmts fbody)
```

These are the isolated frame subgoals, not claims that the original consumer
already states this conjunction as its goal. The original consumer's goal is
`?shadow_unit marks. runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
source_unit_execution_correct_with shadow_unit.cu_context marks tops ret am tx
unit vs`. Its remaining endpoint assumptions supply the same joint execution,
memory and pointer witnesses; none needs altering to solve the frame subgoal.

## Verified selected application

The temporary `selected_branch_frame_probe` universally quantified all variables
above, used the common source/package context plus `cenv0 = cenv_ext`, and
concluded exactly the full frame conjunction displayed above. Its checked proof
was:

```sml
rpt gen_tac >> strip_tac >> gvs[] >>
drule_all (INST_TYPE [alpha |-> ``:expr``] external_body_frame) >> simp[]
```

It needs no selected-placement premise. Thus the selected supplier interface is
adequate after the endpoint equality is eliminated; there is no selected-branch
missing premise established by the initial failed combined application.

## Minimal checked fallback projection

This temporary probe checks the actual definitions, without claiming the
endpoint's two package witnesses have the same source tuple:

```sml
Theorem same_source_fallback_package_environment_probe:
  set_external_package_target target
    (package_external_fn tops use_trans nkeys
      (mut,nr,rr,name,args,([]:expr list),ret,fbody)) =
    (lbl,ce_ext,pa,mc,pay,nr',key,ut,iv,body,rt) /\
  set_fallback_package_target target
    (package_fallback_fn tops use_trans nkeys
      (SOME (mut,nr,rr,name,args,([]:expr list),ret,fbody))) =
    SOME (ce_fb,pay',nr'',key',ut',iv',body',rt') ==>
  ce_fb = ce_ext
Proof
  simp[package_external_fn_def, package_fallback_fn_def,
       set_external_package_target_def, set_fallback_package_target_def] >>
  rpt strip_tac >> gvs[]
QED
```

`Parse.hide "body"` was used in the temporary script. This is a checked
**same-source package** fact, not an unjustified inversion of
`update_cenv_ret_abi`. It covers non-None return types too. The endpoint relation
by itself is not an inverse: the update overwrites three fields. The necessary
extra evidence is already present as fallback provenance in
`runtime_fallback_body_start_def`.

## Supplier signatures and exact provenance still to connect

1. `externalBodyFrame.external_body_frame`: its premises are precisely the common
   context above with `cenv_ext` replaced everywhere by `cenv0`; its conclusion is
   precisely the displayed frame conjunction. No placement premise is required.
2. `runtimeEntryEndpoint.runtime_entry_endpoint_body_projection` takes
   `runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret fbody` and
   existentially packages `lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st
   cenv sa st' func s0 G0 tn0`. It supplies `runtime_entry_body_start`, registration,
   guarded-body compilation and all original joint certificates. It **drops** the
   external-package equation and the distinction between `cenv_ext` and `cenv0`.
   Therefore do not use this projection alone for the proposed frame proof;
   retain the package equation/disjunction from `runtime_entry_endpoint_def`.
3. `runtimeBodyStartDefs.runtime_fallback_body_start_def` supplies
   `classify_functions tops = (exts,ints,SOME fb,ctor)` and
   `set_fallback_package_target rpolicy.rpol_target
      (package_fallback_fn tops T (K global_nonreentrant_slot) (SOME fb)) =
      SOME (cenv0,is_payable,F,nkey,ut',iv,fbody,rt)`.
   It also supplies `pos_args=[]`, `min_cds=4` and the actual compilation
   placement. It does not itself identify the source tuple `fb` with the lookup.
4. `defaultDispatchFacts.default_empty_package_return_layout` takes the external
   package equation with source args `[]`; it returns `pa=[]`, `mc=4`, a fallback
   package **of that same source tuple**, the conditional update equation,
   a restoration equation for the three ABI fields, and
   `ce_fb.ce_vars=FEMPTY`, `ce_fb.ce_module=NONE`, `~ce_fb.ce_is_ctor`,
   `ce_fb.ce_imm_alloca=NONE`, `ce_fb.ce_return_pc=NONE`,
   `ce_fb.ce_return_buf=NONE`. Its `ce_fb` is existential: it must be identified
   with the actual classified fallback before using it in certificates.
5. `externalReturnBuffer.build_compile_env_return_buffer_ok`:
   `!tops vis mut name args ret body use_trans.
      return_buffer_ok (build_compile_env tops vis mut name args ret body use_trans)`.
6. `externalReturnBuffer.external_default_return_buffer_ok` takes lower/supported,
   `tx.function_name="__default__"`, the source lookup, the external package
   equation **at cenv0**, and registration **from that same cenv0**. It concludes
   `stmts_valued_return fbody /\ cenv.ce_is_external /\ ~cenv.ce_raw_return ==>
    return_buffer_ok cenv`.
   It is not an inverse-transport theorem, and cannot directly close the
   mismatch with two distinct package environments.

For source-tuple alignment, the existing non-duplicated interfaces are:

```sml
(* loweringShapeProps.classify_functions_fallback_mem *)
FST (SND (SND (classify_functions tops))) =
  SOME (mut,nr,rr,fname,args,defaults,ret,body) ==>
?rawdefaults rawbody.
  MEM (FunctionDecl External mut nr rr fname args rawdefaults ret rawbody) tops /\
  (mut,nr,rr,fname,args,defaults,ret,body) =
    subst_consts_fn (module_consts_env tops [])
      (mut,nr,rr,fname,args,rawdefaults,ret,rawbody)

(* defaultDispatchFacts.default_decl_raw_return *)
ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
MEM (FunctionDecl External mut nr rr name args ds ret fbody) tops ==>
lookup_raw_return_or_F (NONE:num option) name External tops = rr
```

Use `supported_headers_module_consts_env` with supported headers to make the
substitution empty (`subst_consts_fn_empty`), and source typing's external-name
distinctness with `lookup_function_external_unique_decl` to align the source
lookup and actual fallback declaration. This connection is a **residual proof
obligation**, not part of either checked probe. In particular do not assume a
`__default__`-named source lookup cannot be a getter; name equality alone does not
supply the declaration.

## Field-by-field audit and proof route

`update_cenv_ret_abi_def` writes exactly:

| Field | New value | Observed by the required conjunction? |
| --- | --- | --- |
| `ce_ret_enc_info` | child encoding, possibly ABI tuple wrapped | `stmts_exprs_ok` through `stmt_exprs_ok` / `return_buffer_ok` |
| `ce_ret_dec_info` | child decoding | not directly read by displayed frame predicates |
| `ce_max_return_size` | child bound, possibly plus 32 | `stmts_exprs_ok` through `return_buffer_ok` |

The other fields are preserved. Inspection of `body_inv_def` and
`cenv_module_pins_def` shows no read of these three fields. Inspection of
`expr_sim_inv_def` (including `place_map_tables_agree_on_defined_def` and
`bare_globals_layout`'s explicit field arguments) shows no read of them.
`ce_return_pc` and `ce_locals_declared` read other fields;
`locals_alloc_ok` reads `type_memory_bytes`, whose `type_memory_bytes_frame`
interface depends on struct/flag layout, not these ABI fields.
`alloc_limits_stmt` and its expression/place helpers do not directly read the
three fields either. `supported_stmts`, `type_stmts`, and
`call_evaluation_safe` are independent of the compile environment.
These are source-dependency observations, **not** additional checked universal
transport theorems. In particular `same_frame` is not the right automatic
transport: its definition permits only local-table changes and fixes the ABI
metadata, so it cannot be assumed from the conditional-update relation.

Recommended narrow route: prove source-tuple alignment using actual fallback
placement; apply the checked same-source projection calculation (prefer a small
reusable package boundary if needed); then reuse `external_body_frame` unchanged
at `cenv0`. This establishes equality from package provenance, not from ABI
inversion. It avoids copying the frame proof and avoids separately transporting
return-buffer bounds. An alternative field-transport route would have to prove
`stmts_exprs_ok` transfer with a native fallback return-buffer bound; the existing
default return-buffer theorem alone does not justify it.

## Candidate endpoint-aware boundary header

This is a proposed new theorem, not a modification to an existing statement.
Its conclusion retains the actual registration environment. Both placement arms
are retained for the provenance argument; no valid-call or canonical-calldata
hypothesis is added.

```sml
Theorem runtime_entry_body_frame:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 lbl cenv_ext cenv0 pos_args
   min_cds is_payable nkey ut' iv rt st cenv sa.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut,F,args,[],ret,fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es0) /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
         (mut,F,lookup_raw_return_or_F (NONE:num option)
                     tx.function_name External tops,
          tx.function_name,args,([]:expr list),ret,fbody)) =
      (lbl,cenv_ext,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt) /\
    ((cenv0 = cenv_ext /\
      runtime_selected_body_start tops rpolicy
        (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt) st) \/
     (tx.function_name = "__default__" /\ args = [] /\
      pos_args = [] /\ min_cds = 4 /\
      cenv_ext = (if ret <> NoneT then update_cenv_ret_abi cenv0 ret else cenv0) /\
      runtime_fallback_body_start tops rpolicy
        (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt) st)) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) ==>
    body_inv tops unit.cu_context cenv
      (initial_evaluation_context am.sources am.layouts tx NONE) /\
    cenv.ce_return_pc = NONE /\
    ?bindings env_t env'.
      supported_stmts tops bindings fbody /\
      expr_sim_inv cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) env_t es0 /\
      ce_locals_declared cenv env_t /\ locals_alloc_ok cenv env_t /\
      type_stmts env_t ret fbody = SOME env' /\
      stmts_exprs_ok cenv fbody /\
      call_evaluation_safe
        (initial_evaluation_context am.sources am.layouts tx NONE)
        (int_calls_stmts fbody)
```

No missing premise in an admitted helper was established by this diagnostic.
The residual is connecting existing provenance, not strengthening a frozen
header. No claim of whole-runtime build success is made.
