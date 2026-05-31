# LEARNINGS_type_system_rewrite

Reusable proof patterns only. Greppable structured entries; evidence refs point to episodes/tool outputs/source.

## L0001 scope='C1.1' tags=ExtCall,Resume,boundary_lemma,holbuild-timeout,monadic-continuation
shape: ExtCall Resume proof after `Once evaluate_def` exposes full `case INL vs of ... do ...` continuation and generated IHs
pattern: Do not prove ExtCall directly inside the suspended mutual Resume. First add standalone local boundaries: one wrapper from record-updated state to `extcall_return_tail_sound`, then an `extcall_expr_sound_from_generated_ih` helper. The final Resume should only select the args/driver IHs and apply the helper.
works_when: Applies to `eval_all_type_sound_mutual[Expr_Call_ExtCall]` and similar call-target branches where holbuild timeouts occur on broad simplification of a monadic evaluator continuation.
evidence:
- episode:E0002
- tool_output:TO_type_system_rewrite-20260531T201026Z_m0007_t001
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0040_t001

## L0002 scope='C1.1.1' tags=runtime_consistent,record-update,extcall_return_tail_sound,update_accounts_transient
shape: Need ExtCall result after `base_st with <| accounts := accounts'; tStorage := tStorage' |>`
pattern: Bridge the post-run external-call state by deriving `runtime_consistent env cx (base_st with <| accounts := accounts'; tStorage := tStorage' |>)` from `runtime_consistent env cx base_st` and `accounts_well_typed accounts'` via `update_accounts_transient_runtime_consistent`, then apply `extcall_return_tail_sound` unchanged to the supplied return-tail equation.
works_when: The return data path is already isolated as `(if returnData=[] /\ IS_SOME drv then eval_expr cx (THE drv) else do ... od) updated_st = (res,st')` and the caller has driver typing/IH premises.
evidence:
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0040_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:9561-9594
