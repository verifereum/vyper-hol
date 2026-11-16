# Dynamic-entry premises: actual application obstruction

Component C1.5.5.1.e; observation only, not a proved helper or Consumer.

**Status: post-match premise sequent not observed; local_dynamic_entry_premises not extracted.**

The recorded application fails before exposing its antecedent. This package
preserves the actual pre-match goal, not a replacement `dynamic_static` goal.
It does not establish a missing semantic resource, a counterexample to the
frozen TASK, or unprovability. Application and final assembly need a separate
owner/strategist disposition before relying on a post-match helper.

## Public source and byte identities

Input is the integrated C1.5.5.1.a package, not another lane's worktree:

- `bodyFullForArrayLocalCaptureContext/Consumer.reconstructed.txt`, Git blob
  `2970c304716a8db3019f7f0b490e31c98bce8270` (106827 bytes).
- Its base/patch/provenance remain in that same public context directory.
- `bodyFullForArrayLocalContractsScript.sml`, Git blob
  `f363d2c91cc5a2dd39819e6b0359b0224bc4a986`, is unchanged.
- The production `bodyFullForArrayLocalConsumerScript.sml` is absent; it was
  neither restored nor edited for this capture.

The following companion files are **inert data**, never imported theories.
Each name begins `bodyFullForArrayLocalCaptureDynamicEntryPremises.`:

| Suffix | Contents |
| --- | --- |
| `Generator.txt` | Complete byte-identical snapshot of temporary `bodyFullForArrayDynamicCaptureGeneratorScript.sml` (1821 bytes). |
| `Replay.txt` | Complete byte-identical snapshot of temporary `bodyFullForArrayDynamicCaptureReplayScript.sml` (107032 bytes). |
| `RawLog.txt` | Complete persisted typed replay log (69227 bytes), including printing timeout and instrumented full goal. |
| `Types.txt` | Exact bound-contract and live-goal variable type tables from RawLog (2760 bytes). |
| `Sequent.txt` | Exact instrumented pre-match conclusion and **all 268 assumptions**, numbered 0 through 267 (29301 bytes). No assumption is omitted. |
| `SourceChanges.txt` | Human-readable line comparison of public reconstruction and replay; full snapshots are authoritative, not this comparison as a patch. |

`Sequent.txt` is an unedited contiguous slice of `RawLog.txt` beginning
` 0.  dynamic_entry` and ending before `holbuild end failed tactic top input goal`.
`Types.txt` is the contiguous slice beginning `DYNAMIC-CONTRACT-BOUND-TYPES`
and ending immediately before the first `ASSUMPTION` print. Thus the retained
sequent and types can be inspected without the partial duplicate printing.
The raw log's timeout is not a passing prefix qualification.

## Original application and type obstruction

The archived application, public reconstruction lines 2018-2021, is:

```sml
Resume body_for_local_array_full_from_contracts[dynamic_entry_pending]:
  asm "dynamic_entry" match_mp_tac >> simp[mk_inst_def] >>
  capture_goal "dynamic-entry-premises" (* original: FAIL_TAC "dynamic-entry-premises" *)
QED
```

Moved immediately after `dynamic_init` for isolated diagnostic execution, the
first tactic fails with `HOL_ERR`, message `No match`, origin
`Tactic.MATCH_MP_TAC`. The subsequent `simp` and premise capture do not execute.
This is persisted in
`TO_statement_cases-L0051-20261116T223012587493Z_m0021_t001`
(remote batch `d789916f-7b86-4b75-8f8f-68df4883f555`).

The later non-logical type print retains these actual distinctions:

| Variable | In term-universally closed assumed dynamic_entry | In live endpoint goal |
| --- | --- | --- |
| `vs` | `'a list` | `value list` |
| `DF` | `'b -> dead` | `((bool # 256 word # type_value) list # num list) -> dead` |

The complete tables, with every other type, are in `Types.txt`; the printed
alpha/beta characters there are preserved verbatim. Universal closure over
term variables does not make the type variables in an assumed proposition
instantiable while keeping its hypothesis unchanged. In particular,
`INST_TYPE` of that assumption is not a sound way to consume the original
cut at these other types. This diagnoses the recorded matcher application;
it neither changes nor refutes any of the seven quotations or frozen roots.
No monomorphic replacement cut has been introduced.

## Exact endpoint boundary

The exact pretty-printed conclusion is `Sequent.txt` lines 541-554, including
the types supplied separately by `Types.txt`. Its ASCII rendering for navigation
only is:

```sml
?dst cc s1.
  exec_alloca (mk_inst (start.cs_next_id + 1) ALLOCA
    [Lit (n2w (type_memory_size tv))] [p])
    (update_var lv (n2w (LENGTH vs)) s0) (n2w (type_memory_size tv)) = OK s1 /\
  s1 = sA /\
  cc = jump_to cond (update_var vld 1w (update_var g 0w
    (update_var idx 0w (jump_to entry' s1)))) /\
  array_loop_inv ctx func cenv cx st0 (expr_sim_inv cenv cx env)
    vs id idx (Var ap) base' p dst (type_memory_size tv)
    (mk_inst (start.cs_next_id + 1) ALLOCA
      [Lit (n2w (type_memory_size tv))] [p]) cond start 0 es cc /\
  lookup_var lv cc = SOME (n2w (LENGTH vs)) /\
  array_caller_frame start s0 cc /\
  gas_marked_path F ctx func s0 0 (OK cc) /\
  gas_path_mem ctx func s0 0 (OK cc) /\
  alloca_history func cc /\ cc.vs_memory = s0.vs_memory /\
  s0.vs_alloca_next <= cc.vs_alloca_next /\
  !H. gas_origin_ptr_path
    (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (s0,G0,tn0) [] (OK cc,Gf,tf)
```

This is an **unproved goal**, not a helper declaration. The existential endpoint
and ghosts have not been independently selected under H or merged from
separate executions.

## Observational premise map (not an extracted helper)

Numbers below refer to the complete `Sequent.txt` assumption numbering. This
map identifies where the actual static and initialized-state material sits;
it does not assert sufficiency, necessity/minimality, or discharged antecedents
for an application that did not match.

| Material | Actual assumptions / source location |
| --- | --- |
| Assumed contract, not proved supplier | 0, the labelled `dynamic_entry` proposition; its types are above. |
| Source typing/iterator and root contracts | 1-32; `vs : value list`, source scope entry/type and length facts. |
| Actual ordinary/shadow root compilation | 33-43 and 66; distinct starts/finishes, `gas_shadow_state` and `fn_has_code`. |
| Initial runtime/ghost/frame resources | 44-59; arbitrary `lo`, `ret_pc_ok`, history, conditional allocation, no-wrap, all-H state relation and storage domain. No alloca_inv-only room inference. |
| Compiler size and stages | 60-74, 88-144; actual root/dynamic stage equations, body ordinary/shadow input/output at 130-134. No substitute code_ready witness or state identification. |
| Generated names, freshness, register facts | 75-87 and 145-204; including distinct registers and preserved old names. |
| MLOAD equation, then unresolved stage fields | 205 and 206-211 respectively. See suspension below; fields are not independently proved. |
| Allocation compilation and concrete code | 212-217, 222, 223; allocation buffer, fn_has_code and block lookup. |
| Valid horizon and bounds | 218-221; actual horizon witness, return-pc freshness and `LENGTH vs <= n'`, `n' < dimword (:256)`. |
| Conditional prefix result | 224-249; selected allocation endpoint, memory/history/frame/ghost facts and pointer paths, conditional on the retained unresolved fields and assumed cuts. |
| Abbreviations | 250 (`vs`) and 251 (`sA = t with vs_inst_idx := s0.vs_inst_idx`). |
| Re-expressed allocation and initial register | 252-255. |
| ASSIGN/GT/ISZERO/ASSERT initialized path | 256-267; initialized ghosts/taints, unchanged memory taint components and all-H instruction sequences. |

No unrelated assumptions have been silently discarded from the data. Some
are likely irrelevant to a future smaller lemma, but dropping them now would
misrepresent the actual failed proof point.

## Replay differences and unresolved prerequisites

`Generator.txt` records the initial deterministic public-archive transformation:
renamed theory, explicit pending MLOAD-equation suspension, and assumption
printing. The generator alone does **not** reproduce the final replay. The
additional edits are all retained in `Replay.txt` and `SourceChanges.txt`:

1. Rename only the temporary theory to avoid publishing a production Consumer.
2. Print assumptions in `capture_goal` for observation only.
3. Replace the failed MLOAD field by-proof with
   `suspend "capture_load_equations"`; this remains unresolved.
4. Replace the redundant MLOAD equality's global `simp[]` with a proof consuming
   just `emit_op MLOAD ... = ...` and `load_result = Var lv`, clearing irrelevant
   assumptions before `metis_tac[]`.
5. Move `dynamic_entry_pending` before unrelated later Resumes; first attempt
   the original matcher (m0021), then replace it with the bound-variable type
   print and `capture_goal "dynamic-entry-pre-match"` (final replay snapshot).

The precise unresolved conjunction at `Replay.txt` lines 1542-1548 is:

```sml
load_result = Var lv /\
load_cs.cs_current_bb = start.cs_current_bb /\
load_cs.cs_current_insts = start.cs_current_insts ++
  [mk_inst start.cs_next_id MLOAD [Var ap] [lv]] /\
load_cs.cs_blocks = start.cs_blocks /\
load_cs.cs_next_id = start.cs_next_id + 1 /\
load_cs.cs_next_var = start.cs_next_var + 1
```

These fields appear as assumptions 206-211 in the conditional continuation.
They are NOT accepted facts. Original unresolved branches, FAIL_TACs and
suspensions elsewhere are also preserved byte-for-byte except for the changes
listed above. The unreachable `Finalise` at the end of the snapshot does not
make an unfinished theory a registered theorem. No replay theorem is delivered.

The all-assumption printer exceeded the ordinary 2.5s tactic limit after
printing the useful type table and part of its duplicate assumption list.
The instrumentation nevertheless retained the entire numbered goal. No timeout
override, admission, failed-cone retry or Consumer qualification is warranted.

## Preservation execution and final audit

A temporary empty arithmetic-only `bodyFullForArrayDynamicCaptureArchiveCopy`
utility read both temporary scripts and the existing public log as declared
inputs. It copied/read back the five raw artifacts byte-for-byte, extracted
only contiguous log slices, and generated the sixth human-readable comparison.
It separately compared all seven quotation blocks and the complete theorem
header (through `Proof`) between public reconstruction and replay. All were
identical. It introduced no theorem, assumption, definition or proof rule.

Ordinary utility build passed at project defaults:
`TO_statement_cases-L0051-20261116T225314472881Z_m0045_t001`;
its execution output is
`TO_statement_cases-L0051-20261116T225314472881Z_m0046_t003`.
The initial utility invocation rejected a mistaken private quotation name
before writing outputs; the corrected invocation passed. This utility build
qualifies mechanical preservation only, **not** the replay/Consumer or any
helper theorem. No repeat of the unchanged failing replay was needed.

Staged Git blob identities of the inert artifacts (before publication):

| Suffix | Git blob |
| --- | --- |
| `Generator.txt` | `1131ccf820ea764d7bf0538f6ac67f6194253d7b` |
| `Replay.txt` | `0e45a35969080cc9d4c12b048db3a12540f39c18` |
| `RawLog.txt` | `ee9057d64a45b70ef7a4f68b4f2a70df7043d4df` |
| `Types.txt` | `3cd84c915970edb4a04cae0652ae2521f180eb54` |
| `Sequent.txt` | `a93b30877f13e7c1db8baebf3141224b70c4b3fc` |
| `SourceChanges.txt` | `1325337e8ddb498c24617657943d4602ffe388fd` |

The only `git diff --cached --check` warnings are original RawLog trailing
whitespace at line 1582 and its final blank line; both are deliberately retained
for byte identity, not source-code whitespace changes. The archived Replay
contains no admission constructors. No `.sml` path is staged or modified.

After preservation, all three temporary active `*Script.sml` paths are removed.
Only this markdown and the six inert text companions are published. No
production source, LocalContracts quotation, frozen header, shared provider,
logical definition or admission is changed. The public context package is
untouched. Any future helper and assembled Consumer still require their own
ordinary build and proof-integrity checks.

## Evidence and downstream notice

- E0176: isolated conditional replay and pre-match type obstruction.
- `TO_statement_cases-L0051-20261116T223012587493Z_m0018_t001`: dynamic_init continuation, with explicit pending MLOAD equations.
- `TO_statement_cases-L0051-20261116T223012587493Z_m0021_t001`: actual original matcher, No match before antecedent capture.
- `TO_statement_cases-L0051-20261116T223012587493Z_m0025_t001`: bound/live type tables and full instrumented pre-match goal (RawLog).
- `TO_statement_cases-L0051-20261116T223012587493Z_m0026_t001`: readback of actual initialized-state premises and endpoint.
- `TO_statement_cases-L0051-20261116T225314472881Z_m0032_t001`: strategist disposition to package the obstruction, not invent local_dynamic_entry_premises.

**Notice to C1.5.5.1, the application capture/helper owner and C1.5.5.8:**
this is observation-complete data only. There is no post-match premises helper
to consume and no successful dynamic-entry application. Those consumers need
a separate supported strategic disposition of the actual application before
relying on it. This leaf neither changes their PLAN nor transfers ownership;
its diagnostic completion supplies no proof credit for their open obligations.
