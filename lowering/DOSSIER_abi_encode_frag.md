# DOSSIER: abi_encode_frag

PLAN: `lowering/PLAN_abi_encode_frag.md`

## Component Index

| Component | Status | Diagnosis | Latest Episode | Next |
|---|---|---|---|---|
| C1.1 | proved |  | E0002 |  |
| C1.2 | proved |  | E0005 |  |

## C1.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0002`
- blocker: 
- actual effort: 1 sessions, 9 steps, 8 tools, 3 holbuild, 777,170 tok (776,338 in, 832 out, 766,208 cached), 95.7s, $0.1052008

### Attempts / Evidence

- `E0001` (proved, , actual effort: 1 sessions, 3 msgs, 58 steps, 57 tools, 17 holbuild, 3,895,225 tok (3,889,860 in, 5,365 out, 3,803,520 cached), 924.8s, $0.6066820)
  - Plan inversion via generated abi_enc_plan_cases, list induction for sizes/head lengths, static encoding length from memory boundary, enc_tuple_append for cons and dynamic-array layout -> Added checked abi_enc_plans_nil/cons, abi_enc_plans_memory_sizes (map equality, stronger than sum), abi_enc_plan_static, abi_enc_plans_head_lengths (arbitrary accumulator), val_in_memory_static_enc_length, enc_tuple_cons_parts, enc_tuple_nil, enc_dynarray_parts/payload. Existing generated cases supply all constructor inversions. Standard LENGTH_DROP gives payload subtraction identity; static length boundary uses val_in_memory available from enc_pre. (`TO_abi_encode_frag-20261024T233520Z_m0059_t001`)
- `E0002` (proved, , actual effort: 1 sessions, 9 steps, 8 tools, 3 holbuild, 777,170 tok (776,338 in, 832 out, 766,208 cached), 95.7s, $0.1052008)
  - Search exported contractABI theorem names and inspect head_lengths_leq_LENGTH_enc_tuple -> Existing general bound exactly subsumes requested repair: forall ts vs hl tl hds tls n. has_types ts vs ==> head_lengths ts n + SUM (MAP LENGTH hds) <= n + LENGTH (enc_tuple hl tl ts vs hds tls). Set n=0,hds=[],tls=[]; no duplicate added. Removed diagnostic prints and rebuilt. (`TO_abi_encode_frag-20261024T233520Z_m0068_t001`, `TO_abi_encode_frag-20261024T233520Z_m0070_t001`)

### Evidence refs

- `TO_abi_encode_frag-20261024T233520Z_m0068_t001` (use `read_tool_output` for exact output)
- `TO_abi_encode_frag-20261024T233520Z_m0070_t001` (use `read_tool_output` for exact output)

## C1.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0005`
- blocker: 
- actual effort: 1 sessions, 8 steps, 7 tools, 4 holbuild, 450,283 tok (449,739 in, 544 out, 438,912 cached), 68.6s, $0.0709852

### Attempts / Evidence

- `E0003` (progressed, missing_helper, actual effort: 1 sessions, 3 msgs, 45 steps, 44 tools, 13 holbuild, 4,675,429 tok (4,670,323 in, 5,106 out, 4,607,104 cached), 364.4s, $0.6382084)
  - Prove general subregion, scratch allocation, tuple append/EL, homogeneous EL and pointwise padded memory boundaries -> Target builds. Added enc_pre_bounds, regions_disjoint_subregions, enc_scratch_alloca_bound/outside_disjoint, tuple_in_memory_append/EL, elems_in_memory_EL, mem_bytes_at_pointwise and val_in_memory_pointwise. Last preservation boundary requires val_wf as the library interface does. No new cheats. (`TO_abi_encode_frag-20261024T233520Z_m0122_t001`)
- `E0004` (progressed, other, actual effort: 1 sessions, 3 msgs, 29 steps, 28 tools, 9 holbuild, 3,745,427 tok (3,742,132 in, 3,295 out, 3,561,856 cached), 188.9s, $0.7496876)
  - Implement strategist's mutual value_has_type-to-val_wf induction, typed byte-preservation corollary, then enc_frame source boundary -> Typing bridge and typed pointwise corollary verified through builds. Frame proof at lines 1172-1191 is nearly complete but currently fails at arithmetic leaf: paired lambda has not beta-reduced before decide_tac. Need simplify pair application before arithmetic. No new cheats; main theorem remains untouched. C1.1 stable progress already committed as 53318170; C1.2 remains uncommitted until target builds. (`TO_abi_encode_frag-20261024T233520Z_m0140_t001`, `TO_abi_encode_frag-20261024T233520Z_m0151_t001`)
- `E0005` (proved, , actual effort: 1 sessions, 8 steps, 7 tools, 4 holbuild, 450,283 tok (449,739 in, 544 out, 438,912 cached), 68.6s, $0.0709852)
  - Finish enc_frame_preserves_source with targeted disjointness rewriting, simp[] for paired beta normalization, and arithmetic; retain checked typing and extraction boundaries. -> abiEncoderPropsTheory builds successfully; source preservation and all requested C1.2 boundaries proved without new cheats. (`TO_abi_encode_frag-20261024T233520Z_m0164_t001`)

### Evidence refs

- `TO_abi_encode_frag-20261024T233520Z_m0164_t001` (use `read_tool_output` for exact output)
