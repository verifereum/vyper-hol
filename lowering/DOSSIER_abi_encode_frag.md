# DOSSIER: abi_encode_frag

PLAN: `lowering/PLAN_abi_encode_frag.md`

## Component Index

| Component | Status | Diagnosis | Latest Episode | Next |
|---|---|---|---|---|
| C1.1 | proved |  | E0002 |  |

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
