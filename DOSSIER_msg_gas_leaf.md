# DOSSIER: msg_gas_leaf

PLAN: `PLAN_msg_gas_leaf.md`

## Component Index

| Component | Status | Diagnosis | Latest Episode | Next |
|---|---|---|---|---|
| C1.1 | proved |  | E0001 |  |
| C1.2 | proved |  | E0004 |  |
| C1.3 | proved |  | E0003 |  |
| C1.4 | proved |  | E0005 |  |
| C1.5 | proved |  | E0006 |  |
| C1.6 | proved |  | E0007 |  |

## C1.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0001`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 16 steps, 15 tools, 2 holbuild, 803,681 tok (802,666 in, 1,015 out, 783,232 cached), 1985.1s, $0.1273412

### Attempts / Evidence

- `E0001` (proved, , actual effort: 1 sessions, 1 msgs, 16 steps, 15 tools, 2 holbuild, 803,681 tok (802,666 in, 1,015 out, 783,232 cached), 1985.1s, $0.1273412)
  - Unfold concrete compiler into existential append shape, apply fn_has_code_same_block at zero. -> Placement helper kernel checked; existential instruction identity needed metis rather than simp. (`TO_msg_gas_leaf-20261103T024228Z_m0017_t001`)

### Evidence refs

- `TO_msg_gas_leaf-20261103T024228Z_m0017_t001` (use `read_tool_output` for exact output)

## C1.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0004`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 14 steps, 13 tools, 5 holbuild, 1,160,543 tok (1,158,977 in, 1,566 out, 1,139,328 cached), 451.8s, $0.1688908

### Attempts / Evidence

- `E0002` (stuck, risk_mismatch, actual effort: 1 sessions, 1 msgs, 17 steps, 16 tools, 5 holbuild, 1,067,633 tok (1,065,772 in, 1,861 out, 1,037,952 cached), 500.9s, $0.1780452)
  - Split oracle cases, simplify gas_prefix_suc, witness edge fuel. -> Numeral 1 did not match SUC n, leaving existential w before fuel, hence fuel witness targeted wrong existential. (`TO_msg_gas_leaf-20261103T024228Z_m0029_t001`)
  - Use gas_prefix_def then execution simplification. -> TAKE 1 (REPLICATE 1 0w) not reduced automatically; broad execution simp timed out. (`TO_msg_gas_leaf-20261103T024228Z_m0031_t001`, `TO_msg_gas_leaf-20261103T024228Z_m0033_t001`)
  - Rewrite numeral using arithmeticTheory.ONE with gas_prefix_suc. -> Simplification timed out, likely numeral rewrite loop. Removed experimental helper to restore prior stable source. (`TO_msg_gas_leaf-20261103T024228Z_m0037_t001`)
- `E0004` (proved, , actual effort: 1 sessions, 1 msgs, 14 steps, 13 tools, 5 holbuild, 1,160,543 tok (1,158,977 in, 1,566 out, 1,139,328 cached), 451.8s, $0.1688908)
  - Stage prefix equality and actual step equation in two oracle cases, then construct counted edge at fuel zero. -> Both oracle cases and actual GAS count verified. Removing numeral equality from context after controlled rewrite prevents simplifier loop; empty-oracle unchanged field needs record component equality. (`TO_msg_gas_leaf-20261103T024228Z_m0078_t001`)

### Evidence refs

- `TO_msg_gas_leaf-20261103T024228Z_m0078_t001` (use `read_tool_output` for exact output)

## C1.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0003`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 18 steps, 17 tools, 2 holbuild, 1,336,601 tok (1,335,642 in, 959 out, 1,315,328 cached), 864.0s, $0.1817508

### Attempts / Evidence

- `E0003` (proved, , actual effort: 1 sessions, 2 msgs, 18 steps, 17 tools, 2 holbuild, 1,336,601 tok (1,335,642 in, 959 out, 1,315,328 cached), 864.0s, $0.1817508)
  - Rewrite selected evaluate_def equation, simplify concrete builtin arity and monad/source-event/value-read definitions. -> Full arbitrary-word/arbitrary-tail source helper built at default tactic limit. (`TO_msg_gas_leaf-20261103T024228Z_m0060_t001`)

### Evidence refs

- `TO_msg_gas_leaf-20261103T024228Z_m0060_t001` (use `read_tool_output` for exact output)

## C1.4

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0005`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 8 steps, 7 tools, 3 holbuild, 721,452 tok (720,197 in, 1,255 out, 709,120 cached), 218.9s, $0.1056160

### Attempts / Evidence

- `E0005` (proved, , actual effort: 1 sessions, 1 msgs, 8 steps, 7 tools, 3 holbuild, 721,452 tok (720,197 in, 1,255 out, 709,120 cached), 218.9s, $0.1056160)
  - Combine placement and counted edge; forward chain edge with gas_path rule at m=0. -> Frozen path root built; explicit forward chaining avoided broad metis timeout. (`TO_msg_gas_leaf-20261103T024228Z_m0090_t001`)

### Evidence refs

- `TO_msg_gas_leaf-20261103T024228Z_m0090_t001` (use `read_tool_output` for exact output)

## C1.5

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0006`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 21 steps, 20 tools, 5 holbuild, 2,093,510 tok (2,092,000 in, 1,510 out, 2,055,936 cached), 352.3s, $0.2928216

### Attempts / Evidence

- `E0006` (proved, , actual effort: 1 sessions, 1 msgs, 21 steps, 20 tools, 5 holbuild, 2,093,510 tok (2,092,000 in, 1,510 out, 2,055,936 cached), 352.3s, $0.2928216)
  - Instantiate actual path with ctx; choose marks [T], source result and es; discharge arbitrary-tail source via msg_gas_source and target post by state projections. -> Strict frozen summary proved unconditionally and target built clean at default tactic limit. (`TO_msg_gas_leaf-20261103T024228Z_m0106_t001`)
  - Audit generated theory and source. -> Generated .dat exports both roots with only DISK_THM tags (lines 71-90); no new script cheat or forbidden generic theorem/search wrappers. .holbuild/gen not present, so used generated .obj theory data instead. (`TO_msg_gas_leaf-20261103T024228Z_m0113_t001`, `TO_msg_gas_leaf-20261103T024228Z_m0115_t001`)

### Evidence refs

- `TO_msg_gas_leaf-20261103T024228Z_m0106_t001` (use `read_tool_output` for exact output)
- `TO_msg_gas_leaf-20261103T024228Z_m0113_t001` (use `read_tool_output` for exact output)
- `TO_msg_gas_leaf-20261103T024228Z_m0115_t001` (use `read_tool_output` for exact output)

## C1.6

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0007`
- blocker: 
- actual effort: 1 sessions, 10 steps, 9 tools, 1 holbuild, 525,610 tok (525,037 in, 573 out, 513,152 cached), 38.2s, $0.0808152

### Attempts / Evidence

- `E0007` (proved, , actual effort: 1 sessions, 10 steps, 9 tools, 1 holbuild, 525,610 tok (525,037 in, 573 out, 513,152 cached), 38.2s, $0.0808152)
  - Final default-limit holbuild msgGasSimTheory; source and serialized kernel-tag audit. -> Build clean in 3.647s. Both exact frozen statements retained. Script has no admissions, new definitions, or generic simulation calls. Generated exports contain DISK_THM only for each root; no additional oracle tags. No generated Theory.txt exists, so inspected public obj .sml/.dat exports directly. (`TO_msg_gas_leaf-20261103T024228Z_m0126_t001`, `TO_msg_gas_leaf-20261103T024228Z_m0123_t001`, `TO_msg_gas_leaf-20261103T024228Z_m0132_t001`, `TO_msg_gas_leaf-20261103T024228Z_m0133_t001`)

### Evidence refs

- `TO_msg_gas_leaf-20261103T024228Z_m0126_t001` (use `read_tool_output` for exact output)
- `TO_msg_gas_leaf-20261103T024228Z_m0133_t001` (use `read_tool_output` for exact output)
- `TO_msg_gas_leaf-20261103T024228Z_m0134_t001` (use `read_tool_output` for exact output)
