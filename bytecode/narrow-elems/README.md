# Narrower aggregate-literal elements

Exact bytecode comparisons for literals and internal-call arguments whose
String elements are narrower than the declared member or parameter type,
checked by the native runner (`../native/README.md`):
`./native/bytecode_parity_native.exe . narrow-elems` from `bytecode/`. The
lowering stores each element at its declared type, so the literal's layout is
the declared type's, not the elements' own.

| Source | Checks |
|---|---|
| `n01_intcall_tuple_narrow_str` | tuple literal argument, `String[5]` into `String[10]` |
| `n02_intcall_dynarr_lit_narrow_str` | DynArray literal argument, `String[5]` into `String[10]` |
| `n03_struct_lit_narrow_str` | struct literal field, `String[5]` into `String[10]` |
| `n04_intcall_tuple_wider_str` | n01 with a member whose memory size grows (`String[40]`) |
| `n05_intcall_dynarr_lit_wider_str` | n02 with a member whose memory size grows (`String[40]`) |
| `n06_struct_lit_wider_str` | n03 with a field whose memory size grows (`String[40]`) |
| `n07_intcall_str_arg_wider` | a narrower argument staged at the parameter's declared type |
| `n08_annassign_tuple_lit_wider_str` | a tuple literal assigned at a wider tuple type |
| `n09_intcall_two_str_args_wider` | two narrower arguments: the second staging buffer follows the first at its declared size |
| `n10_intcall_dynarr_lit_wider_str_len` | n05 returning `len(xs)`: the widened DynArray literal without the `String` return |
| `n11_intcall_dynarr_lit_same_str` | control: n05 with both elements `String[40]`, nothing narrower |

The narrower values are locals, not external arguments, so the calldata
argument guard (P2 in `../pending-5127-port.md`) doesn't take them out of
parity. `n05` and its control `n11` are out of parity (listed under "Not
yet attributed" there) and differ from the pin in the same bytes. `n11` has
no narrower element, so the difference comes from the internal call
returning `xs[1]` as a `String`, not from widening the literal; `n10`,
which widens the same literal and returns a word, matches.

`oracle/` holds the annotated AST/layout JSON and deployment/runtime bytecode
from the pinned Python Vyper (`VYPER_PIN`), produced as in
`../name-collisions/README.md`.
