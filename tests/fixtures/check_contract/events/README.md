Each `<name>.json` here is the sanitized annotated AST and storage layout of
`<name>.vy`, generated with Vyper at `VYPER_PIN`
(`9362e36b145c4b63ceb6a893018ea970e78bf6a6`) under Python 3.11. `libp.vy` is
the module `event_import_user_module.vy` imports. Each JSON's
`source_sha256sum` is the SHA-256 of its `.vy` file.

From this directory, for each fixture:

```sh
vyper --experimental-codegen --evm-version prague -O none \
  --disable-bytecode-metadata -f annotated_ast,layout <name>.vy > <name>.jsonl
python3 ../../../sanitize_check_contract_json.py <name>.jsonl <name>.json \
  --replace "$PWD/=" \
  --replace "<vyper install root>/lib/python3.11/site-packages/vyper/builtins/interfaces/=vyper/builtins/interfaces/"
```

The second replacement turns the resolved path of Vyper's built-in `IERC20`
interface, in `event_import_ierc20.json` and `event_import_approval.json`,
into the path it is imported by.

`vyperEventFixtureTestTheory` runs the frontend and the contract checker in
both modes on all ten inputs. It also checks that the three `event_import_*`
inputs are rejected when projected to a single module.
