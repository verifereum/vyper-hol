# Fixtures out of parity: the uint2str buffer

`compile_uint2str` allocates `buf_size + n_digits` bytes for its digit buffer,
where the pinned Python compiler allocates `buf_size`
(`new_temporary_value(out_t)` in `vyper/codegen_venom/builtins/strings.py`).

The result pointer sits up to `n_digits` bytes into the buffer, and an
assignment copies `buf_size` bytes from it: the memory staging copy in
`_copy_complex_type` and the storage copy in `store_storage` both use the
type's full size. With a `buf_size` buffer that read runs past the
allocation. The extra `n_digits` bytes keep it inside, which the memory
safety proof needs. Values and writes are unchanged.

This is a deliberate difference from Python at the pin; whether and how
upstream changes (a larger buffer, or copying only the length word and the
data) is still open, and the definition follows whichever it picks.

The larger allocation moves later allocations, so these fixtures no longer
match the Python oracle. Their parity theorems are out of the build until
that is settled:

- `builtin-forms/uint2str_local` (`uint2str_local_matches_python_oracle` in
  `eval/evalCompilerBuiltinForms2Script.sml`)

`phi-pointers/uint2str_arg` still matches.
