# Current branch/interface audit (decision17)

Checked endpoint builds: WordCases, EmptyExec, EmptyPost, IndexContinue,
ScalarCertificate, CastSemantic, WidenCounted, WidenSemantic; additionally
CheckedArithmetic, ScalarChecks, Bool, EmptyUniform and SourcePrefix. All pass.
No necessary owned proof repair or immutable dependency failure was found in
this selected closure. ResidualTheory is built separately and is not imported
by these helpers. Earlier counterexample theories are retained separately.

## Branch coverage and remaining boundaries

| Family | Existing boundary | Remaining assembly |
|---|---|---|
| MaxValue/MinValue/Epsilon | WordCases.bound_builtin_body_expr_ptr_ok | Direct use; arbitrary args handled via impossible typed arity |
| word Empty | WordCases.empty_word_body_expr_ptr_ok | Direct use |
| memory Empty | EmptyExec.empty_buffer_run_certificate; EmptyPost.empty_robust_default_memory; EmptyFrame.ghost_inv_exterior_frame | Full same-endpoint ghost frame and ghost_kept; lift counted run; semantic post, vv/value body judgment |
| malformed Convert arity | ConvertEntry.convert_arity_body_expr_ptr_ok | Direct use when length<>1 |
| scalar Convert | Bool; ScalarChecks integer/address/flag/BytesM certificates; ScalarArithmetic bytes->integer/address/decimal; CheckedArithmetic int->bytes and decimal pipeline success/abort counted certificates | Semantic continuation and operand gas_outcome binding; word outputs already expose provenance NONE and empty taint |
| signed dynamic bytes -> IntT/DecimalT | Sole signed_bytestring_convert_residual | ONLY positive exact guard at final target assembly |
| unsigned dynamic bytes -> UintT/AddressT, dynamic bytes -> Bool/BytesM | Load/BytesRead/PartialRead plus scalar clamp/shift facts | Actual SHR loader counted certificate and semantic continuation, including n=0; not residual-covered |
| bytestring cast | CastSemantic.convert_cast_converted_counted_certificate | Connect source post and header clean, preserve full output lowered extent; success theorem exists, failure/bind still needed |
| widening bytestring conversion | WidenSemantic.widen_copy_converted_counted_certificate | Connect semantic run and child full lowered coverage to source footprint and destination capacity; failures/operand binding |
| identity | Compile return and scalar/memory original child post | Semantic outer-post transport, retain provenance/taint and buffer |
| Extract32 | IndexContinue.saved_source_index_outcome; compile_bytestring_src_saved_entry; SourceCompile counted frame | Read/clamp/bounds continuation, source coverage across index, exceptional paths and malformed arity |

Zero-capacity dynamic-byte scalar bypass and widened internal-call child operands
must be explicit cases during C1.P: do not infer lowered_value_type=expr_type.
The existing saved-source interface retains ptr_mem_ok after index evaluation,
not by itself full source ptr_buf_ok; combine ptr_buf_ok_ghost_kept separately.

## Exact certificate distinctions

- EmptyExec certificate consumes the *actual* run_inst_seq endpoint and yields
  inst_seq_ptr, full sz coverage and clean header/full-zero window. It does NOT
  yet export ghost_inv or ghost_kept. EmptyPost's old audit comment is historical;
  some instruction coverage has since been proved, but the final frame bridge is
  still absent.
- Scalar success certificates take op_prov G x=NONE and op_taint tn x={}; they
  return op_prov H out=NONE and empty taint, old-variable ghost frame and memory/
  storage taint preservation. Current word ptr_val_ok supplies both inputs.
  Abort certificates must be consumed without relying on output assignment.
- CastSemantic requires header coverage>=32, clean header and robust source
  memory. It preserves existing ptr_covers sz, not an arbitrary larger target.
- WidenSemantic requires capacity<2^256, n<=capacity, source full read coverage,
  semantic footprint<=n, same semantic run and robust input. It returns target
  capacity coverage, ghost_inv/ghost_kept and robust converted memory at the
  counted endpoint. Source dynamic representation vs lowered widened type is
  still a semantic adapter issue, not a reason to narrow the target.
- IndexContinue supplies the second operand judgment from success-guarded
  body_exprs_ptr_ok and source read; it preserves ptr_mem_ok via saved_ptr_mem_ok.
  It is not yet an Extract32 family theorem.

No new proof obligations were admitted in this audit. The target's old cheat
remains for final C1.F replacement; the only newly authorized admission is the
independent Residual theorem. No helper proof may import it.

## C1.P interface findings

Checked UnsignedProbe supplies two arithmetic/taint boundaries:
`unsigned_data_window_shift_clean`: n<=32 and clean occupied interval[a,a+n)
implies SHR by8*(32-n) clears the whole read-word taint, including n=0.
`extract32_data_window_clean`: off+32<=len and clean logical payload implies
clean full word at a+off. Actual taint_ok explicitly permits tainted shift data
when shift amount is clean; no extra clean-data hypothesis is needed for SHR.

Actual Extract32 sequence evaluates source, compile_bytestring_src, index, then
compile_assert_slice_bounds off32len, ADD data off, MLOAD, clamp. Required success
boundary must derive natural off+32<=LENGTH bs (including no-overflow checks)
before applying the checked clean-window theorem. Need retain source operand
value and provenance across index, using ptr_buf_ok_ghost_kept in addition to
saved_source_index_outcome's ptr_mem_ok. TransportTheory independently builds.
Zero-capacity source cannot succeed at Extract32's bounds check. The unsigned
Convert zero-capacity bypass is in compile_type_builtin_dispatch_body, before
compile_type_convert; it evaluates child but emits Lit0 without any data read.
For positive lowered capacity, require full lowered buffer>=64 plus actual
length<=32 for data word access; occupied byte cleanliness comes from robust
ptr_mem_ok_bytes_window_clean, not full padding cleanliness.

Widened interface: newer reference bodySimConvertWidened is itself admitted,
so cannot use its proof as a pointer recipe. Existing inherited theorem
memoryLocalRhsProps.memory_rhs_read_lowered_typed supplies value_runtime_typed
at lowered_value_type under expr_body_pre, supported_expr, body-program
compile mapping and successful read. memory_rhs_runtime_layout turns that into
evaluated lower type/value_has_type/memory size. Annotation typing is also
available separately via memory_rhs_read_annotation_typed. What remains is a
robust-memory adapter between annotated and lowered dynamic-byte representations
using actual value length within lowered max, and source allocation footprint
alignment. Do NOT equate the two types. exprSimConvertBytes provides
convert_bytestring_lowered_widen_success plus convert_bytestring_memory for
conversion between arbitrary dynamic bytes/string variants. An adapter can
reduce val_in_memory for each variant using the actual runtime length bound,
then quantify over arbitrary agreeing memories. This adapter and its calling
premises should be planned explicitly before claiming the full Convert family
low risk; no missing immutable dependency was discovered.
