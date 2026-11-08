# Immediate returned-pointer reader diagnostic

The single candidate wraps terminal_probe_empty (Bytes[1]) in Convert uint256,
inside the existing terminal_probe_call operand list. Sink, environment and
initial state are unchanged. valid_conversion permits this conversion and the
actual supported_effect_expr computation is true. No installation attempted.

ImmediateReaderProbe independently builds and checks TAKE6 of actual compile_expr:
ALLOCA32 %0; ADD %0 32 -> %1; ALLOCA64 %2; MSTORE %2 0;
MLOAD %2 -> %3; ADD %2 32 -> %4.

The fifth record now matches Concat's MLOAD off. The first instruction still
allocates32 instead of the literal-Concat fixture's64; this was already allowed
by the generic header matcher. Modulo that explicit size difference, the next
first mismatch is record5 (sixth instruction): Convert uses ADD off 32, whereas
Concat uses ADD older_data loaded_offset = ADD %1 %3. Thus absence of an immediate
reload of the fresh cell is NOT a valid boundary. This probe says nothing about
other source candidates or installed full-code occurrence.

The symbolic equation already exists as load_bytestring_as_word_def; it is not
duplicated. Its exact condition is shift_opc = SAR for signed empty masking,
otherwise no masking. ImmediateReaderProbe.immediate_reader_symbolic_prefix is
a new arbitrary-operand/arbitrary-state SHR first-two-record boundary. It
preserves the old instruction prefix, exposes fresh ids/names, MLOAD v then
ADD v literal32. SHR is the unsigned uint256 conversion selected here. The
symbolic boundary was built independently before adding the concrete fixture.
No generic image predicate, conditional simulation or assumed origin lemma was
added. Stop after this single candidate for strategy review, as PLAN requests.
