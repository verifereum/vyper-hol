(* Kernel regressions for the read table. Physical LOG operands are
   metadata, topics, size, offset; other rows retain their existing order. *)
Theory sourceMemoryRangeChecks
Ancestors
  contextCodegenRel codegenRel venomExecSemantics venomInst venomState
  list finite_map words integer_word byte
Libs wordsLib computeLib

val () = computeLib.upd_compset (computeLib.add_thms [set_byte_def])

Theorem source_memory_read_ranges_table:
  MAP (\(opc,ops).
    source_memory_read_ranges (instruction 0 opc ops []) (init_venom_state ""))
    [(MLOAD,[Lit 64w]); (ILOAD,[Lit 96w]);
     (MCOPY,[Lit 128w; Lit 64w; Lit 7w]);
     (RETURN,[Lit 64w; Lit 7w]); (REVERT,[Lit 64w; Lit 7w]);
     (SHA3,[Lit 64w; Lit 7w]);
     (LOG,[Lit 0w; Lit 7w; Lit 64w]);
     (LOG,[Lit 1w; Lit 111w; Lit 7w; Lit 64w]);
     (LOG,[Lit 2w; Lit 111w; Lit 222w; Lit 7w; Lit 64w]);
     (LOG,[Lit 3w; Lit 111w; Lit 222w; Lit 333w; Lit 7w; Lit 64w]);
     (LOG,[Lit 4w; Lit 111w; Lit 222w; Lit 333w; Lit 444w; Lit 7w; Lit 64w]);
     (CALL,[Lit 1w; Lit 2w; Lit 3w; Lit 64w; Lit 7w; Lit 128w; Lit 9w]);
     (STATICCALL,[Lit 1w; Lit 2w; Lit 64w; Lit 7w; Lit 128w; Lit 9w]);
     (DELEGATECALL,[Lit 1w; Lit 2w; Lit 64w; Lit 7w; Lit 128w; Lit 9w]);
     (CREATE,[Lit 3w; Lit 64w; Lit 7w]);
     (CREATE2,[Lit 3w; Lit 64w; Lit 7w; Lit 4w])] =
    [[(64,32)]; [(96,32)]; [(64,7)]; [(64,7)]; [(64,7)]; [(64,7)];
     [(64,7)]; [(64,7)]; [(64,7)]; [(64,7)]; [(64,7)];
     [(64,7)]; [(64,7)]; [(64,7)]; [(64,7)]; [(64,7)]]
Proof
  EVAL_TAC
QED

(* No direct memory read for copying from a non-memory source, storing,
   or aggregate INVOKE. No fallback range on undefined/malformed operands. *)
Theorem source_memory_read_ranges_empty_table:
  MAP (\(opc,ops).
    source_memory_read_ranges (instruction 0 opc ops []) (init_venom_state ""))
    [(CALLDATACOPY,[Lit 64w; Lit 0w; Lit 7w]);
     (RETURNDATACOPY,[Lit 64w; Lit 0w; Lit 7w]);
     (CODECOPY,[Lit 64w; Lit 0w; Lit 7w]);
     (EXTCODECOPY,[Lit 1w; Lit 64w; Lit 0w; Lit 7w]);
     (DLOADBYTES,[Lit 64w; Lit 0w; Lit 7w]);
     (MSTORE,[Lit 64w; Lit 1w]); (ISTORE,[Lit 64w; Lit 1w]);
     (INVOKE,[Label "callee"]); (ADD,[Lit 1w; Lit 2w]);
     (ILOAD,[]); (ILOAD,[Lit 64w; Lit 7w]); (ILOAD,[Var "missing"]);
     (LOG,[]); (LOG,[Var "missing"; Lit 7w; Lit 64w]);
     (LOG,[Lit 1w; Lit 7w; Lit 64w]);
     (LOG,[Lit 1w; Var "missing"; Lit 7w; Lit 64w]);
     (LOG,[Lit 0w; Var "missing"; Lit 64w]);
     (LOG,[Lit 0w; Lit 7w; Var "missing"]);
     (MCOPY,[Var "missing"; Lit 64w; Lit 7w]);
     (CALL,[Var "missing"; Lit 2w; Lit 3w; Lit 64w; Lit 7w; Lit 128w; Lit 9w]);
     (CREATE2,[Lit 3w; Lit 64w; Lit 7w; Var "missing"])] =
    REPLICATE 21 []
Proof
  EVAL_TAC
QED

Theorem source_memory_read_zero_and_boundaries:
  source_memory_read_ranges (instruction 0 LOG [Lit 0w; Lit 0w; Lit 64w] [])
    (init_venom_state "") = [(64,0)] /\
  ~source_memory_read_byte (instruction 0 LOG [Lit 0w; Lit 0w; Lit 64w] [])
    (init_venom_state "") 64 /\
  source_memory_read_byte (instruction 0 ILOAD [Lit 64w] ["x"])
    (init_venom_state "") 64 /\
  source_memory_read_byte (instruction 0 ILOAD [Lit 64w] ["x"])
    (init_venom_state "") 95 /\
  ~source_memory_read_byte (instruction 0 ILOAD [Lit 64w] ["x"])
    (init_venom_state "") 96
Proof
  EVAL_TAC >> simp[byte_in_memory_range_def]
QED

(* DRET keeps its metadata/ordinary-values/dynamic-pairs/return-PC envelope.
   Writes advance a padded destination cursor; reads retain source offsets. *)
Theorem DRET_range_table_unchanged:
  source_memory_read_ranges
    (instruction 0 DRET [Lit 2w; Lit 99w; Lit 64w; Lit 7w; Lit 96w; Lit 0w; Lit 0w] [])
    (init_venom_state "") = [(64,7); (96,0)] /\
  source_memory_write_ranges
    (instruction 0 DRET [Lit 2w; Lit 99w; Lit 64w; Lit 7w; Lit 96w; Lit 0w; Lit 0w] [])
    ((init_venom_state "") with vs_call_entry_fmp := 128w) = [(128,7); (160,0)] /\
  source_memory_read_ranges (instruction 0 DRET [Lit 0w; Lit 0w] [])
    (init_venom_state "") = [] /\
  source_memory_read_ranges (instruction 0 DRET [Lit 1w; Var "missing"; Lit 7w; Lit 0w] [])
    (init_venom_state "") = []
Proof
  EVAL_TAC
QED

(* Cross-check the physical LOG order against the source execution itself. *)
Theorem LOG_reads_reversed_tail:
  step_inst_base
    (instruction 0 LOG [Lit 2w; Lit 111w; Lit 222w; Lit 2w; Lit 1w] [])
    ((init_venom_state "") with vs_memory := [9w; 10w; 11w]) =
  OK ((init_venom_state "") with
    <| vs_memory := [9w; 10w; 11w];
       vs_logs := [<| logger := 0w; topics := [222w; 111w];
                       data := [10w; 11w] |>] |>)
Proof
  EVAL_TAC
QED

Theorem ILOAD_reads_byte_memory:
  step_inst_base (instruction 0 ILOAD [Lit 0w] ["x"])
    ((init_venom_state "") with
      <| vs_memory := REPLICATE 31 0w ++ [7w]; vs_immutables := FEMPTY |>) =
  OK (update_var "x" 7w ((init_venom_state "") with
      <| vs_memory := REPLICATE 31 0w ++ [7w]; vs_immutables := FEMPTY |>))
Proof
  EVAL_TAC
QED

(* Destination ranges are intentionally unchanged, including CALL's original
   declared return capacity rather than the actual short return length. *)
Theorem source_memory_write_ranges_table_unchanged:
  MAP (\(opc,ops).
    source_memory_write_ranges (instruction 0 opc ops []) (init_venom_state ""))
    [(MSTORE,[Lit 128w; Lit 1w]); (MSTORE8,[Lit 128w; Lit 1w]);
     (ISTORE,[Lit 128w; Lit 1w]);
     (MCOPY,[Lit 128w; Lit 64w; Lit 7w]);
     (CALLDATACOPY,[Lit 128w; Lit 64w; Lit 7w]);
     (RETURNDATACOPY,[Lit 128w; Lit 64w; Lit 7w]);
     (DLOADBYTES,[Lit 128w; Lit 64w; Lit 7w]);
     (CODECOPY,[Lit 128w; Lit 64w; Lit 7w]);
     (EXTCODECOPY,[Lit 1w; Lit 128w; Lit 64w; Lit 7w]);
     (CALL,[Lit 1w; Lit 2w; Lit 3w; Lit 64w; Lit 7w; Lit 128w; Lit 9w]);
     (STATICCALL,[Lit 1w; Lit 2w; Lit 64w; Lit 7w; Lit 128w; Lit 9w]);
     (DELEGATECALL,[Lit 1w; Lit 2w; Lit 64w; Lit 7w; Lit 128w; Lit 9w]);
     (ILOAD,[Lit 128w]); (LOG,[Lit 0w; Lit 7w; Lit 128w]);
     (INVOKE,[Label "callee"])] =
    [[(128,32)]; [(128,1)]; [(128,32)]; [(128,7)]; [(128,7)]; [(128,7)];
     [(128,7)]; [(128,7)]; [(128,7)]; [(128,9)]; [(128,9)]; [(128,9)];
     []; []; []]
Proof
  EVAL_TAC
QED
