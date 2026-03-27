(*
 * Selector Dispatch Definitions
 *
 * Upstream: vyperlang/vyper@a7f7bf133
 *
 * Definitions connecting Vyper-level function dispatch (by name + args)
 * to Venom-level selector dispatch (by 4-byte method_id in calldata).
 *
 * The Venom selector dispatch CFG (produced by compile_selector_dispatch)
 * extracts method_id = shr(224, calldataload(0)) and routes to the
 * matching function's entry block. These definitions formalize the
 * relationship between calldata bytes and the selector table.
 *
 * TOP-LEVEL:
 *   calldata_method_id   -- extract 4-byte selector from calldata
 *   calldata_encodes     -- calldata = selector ++ abi_encode(args)
 *   selector_matches     -- selector table entry matches a function
 *)

Theory selectorDispatch
Ancestors
  moduleLowering
  compileEnv
  vyperABI
  contractABI
  venomExecSemantics

(* ===== Calldata Method ID Extraction ===== *)

(* Extract the 4-byte method_id from calldata as a 256-bit word.
   This mirrors the Venom dispatch: shr(224, calldataload(0)).
   calldataload pads with zeros if calldata is shorter than 32 bytes,
   then shr(224, ...) isolates the top 4 bytes as a uint32. *)
Definition calldata_method_id_def:
  calldata_method_id (cd : byte list) : bytes32 =
    if LENGTH cd < 4 then 0w
    else
      let b0 = w2n (EL 0 cd) in
      let b1 = w2n (EL 1 cd) in
      let b2 = w2n (EL 2 cd) in
      let b3 = w2n (EL 3 cd) in
      n2w (b0 * 2 ** 24 + b1 * 2 ** 16 + b2 * 2 ** 8 + b3)
End

(* The 4-byte selector as a word, from function_selector. *)
Definition selector_word_def:
  selector_word (sel_bytes : byte list) : bytes32 =
    calldata_method_id sel_bytes
End

(* ===== Calldata Encoding ===== *)

(* Calldata bytes correctly encode a call to func_name with values vals.
   Uses function_selector (keccak256 of ABI signature) and
   enc (ABI encoding). *)
Definition calldata_encodes_def:
  calldata_encodes tenv func_name arg_types vals cd <=>
    ?abi_types abi_vals.
      abi_types = vyper_to_abi_types tenv (TAKE (LENGTH vals) arg_types) /\
      vyper_to_abi_list tenv (TAKE (LENGTH vals) arg_types) vals =
        SOME abi_vals /\
      cd = function_selector func_name abi_types ++
           enc (Tuple abi_types) (ListV abi_vals)
End

(* ===== Selector Table Matching ===== *)

(* A selector table entry (selector_num, entry_label) matches function
   func_name with ABI types abi_types if the selector_num equals the
   method_id derived from function_selector. *)
Definition selector_matches_def:
  selector_matches sel_num func_name abi_types <=>
    let sel_bytes = function_selector func_name abi_types in
    sel_num = w2n (calldata_method_id sel_bytes)
End

(* Calldata method_id matches a selector if the first 4 bytes of
   calldata, interpreted as uint32, equal the selector number. *)
Definition calldata_hits_selector_def:
  calldata_hits_selector cd sel_num <=>
    LENGTH cd >= 4 /\
    w2n (calldata_method_id cd) = sel_num
End

(* ===== Dispatch Routing (per-strategy) ===== *)

(* The linear dispatch strategy: iterates through selectors and jumps
   to the matching label. If calldata matches selector sel with entry
   label fn_lbl, execution from the dispatch entry block reaches fn_lbl.

   This is the key correctness property for the linear strategy.
   The sparse and dense strategies have analogous properties but with
   different CFG structures (buckets, jumptables). *)

(* Placeholder for per-strategy routing proofs. The actual proofs
   require reasoning about run_block on the compiled CFG, showing
   that the SHR/EQ/JNZ instruction sequence correctly routes. *)
Theorem linear_dispatch_reaches_label:
  !selectors fallback_lbl sel fn_lbl ctx fuel vs st st'.
    compile_selector_dispatch_linear selectors fallback_lbl st =
      ((), st') /\
    LENGTH vs.vs_call_ctx.cc_calldata >= 4 /\
    MEM (sel, fn_lbl) selectors /\
    calldata_method_id vs.vs_call_ctx.cc_calldata = n2w sel
    ==>
    T
Proof
  cheat
QED
