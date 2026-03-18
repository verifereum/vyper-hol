(*
 * Module-Level Lowering: selector dispatch, external/internal functions,
 * constructor, deploy code
 *
 * TOP-LEVEL:
 *   compile_selector_dispatch_linear — O(n) linear selector matching
 *   compile_selector_dispatch_sparse — O(1) binary search on selectors
 *   compile_selector_dispatch_dense  — O(1) dense jumptable dispatch
 *   compile_internal_function       — internal function with PARAM/RET
 *   compile_entry_checks           — calldatasize + payable checks
 *   compile_constructor_epilogue   — deploy: copy runtime + RETURN
 *   compile_simple_deploy           — deploy without constructor
 *   compile_external_entry_points  — entry points for external fn w/ kwargs
 *   compile_decode_args             — unified arg decode (calldata / data section)
 *   compile_register_positional_args — wrapper: calldata positional args
 *   compile_register_constructor_args — wrapper: data section constructor args
 *
 * Mirrors Python: ~/vyper/vyper/codegen_venom/module.py
 *)

Theory moduleLowering
Ancestors
  stmtLowering exprLowering context abiEncoder compileEnv venomInst

(* SELECTOR_BYTES = 4, SELECTOR_SHIFT_BITS = 224 *)

(* Iterate through selectors, emit comparison + conditional jump *)
Definition compile_selector_checks_def:
  compile_selector_checks method_id [] st = ((), st) ∧
  compile_selector_checks method_id ((sel, fn_label)::rest) st =
    let (match_op, st1) = emit_op EQ [method_id; Lit (n2w sel)] st in
    let (match_lbl, st2) = fresh_label "match" st1 in
    let (next_lbl, st3) = fresh_label "next" st2 in
    let (_, st4) = emit_inst JNZ [match_op; Label match_lbl; Label next_lbl] [] st3 in
    (* Match: jump to function *)
    let (_, st5) = new_block match_lbl st4 in
    let (_, st6) = emit_inst JMP [Label fn_label] [] st5 in
    (* Next: continue checking *)
    let (_, st7) = new_block next_lbl st6 in
    compile_selector_checks method_id rest st7
End

(* ===== Linear Selector Dispatch ===== *)
(* Mirrors Python: module.py _generate_selector_section_linear
   Takes fallback_lbl: after all checks fail, JMP to fallback.
   Caller provides the fallback block (which may REVERT or run __default__). *)
Definition compile_selector_dispatch_linear_def:
  compile_selector_dispatch_linear selectors fallback_lbl st =
    let (cds, st1) = emit_op CALLDATASIZE [] st in
    let (has_sel, st2) = emit_op LT [cds; Lit 4w] st1 in
    let (has_sel2, st3) = emit_op ISZERO [has_sel] st2 in
    let (dispatch_lbl, st4) = fresh_label "dispatch" st3 in
    let (_, st5) = emit_inst JNZ [has_sel2; Label dispatch_lbl; Label fallback_lbl] [] st4 in
    let (_, st6) = new_block dispatch_lbl st5 in
    let (raw, st7) = emit_op CALLDATALOAD [Lit 0w] st6 in
    let (method_id, st8) = emit_op SHR [Lit 224w; raw] st7 in
    let (_, st_final) = compile_selector_checks method_id selectors st8 in
    (* After all checks: fall through to fallback *)
    emit_inst JMP [Label fallback_lbl] [] st_final
End

(* ===== Sparse Jumptable Dispatch ===== *)
(* Mirrors Python: module.py _generate_selector_section_sparse
   Binary search on sorted selectors for O(log n) dispatch.
   Uses DJMP (dynamic jump) with computed targets. *)
(* ===== Sparse Bucket Linear Search ===== *)
(* Within a single sparse bucket, do linear search through method IDs.
   For each entry: check method_id match, branch to match or next check.
   Mirrors Python: module.py sparse bucket generation (inner loop) *)
Definition compile_sparse_bucket_search_def:
  compile_sparse_bucket_search method_id_var [] fallback_lbl st =
    emit_inst JMP [Label fallback_lbl] [] st ∧
  compile_sparse_bucket_search method_id_var
      ((selector, func_lbl, has_trailing_zeroes) :: rest) fallback_lbl st =
    let (match_lbl, st1) = fresh_label "match" st in
    let (next_lbl, st2) = fresh_label "next_check" st1 in
    (* Check method_id == selector *)
    let (is_match, st3) = emit_op EQ [method_id_var;
                                      Lit (n2w selector)] st2 in
    (* If trailing zeroes, also check calldatasize >= 4.
       Mirrors Python: iszero(lt(calldatasize, 4)) *)
    let (final_match, st4) =
      if has_trailing_zeroes then
        let (cds, st3a) = emit_op CALLDATASIZE [] st3 in
        let (too_small, st3b) = emit_op LT [cds; Lit 4w] st3a in
        let (has_cd, st3c) = emit_op ISZERO [too_small] st3b in
        emit_op AND [has_cd; is_match] st3c
      else (is_match, st3) in
    let (_, st5) = emit_inst JNZ [final_match; Label match_lbl;
                                  Label next_lbl] [] st4 in
    (* Match block *)
    let (_, st6) = new_block match_lbl st5 in
    let (_, st7) = emit_inst JMP [Label func_lbl] [] st6 in
    (* Next check block *)
    let (_, st8) = new_block next_lbl st7 in
    compile_sparse_bucket_search method_id_var rest fallback_lbl st8
End

(* Pre-allocate bucket labels without creating blocks.
   Returns list of labels and updated state. *)
Definition alloc_bucket_labels_def:
  alloc_bucket_labels (0:num) st = ([] : string list, st) ∧
  alloc_bucket_labels n st =
    let (lbl, st1) = fresh_label "bucket" st in
    let (rest, st2) = alloc_bucket_labels (n - 1) st1 in
    (lbl :: rest, st2)
Termination
  WF_REL_TAC `measure FST`
End

(* Create bucket blocks at pre-allocated labels.
   Each bucket block: linear search through its selectors. *)
Definition create_bucket_blocks_def:
  create_bucket_blocks method_id_var [] [] fallback_lbl st =
    (((), st) : unit # compile_state) ∧
  create_bucket_blocks method_id_var (lbl::lbls)
      ((_, selectors) :: rest) fallback_lbl st =
    (let (_, st1) = new_block lbl st in
     let (_, st2) = compile_sparse_bucket_search method_id_var
                      selectors fallback_lbl st1 in
     create_bucket_blocks method_id_var lbls rest fallback_lbl st2) ∧
  create_bucket_blocks _ _ _ _ st = (((), st) : unit # compile_state)
End

(* ===== Sparse Jumptable Dispatch ===== *)
(* Full sparse jumptable dispatch with bucket-based structure.
   Computes bucket_id = method_id % n_buckets, loads bucket location
   from data section header via codecopy, dispatches via DJMP to bucket.
   Each bucket does linear search. Falls through to fallback on no match.
   Mirrors Python: module.py _generate_selector_section_sparse *)
(* Group selectors into buckets by (selector MOD n_buckets).
   Returns list of (bucket_id, selector_list) pairs. *)
Definition group_into_buckets_def:
  group_into_buckets [] _ = ([] : (num # (num # string # bool) list) list) ∧
  group_into_buckets ((sel, lbl, has_tz) :: rest) n_buckets =
    let bucket_id = sel MOD n_buckets in
    let rest_buckets = group_into_buckets rest n_buckets in
    (* Add to existing bucket or create new one *)
    let updated = MAP (λ(bid, items).
      if bid = bucket_id then (bid, items ++ [(sel, lbl, has_tz)])
      else (bid, items)) rest_buckets in
    if EXISTS (λ(bid, _). bid = bucket_id) rest_buckets then updated
    else (bucket_id, [(sel, lbl, has_tz)]) :: rest_buckets
End

(* KNOWN LIMITATION: Sparse and dense dispatch emit CODECOPY reads from
   data section labels ("BUCKET_HEADERS", "selector_buckets") but the data
   sections are never populated. Python calls runtime_ctx.append_data_section()
   / append_data_item() to create the backing data. The dispatch logic is
   structurally correct but incomplete — it reads from labels with no data. *)
Definition compile_selector_dispatch_sparse_def:
  compile_selector_dispatch_sparse selectors bucket_count fallback_lbl st =
    (* Check calldatasize >= 4 before reading selector.
       Mirrors Python: module.py sparse section calldatasize check *)
    let (cds, st0a) = emit_op CALLDATASIZE [] st in
    let (has_sel, st0b) = emit_op LT [cds; Lit 4w] st0a in
    let (has_sel2, st0c) = emit_op ISZERO [has_sel] st0b in
    let (dispatch_lbl, st0d) = fresh_label "dispatch" st0c in
    let (_, st0e) = emit_inst JNZ [has_sel2; Label dispatch_lbl;
                                   Label fallback_lbl] [] st0d in
    let (_, st0f) = new_block dispatch_lbl st0e in
    (* Load method ID *)
    let (raw, st1) = emit_op CALLDATALOAD [Lit 0w] st0f in
    let (method_id, st2) = emit_op SHR [Lit 224w; raw] st1 in
    if bucket_count ≤ 1 then
      (* Single bucket: inline linear search reusing method_id, jump to fallback *)
      let (_, st_chk) = compile_selector_checks method_id
            (MAP (λ(sel,lbl,_). (sel,lbl)) selectors) st2 in
      emit_inst JMP [Label fallback_lbl] [] st_chk
    else
      (* Group selectors into buckets.
         group_into_buckets only returns non-empty buckets.
         For DJMP, we need a label for ALL bucket_count slots
         so empty buckets fall through to fallback. *)
      let buckets = group_into_buckets selectors bucket_count in
      (* Phase 1: Pre-allocate bucket labels WITHOUT creating blocks.
         This keeps us in the dispatch block for the dispatch logic below.
         Allocate for ALL bucket_count slots (not just non-empty ones).
         Empty slots will map to fallback_lbl in the DJMP target list. *)
      let (bucket_lbls, st3) = alloc_bucket_labels (LENGTH buckets) st2 in
      (* Build full target list: bucket_lbls for non-empty, fallback for empty.
         bucket_lbls is indexed by bucket list position, not bucket_id.
         Map bucket_id → label, defaulting to fallback_lbl for gaps. *)
      let bucket_id_to_lbl = MAP2 (λ(bid, _) lbl. (bid, lbl))
                                   buckets bucket_lbls in
      let full_target_list = GENLIST (λi.
        case ALOOKUP bucket_id_to_lbl i of
          SOME lbl => lbl
        | NONE => fallback_lbl) bucket_count in
      (* Emit dispatch logic (still in dispatch block).
         Compute bucket_id = method_id % n_buckets *)
      let (bucket_id, st4) = emit_op Mod [method_id;
                                          Lit (n2w bucket_count)] st3 in
      (* Load bucket location from data section header.
         Header layout: 2 bytes per bucket (location field). *)
      let sz_bucket_header = 2 in
      let (hdr_offset, st5) = emit_op MUL [bucket_id;
                                           Lit (n2w sz_bucket_header)] st4 in
      (* Get data section base via OFFSET, then add per-bucket offset.
         Mirrors Python: builder.offset(0, IRLabel("BUCKET_HEADERS")) *)
      let (base_addr, st5a) = emit_op OFFSET [Lit 0w;
                                               Label "BUCKET_HEADERS"] st5 in
      let (hdr_loc, st5b) = emit_op ADD [base_addr; hdr_offset] st5a in
      let (_, st6) = emit_void CODECOPY [Lit 30w; hdr_loc;
                                         Lit (n2w sz_bucket_header)] st5b in
      let (jumpdest, st7) = emit_op MLOAD [Lit 0w] st6 in
      (* DJMP to one of the bucket blocks — finalizes dispatch block.
         Uses full_target_list so empty buckets jump to fallback. *)
      let (_, st8) = emit_inst DJMP
        (jumpdest :: MAP (λl. Label l) full_target_list) [] st7 in
      (* Phase 2: NOW create bucket blocks with linear search *)
      let (_, st9) = create_bucket_blocks method_id bucket_lbls
                       buckets fallback_lbl st8 in
      ((), st9)
End

(* ===== Dense Jumptable Dispatch ===== *)
(* Full dense jumptable dispatch with two-level perfect hash.
   1. bucket_id = method_id % n_buckets
   2. Load bucket header (5 bytes): magic(2) | location(2) | size(1)
   3. func_id = ((method_id * bucket_magic) >> BITS_MAGIC) % bucket_size
   4. Load function info from bucket: method_id(4) | label(2) | metadata(1-3)
   5. Verify method_id matches, check entry conditions
   6. DJMP to function label
   Mirrors Python: module.py _generate_selector_section_dense *)
Definition compile_selector_dispatch_dense_def:
  compile_selector_dispatch_dense selectors bucket_count
                                  fn_metadata_bytes
                                  entry_point_labels fallback_lbl st =
    (* Check calldatasize >= 4 before reading selector.
       Mirrors Python: module.py dense section calldatasize check *)
    let (cds, st0a) = emit_op CALLDATASIZE [] st in
    let (has_sel, st0b) = emit_op LT [cds; Lit 4w] st0a in
    let (has_sel2, st0c) = emit_op ISZERO [has_sel] st0b in
    let (dispatch_lbl, st0d) = fresh_label "dispatch" st0c in
    let (_, st0e) = emit_inst JNZ [has_sel2; Label dispatch_lbl;
                                   Label fallback_lbl] [] st0d in
    let (_, st0f) = new_block dispatch_lbl st0e in
    let (raw, st1) = emit_op CALLDATALOAD [Lit 0w] st0f in
    let (method_id, st2) = emit_op SHR [Lit 224w; raw] st1 in
    (* Step 1: compute bucket_id = method_id % n_buckets *)
    let (bucket_id, st3) = emit_op Mod [method_id;
                                        Lit (n2w bucket_count)] st2 in
    (* Step 2: load 5-byte bucket header via CODECOPY.
       Must add data section base address (OFFSET) to per-bucket offset.
       Mirrors Python: builder.offset(0, IRLabel("BUCKET_HEADERS")) + offset *)
    let sz_bucket_header = 5 in
    let (hdr_offset, st4) = emit_op MUL [bucket_id;
                                         Lit (n2w sz_bucket_header)] st3 in
    let (base_addr, st4a) = emit_op OFFSET [Lit 0w;
                                            Label "BUCKET_HEADERS"] st4 in
    let (hdr_loc, st4b) = emit_op ADD [base_addr; hdr_offset] st4a in
    let (_, st5) = emit_void CODECOPY [Lit 27w; hdr_loc;
                                       Lit (n2w sz_bucket_header)] st4b in
    let (hdr_info, st6) = emit_op MLOAD [Lit 0w] st5 in
    (* Extract header fields:
       hdr_info (right-aligned in 32 bytes):
         [magic:2][location:2][size:1] in low 40 bits *)
    let (bucket_location, st7) =
      let (shifted, st6a) = emit_op SHR [Lit 8w; hdr_info] st6 in
      emit_op AND [Lit 0xFFFFw; shifted] st6a in
    let (bucket_magic, st8) = emit_op SHR [Lit 24w; hdr_info] st7 in
    let (bucket_size, st9) = emit_op AND [Lit 0xFFw; hdr_info] st8 in
    (* Step 3: func_id = ((method_id * magic) >> BITS_MAGIC) % size
       BITS_MAGIC = 24 (from jumptable_utils.py:35) *)
    let bits_magic = 24 in
    let (magic_product, st10) = emit_op MUL [bucket_magic; method_id] st9 in
    let (shifted, st11) = emit_op SHR [Lit (n2w bits_magic); magic_product] st10 in
    let (func_id, st12) = emit_op Mod [shifted; bucket_size] st11 in
    (* Step 4: load function info via CODECOPY.
       func_info_size = 4 + 2 + fn_metadata_bytes *)
    let func_info_size = 4 + 2 + fn_metadata_bytes in
    let (fi_offset, st13) = emit_op MUL [func_id;
                                         Lit (n2w func_info_size)] st12 in
    let (fi_location, st14) = emit_op ADD [bucket_location; fi_offset] st13 in
    let (_, st15) = emit_void CODECOPY [Lit (n2w (32 - func_info_size));
                                        fi_location;
                                        Lit (n2w func_info_size)] st14 in
    let (func_info, st16) = emit_op MLOAD [Lit 0w] st15 in
    (* Step 5: extract and verify fields *)
    let fn_metadata_mask = n2w (2 ** (fn_metadata_bytes * 8) - 1) : bytes32 in
    let calldatasize_mask = n2w (2 ** (fn_metadata_bytes * 8) - 2) : bytes32 in
    let (is_nonpayable, st17) = emit_op AND [Lit 1w; func_info] st16 in
    let (expected_calldatasize, st18) = emit_op AND [Lit calldatasize_mask;
                                                     func_info] st17 in
    let label_bits_offset = fn_metadata_bytes * 8 in
    let (function_label, st19) =
      let (shifted, st18a) = emit_op SHR [Lit (n2w label_bits_offset);
                                          func_info] st18 in
      emit_op AND [Lit 0xFFFFw; shifted] st18a in
    let method_id_bits_offset = (fn_metadata_bytes + 2) * 8 in
    let (function_method_id, st20) = emit_op SHR
      [Lit (n2w method_id_bits_offset); func_info] st19 in
    (* Verify method_id and calldatasize *)
    let (cd_enough, st21) = emit_op CALLDATASIZE [] st20 in
    (* calldatasize_valid = calldatasize > 3 *)
    let (cds_valid, st22) = emit_op GT [cd_enough; Lit 3w] st21 in
    let (mid_correct, st23) = emit_op EQ [function_method_id; method_id] st22 in
    let (should_continue, st24) = emit_op AND [cds_valid; mid_correct] st23 in
    let (should_fallback, st25) = emit_op ISZERO [should_continue] st24 in
    let (check_lbl, st26) = fresh_label "check_passed" st25 in
    let (_, st27) = emit_inst JNZ [should_fallback; Label fallback_lbl;
                                   Label check_lbl] [] st26 in
    let (_, st28) = new_block check_lbl st27 in
    (* Assert entry conditions: callvalue and calldatasize *)
    let (callvalue_op, st29) = emit_op CALLVALUE [] st28 in
    let (bad_callvalue, st30) = emit_op MUL [is_nonpayable; callvalue_op] st29 in
    let (bad_cds, st31) = emit_op LT [cd_enough; expected_calldatasize] st30 in
    let (failed, st32) = emit_op OR [bad_callvalue; bad_cds] st31 in
    let (ok, st33) = emit_op ISZERO [failed] st32 in
    let (_, st34) = emit_void ASSERT [ok] st33 in
    (* Step 6: DJMP to function label.
       Pass all entry point labels as targets for backend verification.
       Mirrors Python: builder.djmp(function_label, *entry_point_labels) *)
    emit_inst DJMP (function_label :: MAP (λl. Label l) entry_point_labels)
              [] st34
End

(* ===== Argument Decoding (unified) ===== *)
(* Decode arguments from calldata or data section into memory.
   3-way dispatch per argument:
   1. Primitive word: LOAD + MSTORE (direct value)
   2. Static complex: decode at inline position (no offset indirection)
   3. Dynamic complex: read ABI offset from head, dereference, then decode
   Parameterized by load opcode and base adjustment for dynamic args.
   - load_opc: CALLDATALOAD (calldata) or DLOAD (data section)
   - hi_op: hi bound operand (CALLDATASIZE, or Lit data_size)
   - base_adj: base offset for dynamic ABI indirection (4 for calldata, 0 for data)
   Mirrors Python: module.py _register_positional_args + _getelemptr_abi *)
Definition compile_decode_args_def:
  compile_decode_args cenv [] _ _ _ _ st = ((), st) ∧
  compile_decode_args cenv ((name, is_prim, is_dynamic, abi_size, dec_info)::rest)
                      offset load_opc hi_op base_adj st =
    if is_prim then
      (* Word type: load, clamp, store.
         Mirrors Python: abi_decoder.py _decode_primitive + clamp_basetype.
         dec_info carries the clamp_info for this type. *)
      let (val_op, st1) = emit_op load_opc [Lit (n2w offset)] st in
      let clamp_info = (case dec_info of DecPrimWord c => c | _ => NoClamp) in
      let (_, st1a) = compile_abi_clamp_basetype val_op clamp_info st1 in
      let (_, st2) =
        case FLOOKUP cenv.ce_vars name of
          SOME (MemLoc mem_offset _) => emit_void MSTORE [Lit (n2w mem_offset); val_op] st1a
        | _ => ((), st1a) in
      compile_decode_args cenv rest (offset + abi_size) load_opc hi_op base_adj st2
    else if is_dynamic then
      (* Dynamic complex: offset indirection then decode.
         Mirrors Python: _getelemptr_abi for is_dynamic=T *)
      (case FLOOKUP cenv.ce_vars name of
         SOME (MemLoc mem_offset _) =>
           let (offset_val, st1) = emit_op load_opc [Lit (n2w offset)] st in
           let (actual_src, st2) = emit_op ADD [Lit (n2w base_adj); offset_val] st1 in
           let dst = Lit (n2w mem_offset) in
           let (_, st3) = compile_abi_decode_to_buf dst actual_src
                            load_opc hi_op dec_info st2 in
           compile_decode_args cenv rest (offset + abi_size) load_opc hi_op base_adj st3
       | _ => compile_decode_args cenv rest (offset + abi_size) load_opc hi_op base_adj st)
    else
      (* Static complex: decode at inline position (no indirection).
         Mirrors Python: _getelemptr_abi for is_dynamic=F *)
      (case FLOOKUP cenv.ce_vars name of
         SOME (MemLoc mem_offset _) =>
           let src = Lit (n2w (base_adj + offset)) in
           let dst = Lit (n2w mem_offset) in
           let (_, st1) = compile_abi_decode_to_buf dst src
                            load_opc hi_op dec_info st in
           compile_decode_args cenv rest (offset + abi_size) load_opc hi_op base_adj st1
       | _ => compile_decode_args cenv rest (offset + abi_size) load_opc hi_op base_adj st)
End

(* ===== Internal Function ===== *)
(* Mirrors Python: module.py _generate_internal_function
   1. Emit PARAM instructions for stack-passed args
   2. Allocate memory for memory-passed args (read from stack as ptrs)
   3. Compile function body
   4. Emit default STOP if no return
   5. For return: stack returns via RET, memory returns via buffer

   Key difference from external: uses PARAM/RET instead of calldata/RETURN *)
(* Emit PARAM for each arg and store to memory.
   Mirrors Python: module.py L1296-L1338 (param emit loop). *)
(* Emit PARAMs in declaration order, interleaving stack and memory params.
   Each param is (name, is_stack):
     - is_stack=T: PARAM gets value, MSTORE to ce_vars MemLoc
     - is_stack=F: PARAM gets memory pointer, no store needed
   Mirrors Python: module.py _generate_internal_function param loop.
   MUST match INVOKE push order (declaration order). *)
(* Returns (updated_cenv, next_param_idx, compile_state).
   For memory-passed params, updates ce_vars to map name → PtrVar (no alloca).
   Mirrors Python: stack-passed → new_variable + ptr_store;
                   memory-passed → register_variable (direct pointer mapping). *)
Definition compile_internal_params_def:
  compile_internal_params cenv [] (idx:num) st = (cenv, idx, st) ∧
  compile_internal_params cenv ((name, is_stack)::rest) idx st =
    let (param_op, st1) = emit_op PARAM [Lit (n2w idx)] st in
    if is_stack then
      (* Stack-passed: PARAM gets value, store to local MemLoc.
         Mirrors Python: val = builder.param(); ptr_store(var.ptr(), val) *)
      let (_, st2) =
        (case FLOOKUP cenv.ce_vars name of
           SOME (MemLoc offset _) => emit_void MSTORE [Lit (n2w offset); param_op] st1
         | _ => ((), st1)) in
      compile_internal_params cenv rest (idx + 1) st2
    else
      (* Memory-passed: PARAM is the pointer. Map variable directly to it.
         No MSTORE needed — operand IS the address.
         Mirrors Python: ptr = builder.param(); register_variable(name, typ, ptr) *)
      let mem_size = (case FLOOKUP cenv.ce_vars name of
                        SOME (MemLoc _ sz) => sz | _ => 0) in
      let cenv' = cenv with ce_vars updated_by
                    (λm. m |+ (name, PtrVar param_op mem_size)) in
      compile_internal_params cenv' rest (idx + 1) st1
End

(* NOTE: compile_internal_fn_entry deleted — was unused subset of
   compile_internal_function which inlines the same logic *)

(* ===== Constructor ===== *)
(* Mirrors Python: module.py _generate_constructor
   1. Allocate immutables buffer (alloca)
   2. Compile __init__ body
   3. Deploy epilogue: copy runtime bytecode to memory, then RETURN *)
Definition compile_constructor_epilogue_def:
  compile_constructor_epilogue runtime_size immutables_len immutables_buf st =
    (* Copy runtime bytecode to memory, append immutables, RETURN.
       Uses CODECOPY with "runtime_begin" label (NOT DLOADBYTES which reads
       vs_data_section = constructor args). The runtime bytecode is embedded
       in the deploy bytecode's data segment, addressable via code labels.
       Mirrors Python: module.py _emit_deploy_epilogue *)
    let (_, st1) =
      if immutables_len > 0 then
        let (rt_size_op, st_a) = (Lit (n2w runtime_size) : operand, st) in
        let (total_size, st_b) = emit_op ADD [rt_size_op; Lit (n2w immutables_len)] st_a in
        (* Allocate deploy buffer *)
                let (deploy_buf, st_d) = emit_op ALLOCA [total_size; Lit 0w] st_b in
        (* Copy immutables from alloca to deploy_buf + runtime_size *)
        let (imm_dst, st_e) = emit_op ADD [deploy_buf; rt_size_op] st_d in
        let (_, st_f) = emit_void MCOPY [imm_dst; immutables_buf;
                                         Lit (n2w immutables_len)] st_e in
        (* CODECOPY: copy runtime bytecode from code section to deploy_buf.
           Uses OFFSET to get runtime_begin address within the code.
           Mirrors Python: builder.codecopy(dst, IRLabel("runtime_begin"), size) *)
        let (rt_begin, st_g) = emit_op OFFSET [Lit 0w;
                                                Label "runtime_begin"] st_f in
        let (_, st_h) = emit_void CODECOPY [deploy_buf; rt_begin;
                                            rt_size_op] st_g in
        emit_inst RETURN [deploy_buf; total_size] [] st_h
      else
        (* No immutables: just CODECOPY runtime and return *)
                let (buf_alloc, st_b) = compile_alloc_buffer runtime_size st in
                let buf = buf_alloc.buf_operand in
        let (rt_begin, st_c) = emit_op OFFSET [Lit 0w;
                                                Label "runtime_begin"] st_b in
        let (_, st_d) = emit_void CODECOPY [buf; rt_begin;
                                            Lit (n2w runtime_size)] st_c in
        emit_inst RETURN [buf; Lit (n2w runtime_size)] [] st_d in
    ((), st1)
End

(* ===== Simple Deploy (no constructor) ===== *)
(* Mirrors Python: module.py _generate_simple_deploy
   Just copy runtime bytecode from data section and return it *)
(* Simple deploy (no constructor): CODECOPY runtime + immutables and RETURN.
   For simple deploy (no __init__), immutables are pre-set by the deployer
   in the code section after the runtime bytecode. CODECOPY copies both.
   Mirrors Python: module.py _generate_simple_deploy → _emit_deploy_epilogue *)
Definition compile_simple_deploy_def:
  compile_simple_deploy runtime_size immutables_len st =
    let total_size = runtime_size + immutables_len in
        let (buf_alloc, st2) = compile_alloc_buffer total_size st in
        let buf = buf_alloc.buf_operand in
    (* CODECOPY from "runtime_begin" label in code section *)
    let (rt_begin, st3) = emit_op OFFSET [Lit 0w;
                                           Label "runtime_begin"] st2 in
    let (_, st4) = emit_void CODECOPY [buf; rt_begin;
                                       Lit (n2w total_size)] st3 in
    emit_inst RETURN [buf; Lit (n2w total_size)] [] st4
End

(* ===== External Function Entry ===== *)
(* Mirrors Python: module.py _generate_external_entry
   1. Check calldata length
   2. Decode arguments from calldata
   3. Emit nonreentrant lock if needed
   4. Compile function body
   5. Emit nonreentrant unlock on return paths *)
(* NOTE: compile_external_fn_entry deleted — dead code,
   superseded by compile_entry_checks which handles both
   calldatasize and payable checks with short-calldata optimization *)

(* NOTE: max_stack_args/max_stack_returns deleted —
   Mirrors Python: calling_convention.py MAX_COPY_TO_RETURN. *)

(* ===== Kwargs Handling ===== *)

(* Create alloca for each kwarg, shared between entry points.
   Mirrors Python: module.py _create_kwarg_allocas *)
Definition compile_create_kwarg_allocas_def:
  compile_create_kwarg_allocas [] st = ([], st) ∧
  compile_create_kwarg_allocas ((name, mem_size)::rest) st =
        let (ptr_op_alloc, st2) = compile_alloc_buffer mem_size st in
        let ptr_op = ptr_op_alloc.buf_operand in
    let (rest_vars, st3) = compile_create_kwarg_allocas rest st2 in
    ((name, ptr_op) :: rest_vars, st3)
End

(* Initialize kwargs in an entry point: either from calldata or from defaults.
   kwargs_from_calldata: how many come from calldata.
   kwarg_vars: pre-allocated (name, alloca_ptr) pairs.
   Mirrors Python: module.py _init_kwargs_in_entry_point *)
(* Init kwargs: from calldata or from default expression.
   kwarg_vars: list of (name, alloca_ptr, default_expr).
   Mirrors Python: module.py _generate_entry_point_kwargs *)
Definition compile_init_kwargs_def:
  compile_init_kwargs cenv [] _ _ _ st = ((), st) ∧
  compile_init_kwargs cenv ((name, alloca_ptr, kwarg_type, default_e)::rest) calldata_offset
                      kwargs_from_calldata hi_op st =
    if kwargs_from_calldata > 0 then
      (* From calldata: ABI decode to alloca.
         Python: _getelemptr_abi + abi_decode_to_buf for calldata kwargs.
         For prim words: CALLDATALOAD + MSTORE (+ clamping).
         For complex types: full ABI decode with offset indirection. *)
      let is_prim = is_word_type kwarg_type in
      if is_prim then
        let (val_op, st1) = emit_op CALLDATALOAD [Lit (n2w calldata_offset)] st in
        let dec_info = type_to_abi_dec_info cenv kwarg_type in
        let clamp_info = (case dec_info of DecPrimWord c => c | _ => NoClamp) in
        let (_, st1a) = compile_abi_clamp_basetype val_op clamp_info st1 in
        let (_, st2) = emit_void MSTORE [alloca_ptr; val_op] st1a in
        compile_init_kwargs cenv rest (calldata_offset + 32)
                            (kwargs_from_calldata - 1) hi_op st2
      else if is_abi_dynamic (cenv_sft cenv) kwarg_type then
        (* Dynamic complex type: ABI decode with offset indirection.
           Mirrors Python: _getelemptr_abi for is_dynamic=T.
           The head position contains an offset pointer.
           Dereference: actual_src = calldata_base + offset_value.
           calldata_base = 4 (after selector) for constructor kwargs. *)
        let dec_info = type_to_abi_dec_info cenv kwarg_type in
        let (offset_val, st1) =
          emit_op CALLDATALOAD [Lit (n2w calldata_offset)] st in
        let (actual_src, st2) =
          emit_op ADD [Lit 4w; offset_val] st1 in
        let (_, st3) =
          compile_abi_decode_to_buf alloca_ptr actual_src
            CALLDATALOAD hi_op dec_info st2 in
        let abi_sz = abi_embedded_static_size (cenv_sft cenv) kwarg_type in
        compile_init_kwargs cenv rest (calldata_offset + abi_sz)
                            (kwargs_from_calldata - 1) hi_op st3
      else
        (* Static complex type: decode at inline position (no indirection).
           Mirrors Python: _getelemptr_abi for is_dynamic=F.
           Data is inline at calldata_offset, not an offset pointer. *)
        let dec_info = type_to_abi_dec_info cenv kwarg_type in
        let src = Lit (n2w (4 + calldata_offset)) in
        let (_, st1) =
          compile_abi_decode_to_buf alloca_ptr src
            CALLDATALOAD hi_op dec_info st in
        let abi_sz = abi_embedded_static_size (cenv_sft cenv) kwarg_type in
        compile_init_kwargs cenv rest (calldata_offset + abi_sz)
                            (kwargs_from_calldata - 1) hi_op st1
    else
      (* Use default: compile default expression and store.
         Mirrors Python: Expr(default_node, ctx).lower_value()
         Prim: MSTORE directly. Complex: store_memory.
         Uses actual kwarg type for the expression compilation. *)
      let (default_val, st1) = lower_value compile_expr cenv kwarg_type default_e st in
      if is_word_type kwarg_type then
        let (_, st2) = emit_void MSTORE [alloca_ptr; default_val] st1 in
        compile_init_kwargs cenv rest calldata_offset 0 hi_op st2
      else if is_bytestring_type kwarg_type then
        (* Bytestring default: dynamic copy of 32 + ceil32(actual_len) *)
        let (_, st2) = compile_store_bytestring default_val alloca_ptr st1 in
        compile_init_kwargs cenv rest calldata_offset 0 hi_op st2
      else
        (* Complex default: static MCOPY of type's memory size *)
        let mem_size = type_memory_bytes cenv kwarg_type in
        let (_, st2) = emit_void MCOPY [alloca_ptr; default_val;
                                        Lit (n2w mem_size)] st1 in
        compile_init_kwargs cenv rest calldata_offset 0 hi_op st2
End

(* Generate entry point for kwargs: init kwargs, jump to common body.
   Mirrors Python: module.py _generate_entry_point_kwargs *)
Definition compile_entry_point_kwargs_def:
  compile_entry_point_kwargs cenv kwarg_vars calldata_offset
                             kwargs_from_calldata common_label st =
    let (hi_op, st0) = emit_op CALLDATASIZE [] st in
    let (_, st1) = compile_init_kwargs cenv kwarg_vars calldata_offset
                                       kwargs_from_calldata hi_op st0 in
    emit_inst JMP [Label common_label] [] st1
End

(* Register pre-allocated kwarg allocas as variables.
   Mirrors Python: module.py _register_kwarg_variables
   Each kwarg is registered at its pre-allocated alloca address and size. *)
Definition compile_register_kwarg_vars_def:
  compile_register_kwarg_vars (cenv : compile_env) [] = cenv ∧
  compile_register_kwarg_vars cenv ((name, alloca_offset, mem_size)::rest) =
    compile_register_kwarg_vars
      (cenv with ce_vars := cenv.ce_vars |+ (name, MemLoc alloca_offset mem_size)) rest
End

(* ===== Positional Args from Calldata ===== *)
(* ===== Calldata / Data-Section Arg Wrappers ===== *)

(* Thin wrapper: decode positional args from calldata.
   Emits CALLDATASIZE once, then delegates to compile_decode_args.
   Mirrors Python: module.py _register_positional_args *)
Definition compile_register_positional_args_def:
  compile_register_positional_args cenv args calldata_offset st =
    let (hi_op, st1) = emit_op CALLDATASIZE [] st in
    compile_decode_args cenv args calldata_offset CALLDATALOAD hi_op 4 st1
End

(* Thin wrapper: decode constructor args from DATA section.
   hi bound is Lit data_size (known at compile time).
   Mirrors Python: module.py _register_constructor_args *)
Definition compile_register_constructor_args_def:
  compile_register_constructor_args cenv args data_offset data_size st =
    compile_decode_args cenv args data_offset DLOAD (Lit (n2w data_size)) 0 st
End

(* ===== Guarded Body ===== *)
(* Shared lock → body → unlock → STOP pattern.
   Used by external, fallback, and common function body generators.
   Mirrors Python: the shared pattern across _generate_external_function_body,
   _generate_fallback_body, and the kwarg common body. *)
Definition compile_guarded_body_def:
  compile_guarded_body cenv is_nonreentrant nkey use_transient
                       is_view body ret_type st =
    (* Nonreentrant lock: view functions check but don't acquire *)
    let (_, st1) =
      if is_nonreentrant then compile_nonreentrant_lock nkey use_transient is_view st
      else ((), st) in
    (* Compile body *)
    let (_, st2) = compile_stmts cenv NoLoop
                     (case ret_type of SOME t => t | NONE => BaseT BoolT)
                     body st1 in
    (* Only emit epilogue if body didn't terminate (explicit return).
       Mirrors Python: if not builder.is_terminated(): ... *)
    if block_is_terminated st2 then ((), st2)
    else
      let (_, st3) =
        if is_nonreentrant then compile_nonreentrant_unlock nkey use_transient is_view st2
        else ((), st2) in
      (* Typed functions that fall through without return: emit INVALID (abort).
         Void functions: emit STOP (success).
         Mirrors Python: CompilerPanic("External function missing return"). *)
      case ret_type of
        SOME _ => emit_inst INVALID [] [] st3
      | NONE => emit_inst STOP [] [] st3
End

(* ===== External Function Body ===== *)
(* Generate body of an external function.
   Mirrors Python: module.py _generate_external_function_body *)
Definition compile_external_function_body_def:
  compile_external_function_body cenv positional_args
                                 is_nonreentrant nkey use_transient
                                 is_view body ret_type st =
    let (_, st1) = compile_register_positional_args cenv positional_args 4 st in
    compile_guarded_body cenv is_nonreentrant nkey use_transient
                         is_view body ret_type st1
End

(* ===== Fallback Function Body ===== *)
(* Generate the fallback (__default__) function body.
   Mirrors Python: module.py _generate_fallback_body *)
Definition compile_fallback_body_def:
  compile_fallback_body cenv is_payable is_nonreentrant nkey use_transient
                        is_view body ret_type st =
    (* Payable check *)
    let (_, st1) =
      if ¬is_payable then
        let (cv, st_a) = emit_op CALLVALUE [] st in
        let (no_value, st_b) = emit_op ISZERO [cv] st_a in
        emit_void ASSERT [no_value] st_b
      else ((), st) in
    compile_guarded_body cenv is_nonreentrant nkey use_transient
                         is_view body ret_type st1
End

(* ===== Internal Function Generation ===== *)
(* Full internal function generation with calling convention.
   Mirrors Python: module.py _generate_internal_function *)
Definition compile_internal_function_def:
  compile_internal_function cenv params (* (name, is_stack) list in decl order *)
                                 has_return_buf is_nonreentrant
                                 nkey use_transient is_view
                                 is_ctor_context immutables_len
                                 immutables_alloca_id
                                 body ret_type st =
    (* Reserve immutables region for ctor-context internal functions.
       Uses shared alloca_id and forces position 0 to match constructor's
       allocation, ensuring all ctor-context functions access immutables
       at the same memory location.
       Mirrors Python: module.py L1307-1318 *)
    let (_, st0) =
      if is_ctor_context ∧ immutables_len > 0 then
        let (_, st_a) = emit_op ALLOCA [Lit (n2w immutables_len);
                                        Lit (n2w immutables_alloca_id)] st in
        (* Touch last word to force msize past immutables (GH#3101) *)
        let touch_offset = if immutables_len > 32 then immutables_len - 32
                           else 0 in
        emit_op MLOAD [Lit (n2w touch_offset)] st_a
      else (Lit 0w, st) in
    (* Return buffer pointer if memory return.
       Must MSTORE to __return_buf__ local slot so compile_stmt Return
       can retrieve it via MLOAD. Mirrors Python: module.py L1331. *)
    let (return_buf_var, st1) =
      if has_return_buf then
        let (param_op, st_a) = emit_op PARAM [Lit 0w] st0 in
        let st_b = (case FLOOKUP cenv.ce_vars "__return_buf__" of
            SOME (MemLoc rbuf_off _) =>
              SND (emit_void MSTORE [Lit (n2w rbuf_off); param_op] st_a)
          | _ => st_a) in
        (SOME param_op, st_b)
      else (NONE, st0) in
    (* Params in declaration order (interleaved stack/memory).
       Mirrors Python: for arg in func_t.arguments: param() *)
    let param_idx_start = if has_return_buf then 1 else 0 in
    let (cenv2, next_idx, st2) = compile_internal_params cenv params param_idx_start st1 in
    (* Return PC is last param.
       Must MSTORE to __return_pc__ local slot so compile_stmt Return
       can retrieve it via MLOAD. *)
    let (return_pc, st4) = emit_op PARAM [Lit (n2w next_idx)] st2 in
    let st4a = (case FLOOKUP cenv2.ce_vars "__return_pc__" of
        SOME (MemLoc rpc_off _) =>
          SND (emit_void MSTORE [Lit (n2w rpc_off); return_pc] st4)
      | _ => st4) in
    (* Nonreentrant lock: view functions check but don't acquire *)
    let (_, st5) =
      if is_nonreentrant then compile_nonreentrant_lock nkey use_transient is_view st4a
      else ((), st4a) in
    (* Compile body with updated cenv (memory-passed params mapped to PtrVar) *)
    let (_, st6) = compile_stmts cenv2 NoLoop
                     (case ret_type of SOME t => t | NONE => BaseT BoolT)
                     body st5 in
    (* Only emit epilogue if body didn't terminate.
       Mirrors Python: if not builder.is_terminated(): ... *)
    if block_is_terminated st6 then ((), st6)
    else
      let (_, st7) =
        if is_nonreentrant then compile_nonreentrant_unlock nkey use_transient is_view st6
        else ((), st6) in
      (* Python: if return_type is None → ret(return_pc)
                 else → CompilerPanic("Internal function missing return")
         We emit INVALID for the panic case — typed functions MUST have explicit return. *)
      case ret_type of
        NONE => emit_inst RET [return_pc] [] st7
      | SOME _ => emit_inst INVALID [] [] st7
End

(* ===== Entry Checks ===== *)
(* Emit payable and calldatasize checks for external entry.
   Mirrors Python: module.py _emit_entry_checks *)
Definition compile_entry_checks_def:
  compile_entry_checks min_calldata_size is_payable st =
    (* Payable check *)
    let (_, st1) =
      if ¬is_payable then
        let (cv, st_a) = emit_op CALLVALUE [] st in
        let (no_value, st_b) = emit_op ISZERO [cv] st_a in
        emit_void ASSERT [no_value] st_b
      else ((), st) in
    (* Calldatasize check *)
    if min_calldata_size > 4 then
      let (cds, st2) = emit_op CALLDATASIZE [] st1 in
      let (enough, st3) = emit_op LT [cds; Lit (n2w min_calldata_size)] st2 in
      let (ok, st4) = emit_op ISZERO [enough] st3 in
      emit_void ASSERT [ok] st4
    else
      ((), st1)
End

(* ===== Generate External Function Bodies ===== *)
(* For each external function, generate a block at its entry label with
   entry checks (payable + calldatasize) followed by the function body.
   Mirrors Python: module.py _generate_selector_section_linear inner loop.

   external_fn record: (entry_label, cenv, positional_args, min_calldata_size,
                        is_payable, is_nonreentrant, nkey, use_transient,
                        is_view, body, ret_type) *)
Definition compile_external_fn_bodies_def:
  compile_external_fn_bodies [] st = ((), st) ∧
  compile_external_fn_bodies ((entry_lbl, cenv, pos_args, min_cds,
                               is_payable, is_nr, nkey, use_trans,
                               is_view, body, ret_type) :: rest) st =
    let (_, st1) = new_block entry_lbl st in
    let (_, st2) = compile_entry_checks min_cds is_payable st1 in
    let (_, st3) = compile_external_function_body cenv pos_args
                     is_nr nkey use_trans is_view body ret_type st2 in
    compile_external_fn_bodies rest st3
End

(* ===== Generate Internal Function Bodies ===== *)
(* For each internal function, generate a new function block with
   PARAM/RET calling convention.
   Mirrors Python: module.py generate_runtime_venom loop over internal_functions.

   internal_fn record: (fn_label, cenv, params, has_return_buf,
                        is_nonreentrant, nkey, use_transient, is_view,
                        is_ctor_context, immutables_len, immutables_alloca_id,
                        body, ret_type) *)
Definition compile_internal_fn_bodies_def:
  compile_internal_fn_bodies [] st = ((), st) ∧
  compile_internal_fn_bodies ((fn_lbl, cenv, params, has_ret_buf,
                               is_nr, nkey, use_trans, is_view,
                               is_ctor, imm_len, imm_aid,
                               body, ret_type) :: rest) st =
    let (_, st1) = new_block fn_lbl st in
    let (_, st2) = compile_internal_function cenv params has_ret_buf
                     is_nr nkey use_trans is_view
                     is_ctor imm_len imm_aid body ret_type st1 in
    compile_internal_fn_bodies rest st2
End

(* ===== Generate Runtime ===== *)
(* Top-level runtime generation: selector dispatch + function bodies.
   Mirrors Python: module.py generate_runtime_venom
   dispatch_strategy: "linear", "sparse", or "dense" *)
Definition compile_generate_runtime_def:
  compile_generate_runtime selectors external_fns internal_fns
                           (fallback_fn : (compile_env # bool # bool # num #
                                           bool # bool # stmt list #
                                           type option) option)
                           dispatch_strategy
                           bucket_count fn_metadata_bytes st =
    (* Create fallback block. If fallback_fn exists, it would be compiled here.
       Otherwise REVERT. *)
    let (fallback_lbl, st0) = fresh_label "fallback" st in
    (* Selector dispatch *)
    let linear_sels = MAP (λ(sel,lbl,_). (sel,lbl)) selectors in
    let (_, st1) =
      case dispatch_strategy of
        "sparse" => compile_selector_dispatch_sparse selectors
                      bucket_count fallback_lbl st0
      | "dense" =>
          let entry_lbls = MAP (λ(_,lbl,_). lbl) selectors in
          compile_selector_dispatch_dense selectors
                     bucket_count fn_metadata_bytes entry_lbls fallback_lbl st0
      | _ (* linear *) => compile_selector_dispatch_linear linear_sels
                            fallback_lbl st0 in
    (* Generate external function bodies at their entry labels *)
    let (_, st1a) = compile_external_fn_bodies external_fns st1 in
    (* Fallback block: revert (or run __default__ if present) *)
    let (_, st2) = new_block fallback_lbl st1a in
    let (_, st3) =
      case fallback_fn of
        NONE => emit_inst REVERT [Lit 0w; Lit 0w] [] st2
      | SOME (fb_cenv, fb_payable, fb_nonreentrant, fb_nkey,
              fb_transient, fb_view, fb_body, fb_ret_type) =>
          compile_fallback_body fb_cenv fb_payable fb_nonreentrant fb_nkey
                                fb_transient fb_view fb_body fb_ret_type st2 in
    (* Generate internal function bodies *)
    let (_, st4) = compile_internal_fn_bodies internal_fns st3 in
    ((), st4)
End

(* ===== Generate Deploy ===== *)
(* Top-level deploy generation: constructor + deploy epilogue.
   Mirrors Python: module.py generate_deploy_venom *)
Definition compile_generate_deploy_def:
  compile_generate_deploy has_constructor runtime_size immutables_len
                           constructor_args data_size
                           ctor_internal_fns
                           cenv body is_payable is_nonreentrant
                           nkey use_transient st =
    if has_constructor then
      (* Payable check *)
      let (_, st1) =
        if ¬is_payable then
          let (cv, st_a) = emit_op CALLVALUE [] st in
          let (no_val, st_b) = emit_op ISZERO [cv] st_a in
          emit_void ASSERT [no_val] st_b
        else ((), st) in
      (* Reserve immutables region at position 0 *)
      let (imm_alloca, st2) =
        if immutables_len > 0 then
                    let (imm_op_alloc, st_b) = compile_alloc_buffer immutables_len st1 in
                    let imm_op = imm_op_alloc.buf_operand in
          (* Force msize past immutables region (GH#3101 fix).
             mload touches bytes [X, X+32), so touch last word.
             Prevents builtins using msize() from clobbering immutables. *)
          let touch_offset = if immutables_len > 32 then immutables_len - 32
                             else 0 in
          let (_, st_c) = emit_op MLOAD [Lit (n2w touch_offset)] st_b in
          (imm_op, st_c)
        else (Lit 0w, st1) in
      (* Register constructor args from DATA section.
         Mirrors Python: module.py _register_constructor_args.
         Constructor args are ABI-encoded and appended after the deploy bytecode. *)
      let (_, st2a) =
        compile_register_constructor_args cenv constructor_args 0 data_size st2 in
      (* Nonreentrant lock — constructors are never VIEW *)
      let (_, st3) =
        if is_nonreentrant then compile_nonreentrant_lock nkey use_transient F st2a
        else ((), st2a) in
      (* Constructor body *)
      let (_, st4) = compile_stmts cenv NoLoop (BaseT BoolT) body st3 in
      (* Only emit epilogue if body didn't terminate.
         Mirrors Python: if not builder.is_terminated(): ... *)
      if block_is_terminated st4 then ((), st4)
      else
        let (_, st5) =
          if is_nonreentrant then compile_nonreentrant_unlock nkey use_transient F st4
          else ((), st4) in
        let (_, st6) =
          compile_constructor_epilogue runtime_size immutables_len imm_alloca st5 in
        (* Generate constructor-reachable internal functions.
           Mirrors Python: module.py L231-237 loop over
           init_func_t.reachable_internal_functions *)
        compile_internal_fn_bodies ctor_internal_fns st6
    else
      compile_simple_deploy runtime_size immutables_len st
End

(* ===== Common Function Body ===== *)
(* Shared body for external functions with kwargs.
   All entry points jump here after initializing kwargs.
   Mirrors Python: module.py _generate_common_function_body *)
Definition compile_common_function_body_def:
  compile_common_function_body cenv positional_args kwarg_vars
                                is_nonreentrant nkey use_transient
                                is_view body ret_type st =
    let (_, st1) = compile_register_positional_args cenv positional_args 4 st in
    let cenv1 = compile_register_kwarg_vars cenv kwarg_vars in
    compile_guarded_body cenv1 is_nonreentrant nkey use_transient
                         is_view body ret_type st1
End

(* Each entry point: checks + kwarg init + JMP to common body.
   kwargs_from_calldata varies per entry point (0 for base, +1 per kwarg).
   Mirrors Python: _generate_entry_point_kwargs per selector variant. *)
Definition compile_external_entry_points_def:
  compile_external_entry_points [] _ _ _ _ st = ((), st) ∧
  compile_external_entry_points
    ((sel, fn_label, min_cds, is_payable, kwargs_from_calldata)::rest)
    cenv kwarg_vars calldata_offset common_label st =
    let (_, st1) = new_block fn_label st in
    let (_, st2) = compile_entry_checks min_cds is_payable st1 in
    (* Initialize kwargs: from calldata or defaults *)
    let (hi_op, st2a) = emit_op CALLDATASIZE [] st2 in
    let (_, st3) = compile_init_kwargs cenv kwarg_vars calldata_offset
                                       kwargs_from_calldata hi_op st2a in
    let (_, st4) = emit_inst JMP [Label common_label] [] st3 in
    compile_external_entry_points rest cenv kwarg_vars calldata_offset
                                  common_label st4
End
