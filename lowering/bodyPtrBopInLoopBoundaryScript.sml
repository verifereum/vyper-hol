Theory bodyPtrBopInLoopBoundary
Ancestors
  ptrDiscipline contextCodegenRel codegenRel memLocDefs list

(* These operations neither access source memory nor compare pointers.
   Loads may produce taint; this boundary checks their inputs only. *)
Theorem word_suffix_access:
  (inst.inst_opcode = AND \/ inst.inst_opcode = ISZERO \/
   inst.inst_opcode = SLOAD \/ inst.inst_opcode = TLOAD \/
   inst.inst_opcode = CALLDATALOAD \/ inst.inst_opcode = DLOAD) ==>
  access_ok lo G fn inst s
Proof
  strip_tac >>
  simp[access_ok_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, mem_read_ops_def, mem_write_ops_def]
QED

Theorem word_suffix_taint:
  (inst.inst_opcode = AND \/ inst.inst_opcode = ISZERO \/
   inst.inst_opcode = SLOAD \/ inst.inst_opcode = TLOAD \/
   inst.inst_opcode = CALLDATALOAD \/ inst.inst_opcode = DLOAD) /\
  (!op. MEM op inst.inst_operands ==> op_taint tn op = {}) ==>
  taint_ok fn tn inst s
Proof
  strip_tac >>
  simp[taint_ok_def, source_memory_read_ranges_def, mem_read_ops_def] >>
  metis_tac[]
QED

(* CONTRACT LEDGER: proposals for review, NOT asserted theorems.
 * Types used below: a/needle/arr/len/op : operand; G : (string,num#num) fmap;
 * tn : taint; s/t : venom_state; sa/sb : compile_state; fn : ir_function.
 * All other types are determined by the existing constants in each formula.
 *
 * A. Loaded-word output, proposed conditional implementation boundary:
 *
 * !PG G tn s t id a out w opc.
 *   eval_operand a s = SOME w /\
 *   (opc = MLOAD \/ opc = SLOAD \/ opc = TLOAD \/
 *    opc = CALLDATALOAD \/ opc = DLOAD) /\
 *   (opc = MLOAD ==> mem_word_taint tn.t_mem (w2n w) = {}) /\
 *   (opc = SLOAD ==> key_taint tn.t_stor w = {}) /\
 *   (opc = TLOAD ==> key_taint tn.t_trans w = {}) ==>
 *   op_taint (step_taint (mk_inst id opc [a] [out]) s t tn)
 *     (Var out) = {} /\
 *   FLOOKUP (step_prov PG G (mk_inst id opc [a] [out]) t) out = NONE
 *
 * Derivation sources: out_taint_def and out_prov_def directly give the
 * implementation equation; no clean input premise is needed for this
 * output equation (clean input is separately needed for taint_ok).
 * Memory antecedent comes from robust_mem_word_at_clean and a robust word
 * projection of ptr_mem_ok, not ptr_buf_ok alone. Dynamic header projection:
 * typedCopyLayoutPtr.dynarray_in_memory_robust_length; live element projection
 * still needed. MLOAD input coverage uses ptr_inst_ok_mload/ptr_covers_offset.
 * Nonconstructor code uses DLOAD, so no ILOAD case is required here.
 *
 * STORAGE/TRANSIENT GAP: ptr_vv_ok LocatedValue supplies only
 *   (k,b) IN tn.t_stor ==> dead_bytes storage base tv (w2n k) b
 * (and the transient twin), restricted to keys in the array's slot range.
 * To derive key_taint={} at a LIVE word child one must prove dead_bytes is
 * false there, using child type, index < runtime length, slot size, and the
 * array value/length relation in vv_post.storage_holds. dead_bytes_def makes
 * base/flag word deadness false, but arrays quantify another index: disjoint
 * child slot ranges must eliminate that index. For a dynamic header, show
 * the header key is outside every child region. Neither load input checks
 * nor the current two LoopBoundary theorems prove these implications.
 *
 * B. Actual generated block has no PHI prefix, proposed code boundary:
 *
 * !cenv needle arr len stride skip is_in sa op sb fn lbl bb.
 *   compile_array_membership_loop needle arr len stride skip
 *     (compile_ptr_load F cenv.ce_imm_alloca LocMemory) is_in sa = (op,sb) /\
 *   fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
 *   (lbl = fresh_label_output "in_entry" sa.cs_next_label \/
 *    lbl = fresh_label_output "in_cond" (sa.cs_next_label + 1) \/
 *    lbl = fresh_label_output "in_body" (sa.cs_next_label + 2) \/
 *    lbl = fresh_label_output "in_found" (sa.cs_next_label + 3) \/
 *    lbl = fresh_label_output "in_incr" (sa.cs_next_label + 4) \/
 *    lbl = fresh_label_output "in_exit" (sa.cs_next_label + 5)) /\
 *   lookup_block lbl fn.fn_blocks = SOME bb ==>
 *   phi_prefix_length bb.bb_instructions = 0
 *
 * This first code contract specializes a simple loader deliberately; it
 * must later be generalized over all compile_ptr_load locations. Existing
 * entry_ghost_no_phi then gives entry_prov=G and entry_taint_vars=tn at each
 * such block. Missing: actual generated block lookup/prefix equations;
 * fn_has_code does not by itself expose them. Need labels fresh wrt existing
 * code (the full compiler wellformedness precondition may be required).
 * Loop source emits mutable idx/result ASSIGNs, no PHI.
 *)

(* C. Zero-length counted exit: proposed first bounded-path contract.
 *
 * !D ctx fn PG G tn s sa sb cenv needle arr loc stride skip is_in op.
 *   compile_array_membership_loop needle arr (Lit 0w) stride skip
 *     (compile_ptr_load F cenv.ce_imm_alloca loc) is_in sa = (op,sb) /\
 *   fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
 *   ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
 *   s.vs_current_bb = sa.cs_current_bb /\
 *   s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
 *   ?n G' tn' t.
 *     gas_path_ptr D 0 ctx fn PG G tn s n G' tn' (OK t) /\
 *     t.vs_current_bb = sb.cs_current_bb /\
 *     t.vs_inst_idx = LENGTH sb.cs_current_insts /\
 *     eval_operand op t = SOME (if is_in then 0w else 1w) /\
 *     op_taint tn' op = {} /\ op_prov G' op = NONE
 *
 * Count existential uses gas_path_ptr's real signature, not an erased run.
 * Here len is a literal, avoiding an unproved clean/provenance premise.
 * No arr/needle coverage needed: body/loader not executed. D is arbitrary
 * since JMP/ASSIGN/EQ/ISZERO neither request nor halt. Needed preliminary
 * code facts: generated entry/cond/exit block lookups, prefix instructions,
 * fresh variable inequality, no-PHI identity, and step equations. C does
 * NOT yet give the ghost_inv/ghost_kept post of the complete consumer.
 * A later frame-strengthened version must preserve older G and tn and use
 * local_ptrs_reserved plus not_fresh return variables for ghost_inv.
 *
 * D. First single-iteration probe proposal, memory word stride only.
 * In addition to the compilation/embedding premises below, all numeric
 * operand values are bytes32; i,len_n are num. This intentionally isolates
 * an ordinary in-bounds memory load, NOT all word-array locations.
 *
 * !D ctx fn PG G tn s sa sb cenv needle arr len is_in op p aw nw i len_n.
 *   compile_array_membership_loop needle arr len 32 0
 *     (compile_ptr_load F cenv.ce_imm_alloca LocMemory) is_in sa = (op,sb) /\
 *   fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
 *   ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
 *   s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
 *   s.vs_inst_idx = 0 /\
 *   arr = Var p /\ eval_operand arr s = SOME aw /\
 *   (!v. MEM (Var v) [arr;needle;len] ==> not_fresh_at sa v) /\
 *   eval_operand needle s = SOME nw /\
 *   eval_operand len s = SOME (n2w len_n) /\
 *   lookup_var ("%" ++ toString (sa.cs_next_var+1)) s = SOME (n2w i) /\
 *   i < len_n /\ len_n < dimword(:256) /\
 *   ptr_covers G tn p s (32 * len_n) /\
 *   (!b cap. FLOOKUP G p = SOME (b,cap) ==> b+cap <= dimword(:256)) /\
 *   op_taint tn needle = {} /\ op_prov G needle = NONE /\
 *   op_taint tn len = {} /\ op_prov G len = NONE /\
 *   op_taint tn (Var ("%" ++ toString (sa.cs_next_var+1))) = {} /\
 *   op_prov G (Var ("%" ++ toString (sa.cs_next_var+1))) = NONE /\
 *   (!j. w2n aw + 32*i <= j /\ j < w2n aw + 32*i + 32 ==>
 *        j NOTIN tn.t_mem) ==>
 *   ?n G' tn' t.
 *     gas_path_ptr D 0 ctx fn PG G tn s n G' tn' (OK t) /\
 *     t.vs_inst_idx = 0 /\
 *     (t.vs_current_bb = fresh_label_output "in_found" (sa.cs_next_label+3) /\
 *      mload (w2n aw + 32*i) s = nw \/
 *      t.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1) /\
 *      mload (w2n aw + 32*i) s <> nw /\
 *      lookup_var ("%" ++ toString (sa.cs_next_var+1)) t = SOME (n2w (i+1)))
 *
 * PROPOSAL D REQUIRES REVIEW: the old operand Vars must not coincide with
 * generated body temporaries. The explicit not_fresh_at sa premise expresses
 * this; its derivation uses operand shape before the loop. Without it a fresh
 * output could clobber needle or arr. The preserved needle/base/length/frame
 * post must still be specified for iteration chaining; this is only a probe.
 * Its coverage premise comes from ptr_mem_ok/read-covers + ptr_covers_offset;
 * taint window from robust live-child word representation, still missing.
 * Index bounds are the intended loop invariant; cleanliness/provenance of
 * index comes from ASSIGN of clean literals or ADD of plain numeric operands.
 * Generalization to dynamic skip, other loaders, and correct found/result
 * assignment is still required before full-loop integration.
 *)
