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

(* E. Embedding/frame audit (diagnostic only; replaces proposal B's claim).
 *
 * Sources: exprLowering.compile_array_membership_loop_def (738-789),
 * context.compile_ptr_load_def/compile_imm_load_word_def;
 * fragExec.fn_has_code_def, emitted_blocks_append, fn_has_code_split,
 * fn_has_code_start; emitHelperProps.fresh_label_output_inj,
 * fresh_label_produces_external, compile_state_ok_new_block.
 *
 * Actual consumer has ~cenv.ce_is_ctor (expr_sim_ptr/expr_vv_sim_ptr).
 * Thus ALL five locations have one emit_op loader: MLOAD, SLOAD, TLOAD,
 * CALLDATALOAD, DLOAD. Constructor ILOAD/optional ADD is excluded by that
 * consumer premise, not by a blanket assumption that arrays are memory.
 *
 * Exact proposed layout boundary, with compilation and fn_has_code sa sb fn
 * as premises, for loader=compile_ptr_load F imm loc:
 * Define notation ONLY IN THIS COMMENT: V(j)="%"++toString(sa.cs_next_var+j),
 * L(j)=fresh_label_output suffix_j (sa.cs_next_label+j), suffixes in order
 * [in_entry,in_cond,in_body,in_found,in_incr,in_exit]; delta=1 if skip>0,
 * otherwise 0. No new logical definition is needed.
 * result=V(0), idx=V(1), done=V(2), product=V(3),
 * offset=V(4) if delta=1 else V(3), address=V(4+delta),
 * element=V(5+delta), match=V(6+delta), new_idx=V(7+delta).
 * out=Var V(0) for In, Var V(8+delta) for NotIn.
 * sb.cs_next_label=sa.cs_next_label+6;
 * sb.cs_next_var=sa.cs_next_var+8+delta+(if is_in then 0 else 1).
 *
 * sb.cs_blocks=[incr_bb;found_bb;body_bb;cond_bb;entry_bb;old_bb]
 *              ++sa.cs_blocks. Each block has its indicated L label;
 * old_bb has sa.cs_current_bb and sa.cs_current_insts++[JMP L(0)].
 * entry_bb: ASSIGN 0 idx; ASSIGN 0 result; JMP L(1).
 * cond_bb: EQ idx len -> done; JNZ done L(5) L(2).
 * body_bb: MUL idx stride -> product; optional ADD skip product -> offset;
 *          ADD arr offset -> address; location load address -> element;
 *          EQ element needle -> match; JNZ match L(3) L(4).
 * found_bb: ASSIGN 1 result; JMP L(5).
 * incr_bb: ADD idx 1 -> new_idx; ASSIGN new_idx idx; JMP L(1).
 * Instruction ids are consecutive in source order from sa.cs_next_id.
 * sb.cs_current_bb=L(5); sb.cs_current_insts=[] for In, or the singleton
 * ISZERO result -> V(8+delta) for NotIn.
 *
 * Given this spine, emitted_blocks_append yields the exact six closed
 * lookups immediately from fn_has_code. No compile_state_ok or global label
 * freshness is needed for this implication: fn_has_code already demands
 * those lookups even if the input compiler state was pathological.
 * The open exit has ONLY an existential lookup with this prefix. In's
 * empty exit prefix DOES NOT imply phi_prefix_length=0: later code may add
 * PHIs. Therefore proposal B is too strong for exit. A path reaching exit
 * must stop before executing/entering its arbitrary suffix, or use a real
 * continuation-head fact. NotIn's nonempty ISZERO prefix rules out PHIs via
 * abiEncoderExitPhi.abi_encoder_nonempty_prefix_phi. Closed entry through
 * incr have explicit non-PHI heads; use typedCopyArrayPtr.entry_ghost_no_phi.
 *
 * Existing generic layout model: typedCopyLoopLayoutPtr's
 * compile_copy_sarray_typed_loop_layout and typed_copy_loop_slice_locations.
 * Missing membership-specific semantic helper: the concrete spine above,
 * then lookup/prefix/no-PHI corollaries. S1 is NOT a loop execution recipe:
 * alan-ref/base/exprSimOperatorsScript.sml.txt compile_bop_rest_case is
 * admitted (line 418); literal simulation is also admitted (line 433).
 * The newer s1-builtins-aggregates loweringShapeProps proves SHAPE only.
 *
 * Proposed chainable frame post for any completed control/load segment:
 * !x. not_fresh_at sa x ==> lookup_var x t=lookup_var x s /\
 *   FLOOKUP G' x=FLOOKUP G x /\ op_taint tn' (Var x)=op_taint tn (Var x).
 * tn'.t_mem=tn.t_mem /\ tn'.t_stor=tn.t_stor /\
 * tn'.t_trans=tn.t_trans /\ tn'.t_imm=tn.t_imm.
 * All venom_state fields equal except vs_vars, vs_current_bb, vs_prev_bb,
 * vs_inst_idx (jump_to changes prev_bb as well as the program counter).
 * In particular memory, storage/accounts, transient, allocas, call context,
 * halt/return/revert data remain unchanged. Preserve eval_operand on each
 * old arr/needle/len operand; additionally give updated idx/result explicitly
 * and clean/absent-provenance outputs for chaining.
 *
 * Derivable premises, NOT extra hypotheses for the top-level theorem:
 * operand Vars old at sa must come from successful operand expr_post/vv_post
 * and ci_mono plus operand freshness results (must be checked at integration).
 * local_ptrs_reserved and old return-buffer/PC premises come directly from
 * expr_sim_ptr; not_fresh_at_mono transports them to sa. Fresh temporaries
 * are V(j); use not_fresh_at_def, toString_inj, fresh_var_neq to separate old
 * operands. idx/result are intentionally rewritten and are NOT in this old
 * frame. Non-variable taints are unchanged since there are no writes.
 * The frame makes ghost_kept immediate and transports ghost_inv for the
 * unchanged source evaluation state once local/return operands are old.
 *
 * compile_state_ok (label disjointness) is NOT present in expr_sim_ptr,
 * expr_vv_sim_ptr or expr_body_pre. Do not add it to their consumers.
 * fresh_label_output_inj separates generated labels unconditionally; the
 * closed lookup equations are supplied by fn_has_code and the spine.
 * fn_inst_ids_distinct comes from expr_sim_ptr for eventual edge execution.
 * Remaining new helpers needing strategist authorization: concrete layout,
 * frame-preserving scalar/load/control segments, and an exit-entry treatment
 * compatible with an empty unfinished prefix. No counted paths established
 * by this audit, and no word-case falsehood established.
 *)
