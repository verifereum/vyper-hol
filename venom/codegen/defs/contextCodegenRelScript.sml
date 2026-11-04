(*
 * Context-wide code-generation memory relations.
 *
 * The existing codegenRel$memory_rel remains the allocator-local relation
 * used by single-function simulation.  This theory adds the ambient relation
 * needed while caller spill regions remain live across internal calls.
 *)

Theory contextCodegenRel
Ancestors
  codegenRel venomExecSemantics venomWf fcgDefs

(* A byte in any function's half-open spill interval. *)
Definition context_spill_byte_def:
  context_spill_byte cp i <=>
    ?r. MEM r cp.cp_regions /\
        r.sr_spill_base <= i /\ i < r.sr_spill_end
End

(* Ambient memories may differ throughout the union of planned spill regions,
   but agree at every other byte (with the usual implicit zero padding). *)
Definition context_memory_rel_def:
  context_memory_rel cp venom_mem asm_mem <=>
    !i. ~context_spill_byte cp i ==>
        read_byte i venom_mem = read_byte i asm_mem
End
(* Context-facing Venom/assembly relation.  Unlike venom_asm_rel, its memory
   mask covers every spill region in the complete context plan.  Its running
   oracle/request clauses match venom_asm_rel; GAS readings remain free. *)
Definition context_venom_asm_rel_def:
  context_venom_asm_rel cp label_offsets ps vs as <=>
    plan_stack_rel label_offsets vs ps.ps_stack as.as_stack /\
    plan_spill_rel label_offsets vs ps.ps_spilled as.as_memory /\
    context_memory_rel cp vs.vs_memory as.as_memory /\
    as.as_accounts = vs.vs_accounts /\
    as.as_transient = vs.vs_transient /\
    as.as_returndata = vs.vs_returndata /\
    as.as_logs = vs.vs_logs /\
    as.as_outcomes = vs.vs_outcomes /\
    as.as_requests = vs.vs_requests /\
    as.as_pending_deletions = vs.vs_pending_deletions /\
    as.as_call_ctx = vs.vs_call_ctx /\
    as.as_tx_ctx = vs.vs_tx_ctx /\
    as.as_block_ctx = vs.vs_block_ctx /\
    as.as_code = vs.vs_code /\
    as.as_prev_hashes = vs.vs_prev_hashes
End

Theorem context_venom_asm_rel_terminal:
  context_venom_asm_rel cp lo ps vs as ==>
  venom_asm_terminal_rel vs as
Proof
  simp[context_venom_asm_rel_def, venom_asm_terminal_rel_def]
QED

Theorem context_venom_asm_rel_memory:
  context_venom_asm_rel cp lo ps vs as ==>
  context_memory_rel cp vs.vs_memory as.as_memory
Proof
  simp[context_venom_asm_rel_def]
QED


(* A source step preserves every byte reserved for compiler spills. *)
Definition context_spill_step_safe_def:
  context_spill_step_safe cp vs vs' <=>
    !i. context_spill_byte cp i ==>
        read_byte i vs.vs_memory = read_byte i vs'.vs_memory
End

(* Membership in a half-open source-memory read range.  In particular a
   zero-length range contains no byte. *)
Definition byte_in_memory_range_def:
  byte_in_memory_range (off:num,len:num) (i:num) <=>
    off <= i /\ i < off + len
End

Definition memory_range_of_operands_def:
  memory_range_of_operands off_op len_op vs =
    case (eval_operand off_op vs, eval_operand len_op vs) of
      (SOME off, SOME len) => [(w2n off,w2n len)]
    | _ => []
End

Definition dret_memory_read_ranges_def:
  dret_memory_read_ranges inst vs =
    case parse_dret_shape inst of
      NONE => []
    | SOME (ordinary,dynamic) =>
        case eval_operands inst.inst_operands vs of
          NONE => []
        | SOME vals =>
            case pair_dret_words
              (TAKE (2 * dynamic) (DROP (1 + ordinary) vals)) of
              NONE => []
            | SOME pairs => MAP (\(src,len). (w2n src,w2n len)) pairs
End

(* Exactly the byte ranges consumed from vs_memory by step_inst_base.
   INVOKE has no direct caller-memory range here: its nested execution is
   covered separately by the aggregate INVOKE closure obligation.  Copies
   whose source is calldata, returndata, code, or the data section are not
   source-memory reads and therefore intentionally have no range here. *)
Definition source_memory_read_ranges_def:
  source_memory_read_ranges inst vs =
    case inst.inst_opcode of
      MLOAD =>
        (case inst.inst_operands of
           [off_op] =>
             (case eval_operand off_op vs of
                SOME off => [(w2n off,32)]
              | NONE => [])
         | _ => [])
    | ILOAD =>
        (case inst.inst_operands of
           [off_op] =>
             (case eval_operand off_op vs of
                SOME off => [(w2n off,32)]
              | NONE => [])
         | _ => [])
    | MCOPY =>
        (case inst.inst_operands of
           [dst_op; src_op; len_op] =>
             (case (eval_operand dst_op vs, eval_operand src_op vs,
                    eval_operand len_op vs) of
                (SOME dst, SOME src, SOME len) => [(w2n src,w2n len)]
              | _ => [])
         | _ => [])
    | DRET => dret_memory_read_ranges inst vs
    | RETURN =>
        (case inst.inst_operands of
           [off_op; len_op] => memory_range_of_operands off_op len_op vs
         | _ => [])
    | REVERT =>
        (case inst.inst_operands of
           [off_op; len_op] => memory_range_of_operands off_op len_op vs
         | _ => [])
    | SHA3 =>
        (case inst.inst_operands of
           [off_op; len_op] => memory_range_of_operands off_op len_op vs
         | _ => [])
    | LOG =>
        (case inst.inst_operands of
           Lit tc :: rest =>
             let n = w2n tc in
             if LENGTH rest <> n + 2 then []
             else
               let rev = REVERSE rest in
               let off_op = EL 0 rev in
               let len_op = EL 1 rev in
               let topic_ops = DROP 2 rev in
               (case eval_operands topic_ops vs of
                  NONE => []
                | SOME topics => memory_range_of_operands off_op len_op vs)
         | _ => [])
    | CALL =>
        (case inst.inst_operands of
           [gas_op; addr_op; val_op; off_op; len_op; ret_off_op; ret_len_op] =>
             (case (eval_operand gas_op vs, eval_operand addr_op vs,
                    eval_operand val_op vs, eval_operand ret_off_op vs,
                    eval_operand ret_len_op vs) of
                (SOME gas, SOME addr, SOME value, SOME ret_off, SOME ret_len) =>
                  memory_range_of_operands off_op len_op vs
              | _ => [])
         | _ => [])
    | STATICCALL =>
        (case inst.inst_operands of
           [gas_op; addr_op; off_op; len_op; ret_off_op; ret_len_op] =>
             (case (eval_operand gas_op vs, eval_operand addr_op vs,
                    eval_operand ret_off_op vs, eval_operand ret_len_op vs) of
                (SOME gas, SOME addr, SOME ret_off, SOME ret_len) =>
                  memory_range_of_operands off_op len_op vs
              | _ => [])
         | _ => [])
    | DELEGATECALL =>
        (case inst.inst_operands of
           [gas_op; addr_op; off_op; len_op; ret_off_op; ret_len_op] =>
             (case (eval_operand gas_op vs, eval_operand addr_op vs,
                    eval_operand ret_off_op vs, eval_operand ret_len_op vs) of
                (SOME gas, SOME addr, SOME ret_off, SOME ret_len) =>
                  memory_range_of_operands off_op len_op vs
              | _ => [])
         | _ => [])
    | CREATE =>
        (case inst.inst_operands of
           [value_op; off_op; len_op] =>
             (case eval_operand value_op vs of
                SOME value => memory_range_of_operands off_op len_op vs
              | NONE => [])
         | _ => [])
    | CREATE2 =>
        (case inst.inst_operands of
           [value_op; off_op; len_op; salt_op] =>
             (case (eval_operand value_op vs, eval_operand salt_op vs) of
                (SOME value, SOME salt) =>
                  memory_range_of_operands off_op len_op vs
              | _ => [])
         | _ => [])
    | _ => []
End

Definition source_memory_read_byte_def:
  source_memory_read_byte inst vs i <=>
    ?range. MEM range (source_memory_read_ranges inst vs) /\
            byte_in_memory_range range i
End

(* Every source read range avoids every context-owned spill region, in the
   same endpoint form as the writes below: a range may not straddle even an
   empty region, which the planner's spill interval can sit on. *)
Definition source_memory_reads_disjoint_def:
  source_memory_reads_disjoint cp inst vs <=>
    EVERY (\(off,len).
      len = 0 \/
      !r. MEM r cp.cp_regions ==>
          off + len <= r.sr_spill_base \/ r.sr_spill_end <= off)
      (source_memory_read_ranges inst vs)
End

(* Every source write range avoids every context-owned spill region.  Keeping
   the endpoint form here makes projection to a function-local allocator a
   direct boundary theorem rather than repeated bytewise arithmetic. *)
Definition context_source_memory_writes_disjoint_def:
  context_source_memory_writes_disjoint cp inst vs <=>
    EVERY (\(off,len).
      len = 0 \/
      !r. MEM r cp.cp_regions ==>
          off + len <= r.sr_spill_base \/ r.sr_spill_end <= off)
      (source_memory_write_ranges inst vs)
End
(* The entry dispatcher must not return through the internal-call protocol. *)
Definition entry_fn_no_ret_def:
  entry_fn_no_ret fn <=>
    EVERY (\bb. EVERY (\inst. inst.inst_opcode <> RET)
                      bb.bb_instructions) fn.fn_blocks
End

(* Connect an invariant point to the state's current executable instruction. *)
Definition active_inst_def:
  active_inst fn inst vs <=>
    ?bb. MEM bb fn.fn_blocks /\
         bb.bb_label = vs.vs_current_bb /\
         vs.vs_inst_idx < LENGTH bb.bb_instructions /\
         EL vs.vs_inst_idx bb.bb_instructions = inst
End

(* run_blocks evaluates the PHI prefix before exposing an instruction. *)
Definition enters_block_def:
  enters_block fn s s1 <=>
    ?bb s_phi. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
               eval_phis s bb.bb_instructions = OK s_phi /\
               s1 = s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions
End

Definition fn_entry_inv_def:
  fn_entry_inv Inv ctx fn s <=>
    !s1 inst. enters_block fn s s1 /\ active_inst fn inst s1 ==>
              Inv ctx fn inst s1
End

(* Closure at actual step_inst call sites, not unincremented step results.
   The ordinary continuation includes aggregate INVOKE return plumbing. *)
Definition reachability_closed_def:
  reachability_closed Inv ctx <=>
    (!fn inst inst' s s' fuel.
       Inv ctx fn inst s /\ active_inst fn inst s /\
       ~is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
       active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
       Inv ctx fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx)) /\
    (!fn inst inst' s s' s1 fuel.
       Inv ctx fn inst s /\ active_inst fn inst s /\
       is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
       ~s'.vs_halted /\ enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
       Inv ctx fn inst' s1) /\
    (!caller inv s nm ops callee args cs.
       Inv ctx caller inv s /\ active_inst caller inv s /\
       inv.inst_opcode = INVOKE /\ decode_invoke inv = SOME (nm, ops) /\
       lookup_function nm ctx.ctx_functions = SOME callee /\
       eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
       fn_entry_inv Inv ctx callee cs)
End

(* An operand resolved backwards through a block's ASSIGN copies: the
   instructions are given latest first (REVERSE (TAKE k bb.bb_instructions)
   for the operand of the instruction at index k).  A variable defined by
   anything but a one-operand ASSIGN resolves to itself. *)
Definition resolve_block_assigns_def:
  resolve_block_assigns [] op = op /\
  resolve_block_assigns (inst :: rest) op =
    case op of
      Var v =>
        if MEM v inst.inst_outputs then
          if inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [v] /\
             LENGTH inst.inst_operands = 1
          then resolve_block_assigns rest (HD inst.inst_operands)
          else op
        else resolve_block_assigns rest op
    | _ => op
End

(* Revert forwarding: RETURNDATACOPY [p; 0; rds] at i, later followed by
   REVERT [p; rds] at j, with only ASSIGNs in between and the operands
   equal up to the block's ASSIGN copies (SingleUseExpansion wraps them in
   fresh ASSIGNs).  After a failed call, the lowering copies the callee's
   revert data to p (a zero-size ALLOCA or address 0) and reverts with it
   (extcall_fail, raw_call's call_failed, create_fail), as Python does.
   Both instructions touch [p, p + rds), past the frontier when rds > 0;
   the REVERT discards memory, so that write is never read by anything
   but the REVERT itself. *)
Definition revert_forward_pair_def:
  revert_forward_pair bb i j <=>
    i < j /\
    (!k inst. i < k /\ k < j /\ get_instruction bb k = SOME inst ==>
              inst.inst_opcode = ASSIGN) /\
    ?inst1 inst2 p src rds p' rds'.
      get_instruction bb i = SOME inst1 /\
      get_instruction bb j = SOME inst2 /\
      inst1.inst_opcode = RETURNDATACOPY /\
      inst1.inst_operands = [p; src; rds] /\
      inst2.inst_opcode = REVERT /\
      inst2.inst_operands = [p'; rds'] /\
      resolve_block_assigns (REVERSE (TAKE i bb.bb_instructions)) src =
        Lit 0w /\
      resolve_block_assigns (REVERSE (TAKE i bb.bb_instructions)) p =
        resolve_block_assigns (REVERSE (TAKE j bb.bb_instructions)) p' /\
      resolve_block_assigns (REVERSE (TAKE i bb.bb_instructions)) rds =
        resolve_block_assigns (REVERSE (TAKE j bb.bb_instructions)) rds'
End

(* Index k is one of the two instructions of a revert forwarding. *)
Definition revert_forward_at_def:
  revert_forward_at bb k <=>
    ?j. revert_forward_pair bb k j \/ revert_forward_pair bb j k
End

(* The instruction state s of fn is one of a revert forwarding's two
   instructions. *)
Definition in_revert_forward_def:
  in_revert_forward fn s <=>
    ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
         revert_forward_at bb s.vs_inst_idx
End

(* A revert forwarding is exempt: it copies the callee's revert data to
   its pointer and reverts with it, reading nothing else (the REVERT's
   operands are loaded onto the stack before the copy writes), and the
   revert discards memory. *)
Definition codegen_memory_obligations_def:
  codegen_memory_obligations Inv ctx cp <=>
    !fn inst vs1 vs2 fuel.
      Inv ctx fn inst vs1 /\
      MEM fn ctx.ctx_functions /\
      MEM inst (fn_insts fn) /\ ~in_revert_forward fn vs1 ==>
      source_memory_reads_disjoint cp inst vs1 /\
      context_source_memory_writes_disjoint cp inst vs1 /\
      (step_inst fuel ctx inst vs1 = OK vs2 ==>
       context_spill_step_safe cp vs1 vs2)
End

Definition reachable_call_graph_acyclic_def:
  reachable_call_graph_acyclic ctx <=>
    reachable_fcg_acyclic ctx (fcg_analyze ctx)
End

Definition codegen_reachability_package_def:
  codegen_reachability_package Inv ctx initial_vs <=>
    reachability_closed Inv ctx /\
    ?name fn lbl.
      ctx.ctx_entry = SOME name /\
      lookup_function name ctx.ctx_functions = SOME fn /\
      fn_entry_label fn = SOME lbl /\
      fn_entry_inv Inv ctx fn
        (initial_vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                            vs_inst_idx := 0 |>)
End

Definition codegen_context_obligations_def:
  codegen_context_obligations Inv ctx cp <=>
    generate_context_plan ctx = SOME cp /\
    context_plan_layout_wf cp /\
    codegen_ready ctx /\ ctx_wf ctx /\
    reachable_call_graph_acyclic ctx /\
    (!name efn. ctx.ctx_entry = SOME name /\
       lookup_function name ctx.ctx_functions = SOME efn ==>
       entry_fn_no_ret efn) /\
    codegen_memory_obligations Inv ctx cp
End

Theorem byte_in_memory_range_zero[simp]:
  ~byte_in_memory_range (off,0) i
Proof
  simp[byte_in_memory_range_def]
QED

Theorem source_memory_read_ranges_INVOKE[simp]:
  source_memory_read_ranges (inst with inst_opcode := INVOKE) vs = []
Proof
  simp[source_memory_read_ranges_def]
QED

Theorem source_memory_read_byte_INVOKE[simp]:
  ~source_memory_read_byte (inst with inst_opcode := INVOKE) vs i
Proof
  simp[source_memory_read_byte_def]
QED
