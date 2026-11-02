(*
 * The pointer discipline the O1 stages share, and the relation the stages
 * that move memory (ConcretizeMemLoc, FmpLowering) prove.
 *
 * ConcretizeMemLoc replaces each ALLOCA's bump-allocated address with a
 * fixed one from a static layout.  The two runs agree if pointer values
 * never become observable and memory is only accessed inside the
 * allocation the address points into.  The bytes of an allocation not yet
 * written hold different data in the two runs (zero or a returned callee's
 * leftovers in one, an earlier tenant's in the other); the lowering does
 * read them, copying a buffer's whole capacity, even into storage.  So
 * those bytes are tracked as tainted, and tainted data may only be copied
 * around and stored.  If taint only reaches bytes nothing reads (dead
 * bytes D: the unused capacity of a stored value, say), the two runs
 * agree except at the dead bytes of storage, transient storage,
 * immutables and return data.  Callees
 * write into buffers their caller allocated, so all this is stated over
 * the whole call stack, not the current frame.
 *
 * frame_reachable is raw_reachable run small-step through INVOKE, with
 * ghosts:
 *   stk  the suspended callers, innermost first;
 *   PG   the allocation site each argument of the current call points
 *        into, by position;
 *   G    the allocation site each pointer variable of the current frame
 *        points into (its provenance), as an (offset, size) pair;
 *   tn   the taint: memory bytes, variable bytes, storage and transient
 *        bytes and immutable bytes holding tainted data.
 *
 * ptr_discipline lo ctx vs: for some choice of pointer parameters P (the
 * argument positions of each function that carry pointers), every
 * function's pointers flow only into memory addresses, pointer arithmetic
 * with a non-pointer, ASSIGN/PHI, and INVOKE arguments at P's positions
 * (fn_ptr_ok); and at every frame_reachable state each nonempty access
 * lies inside the site its address operand points into (access_ok), and
 * tainted data is only copied or stored (taint_ok).
 *
 * ALLOCA and DALLOCA pointers are covered; GETFMP, SETFMP and RETFMP are
 * excluded, as no source emits them.  After ConcretizeMemLoc, static
 * accesses go through plain constants with no provenance: accesses ending
 * at or below the bound lo are exempt from access_ok (lo = 0 before
 * ConcretizeMemLoc, the static layout's end after it).
 *
 * TOP-LEVEL:
 *   ptr_roots, fn_pv, ptr_use_ok, fn_ptr_ok  - the syntactic part
 *   frame_reachable                           - small-step reachability
 *   access_ok, taint_ok                       - the per-state part
 *   ptr_discipline                            - the stage fact
 *   taint_within                              - taint reaches only dead bytes
 *   ctx_sim_dead                              - the stage relation
 *)


Theory ptrDiscipline
Ancestors
  list pred_set finite_map pair words venomInst venomState
  venomExecSemantics codegenRel contextCodegenRel memLocDefs
  pointerConfinedDefs passSimulationDefs

(* ===== The syntactic part ===== *)

(* Pointer roots: ALLOCA and DALLOCA outputs, and PARAMs at the function's
   pointer parameter positions P fn.fn_name. *)
Definition ptr_roots_def:
  ptr_roots (P:string -> num set) fn =
    alloca_roots fn UNION
    {out | ?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = DALLOCA /\
                  inst_output inst = SOME out} UNION
    {out | ?inst idx. MEM inst (fn_insts fn) /\ inst.inst_opcode = PARAM /\
                      inst.inst_operands = [Lit idx] /\
                      w2n idx IN P fn.fn_name /\ inst_output inst = SOME out}
End

Definition fn_pv_def:
  fn_pv P fn = pointer_derived_vars fn (ptr_roots P fn)
End

(* A pointer variable is used only as an INVOKE argument at a pointer
   position of the callee, by a pointer-preserving op, or as the address
   operand of a memory access, once.  At INVOKE, the pointer positions are
   exactly the arguments that are pointer variables. *)
Definition ptr_use_ok_def:
  ptr_use_ok P pv inst <=>
    (inst.inst_opcode = INVOKE ==>
     ?nm args. decode_invoke inst = SOME (nm,args) /\
               !k. k < LENGTH args ==>
                   (k IN P nm <=> ?v. EL k args = Var v /\ v IN pv)) /\
    !v. MEM (Var v) inst.inst_operands /\ v IN pv /\
        inst.inst_opcode <> INVOKE /\
        ~is_pointer_preserving_op inst.inst_opcode ==>
        FILTER ($= (Var v)) inst.inst_operands = [Var v] /\
        ?ops. (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops) /\
              ops.iao_ofst = Var v
End

(* MEMTOP observes the memory size, which the static layout changes, and
   GETFMP/SETFMP/RETFMP the free memory pointer, which FmpLowering changes.
   ISTORE records its address in vs_immutables, so its address (and
   ILOAD's) is never a pointer; the lowering addresses immutables from a
   fixed region.
   Forced alloca positions are taken as given by the layout, so two forced
   allocas that are live together can overlap; the lowering never forces
   any. *)
Definition fn_ptr_ok_def:
  fn_ptr_ok P fn <=>
    fn.fn_forced_alloc_positions = FEMPTY /\
    (!inst. MEM inst (fn_insts fn) ==>
            inst.inst_opcode <> MEMTOP /\ inst.inst_opcode <> DRET /\
            inst.inst_opcode <> GETFMP /\ inst.inst_opcode <> SETFMP /\
            inst.inst_opcode <> RETFMP /\
            ((inst.inst_opcode = ISTORE \/ inst.inst_opcode = ILOAD) ==>
             !v. MEM (Var v) inst.inst_operands ==> v NOTIN fn_pv P fn) /\
            ptr_use_ok P (fn_pv P fn) inst) /\
    affine_pointer_ops fn (ptr_roots P fn)
End


(* ===== Ghost provenance ===== *)

Datatype:
  call_frame = <| cf_fn : ir_function;
                  cf_inst : instruction;
                  cf_state : venom_state;
                  cf_params : (num # num) option list;
                  cf_prov : (string, num # num) fmap;
                  cf_tvar : (string, num set) fmap |>
End

Definition op_prov_def:
  op_prov (G:(string, num # num) fmap) op =
    case op of Var u => FLOOKUP G u | _ => NONE
End

Definition first_prov_def:
  first_prov G [] = NONE /\
  first_prov G (op::ops) =
    case op_prov G op of
      SOME site => SOME site
    | NONE => first_prov G ops
End

(* The site a non-PHI instruction's output points into, after the step
   to s'.  Arithmetic keeps its pointer operand's site. *)
Definition out_prov_def:
  out_prov PG G inst s' =
    if inst.inst_opcode = ALLOCA then FLOOKUP s'.vs_allocas inst.inst_id
    else if inst.inst_opcode = DALLOCA then
      (case inst.inst_outputs of
         [out] =>
           (case lookup_var out s' of
              SOME b => SOME (w2n b, w2n s'.vs_fmp - w2n b)
            | NONE => NONE)
       | _ => NONE)
    else if inst.inst_opcode = PARAM then
      (case inst.inst_operands of
         [Lit idx] => if w2n idx < LENGTH PG then EL (w2n idx) PG else NONE
       | _ => NONE)
    else if inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
            inst.inst_opcode = ASSIGN
    then first_prov G inst.inst_operands
    else NONE
End

Definition set_prov_def:
  set_prov G outs p =
    case (outs, p) of
      ([out], SOME site) => G |+ (out, site)
    | _ => DRESTRICT G (COMPL (set outs))
End

Definition step_prov_def:
  step_prov PG G inst s' = set_prov G inst.inst_outputs (out_prov PG G inst s')
End

(* PHIs read the provenance before the block, in parallel, as eval_phis
   reads values. *)
Definition phi_prov_def:
  phi_prov prev G0 inst =
    case prev of
      NONE => NONE
    | SOME lbl =>
        case resolve_phi lbl inst.inst_operands of
          SOME op => op_prov G0 op
        | NONE => NONE
End

Definition phis_prov_def:
  phis_prov prev G0 [] = G0 /\
  phis_prov prev G0 (inst::rest) =
    if inst.inst_opcode <> PHI then G0
    else set_prov (phis_prov prev G0 rest) inst.inst_outputs
                  (phi_prov prev G0 inst)
End

Definition entry_prov_def:
  entry_prov fn s G =
    case lookup_block s.vs_current_bb fn.fn_blocks of
      SOME bb => phis_prov s.vs_prev_bb G bb.bb_instructions
    | NONE => G
End

(* ===== Ghost taint ===== *)

(* Bytes are numbered as word_to_bytes w T numbers them: byte 0 is the
   most significant, the one at the lowest memory address. *)
Datatype:
  taint = <| t_mem : num set;
             t_var : (string, num set) fmap;
             t_stor : (bytes32 # num) set;
             t_trans : (bytes32 # num) set;
             t_imm : (num # num) set |>
End

Definition entry_taint_def:
  entry_taint =
    <| t_mem := {}; t_var := FEMPTY; t_stor := {}; t_trans := {};
       t_imm := {} |>
End

Definition op_taint_def:
  op_taint tn op =
    case op of
      Var u => (case FLOOKUP tn.t_var u of SOME m => m | NONE => {})
    | _ => {}
End

Definition mem_word_taint_def:
  mem_word_taint M (off:num) = {k | k < 32 /\ off + k IN M}
End

Definition key_taint_def:
  key_taint X key = {k:num | k < 32 /\ (key,k) IN X}
End

Definition range_bytes_def:
  range_bytes rs =
    {i:num | ?off len. MEM (off,len:num) rs /\ off <= i /\ i < off + len}
End

(* The bytes a step writes.  An external call copies only as much return
   data as there is. *)
Definition step_writes_def:
  step_writes inst s s' =
    if inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL \/
       inst.inst_opcode = DELEGATECALL
    then MAP (\(off,len). (off, MIN len (LENGTH s'.vs_returndata)))
             (source_memory_write_ranges inst s)
    else source_memory_write_ranges inst s
End

(* The bytes of the sites a step allocates: a new ALLOCA site, or the
   region a DALLOCA moves the free memory pointer past. *)
Definition new_site_bytes_def:
  new_site_bytes s s' =
    {i | ?aid b sz. aid NOTIN FDOM s.vs_allocas /\
                    FLOOKUP s'.vs_allocas aid = SOME (b,sz) /\
                    b <= i /\ i < b + sz} UNION
    {i | w2n s.vs_fmp <= i /\ i < w2n s'.vs_fmp}
End

(* The memory bytes a step writes with tainted data: a stored word's
   tainted bytes, or a copy's tainted sources.  Every other write is
   untainted. *)
Definition written_taint_def:
  written_taint tn inst s =
    case inst.inst_operands of
      [a; v] =>
        if inst.inst_opcode = MSTORE \/ inst.inst_opcode = ISTORE then
          (case eval_operand a s of
             SOME off => {w2n off + k | k IN op_taint tn v}
           | NONE => {})
        else {}
    | [d; src; sz] =>
        if inst.inst_opcode = MCOPY then
          (case (eval_operand d s, eval_operand src s, eval_operand sz s) of
             (SOME dst, SOME sr, SOME n) =>
               {w2n dst + i | i < w2n n /\ w2n sr + i IN tn.t_mem}
           | _ => {})
        else {}
    | _ => {}
End

(* Fresh allocations start tainted; a write sets its bytes' taint. *)
Definition mem_taint_def:
  mem_taint tn inst s s' =
    ((tn.t_mem UNION new_site_bytes s s') DIFF range_bytes (step_writes inst s s'))
    UNION written_taint tn inst s
End

(* The tainted bytes of a non-PHI instruction's output. *)
Definition out_taint_def:
  out_taint tn inst s =
    case inst.inst_operands of
      [a] =>
        (case eval_operand a s of
           SOME w =>
             if inst.inst_opcode = MLOAD \/ inst.inst_opcode = ILOAD then
               mem_word_taint tn.t_mem (w2n w)
             else if inst.inst_opcode = SLOAD then key_taint tn.t_stor w
             else if inst.inst_opcode = TLOAD then key_taint tn.t_trans w
             else if inst.inst_opcode = ASSIGN then op_taint tn a
             else {}
         | NONE => {})
    | _ => {}
End

Definition set_var_taint_def:
  set_var_taint tv outs (m:num set) =
    case outs of
      [out] => tv |+ (out, m)
    | _ => DRESTRICT tv (COMPL (set outs))
End

Definition key_update_def:
  key_update X key (m:num set) =
    {(k,b) | (k,b) IN X /\ k <> key} UNION {(key,b) | b IN m}
End

(* A store of opcode opc sets its key's taint to its value's. *)
Definition store_taint_def:
  store_taint opc tn inst s (X:(bytes32 # num) set) =
    if inst.inst_opcode = opc then
      case inst.inst_operands of
        [a; v] =>
          (case eval_operand a s of
             SOME key => key_update X key (op_taint tn v)
           | NONE => X)
      | _ => X
    else X
End

Definition imm_taint_def:
  imm_taint tn inst s =
    if inst.inst_opcode = ISTORE then
      case inst.inst_operands of
        [a; v] =>
          (case eval_operand a s of
             SOME off => key_update tn.t_imm (w2n off) (op_taint tn v)
           | NONE => tn.t_imm)
      | _ => tn.t_imm
    else tn.t_imm
End

(* An oracle call (CALL, STATICCALL) that adopts its outcome's storage
   replaces it in both runs alike, clearing its taint.  A call that changes
   nothing keeps it.  DELEGATECALL and CREATE run real code on each run's
   own storage, so taint_ok requires none to be tainted there. *)
Definition adopt_reset_def:
  adopt_reset inst changed (X:'a set) =
    if (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\ changed
    then {} else X
End

Definition step_taint_def:
  step_taint inst s s' tn =
    <| t_mem := mem_taint tn inst s s';
       t_var := set_var_taint tn.t_var inst.inst_outputs (out_taint tn inst s);
       t_stor := adopt_reset inst (s'.vs_accounts <> s.vs_accounts)
                   (store_taint SSTORE tn inst s tn.t_stor);
       t_trans := adopt_reset inst (s'.vs_transient <> s.vs_transient)
                    (store_taint TSTORE tn inst s tn.t_trans);
       t_imm := imm_taint tn inst s |>
End

(* PHIs read the taint before the block, in parallel. *)
Definition phi_taint_def:
  phi_taint prev T0 inst =
    case prev of
      NONE => {}
    | SOME lbl =>
        case resolve_phi lbl inst.inst_operands of
          SOME op => op_taint T0 op
        | NONE => {}
End

Definition phis_taint_def:
  phis_taint prev T0 [] = T0.t_var /\
  phis_taint prev T0 (inst::rest) =
    if inst.inst_opcode <> PHI then T0.t_var
    else set_var_taint (phis_taint prev T0 rest) inst.inst_outputs
                       (phi_taint prev T0 inst)
End

Definition entry_taint_vars_def:
  entry_taint_vars fn s tn =
    case lookup_block s.vs_current_bb fn.fn_blocks of
      SOME bb => tn with t_var := phis_taint s.vs_prev_bb tn bb.bb_instructions
    | NONE => tn
End

(* ===== Small-step reachability with a call stack ===== *)

(* Rules: entry, a non-terminator other than INVOKE, a terminator entering
   a block, an INVOKE entering its callee, and a callee's return resuming
   its caller after the INVOKE.  Call arguments and return values are
   untainted (taint_ok), so the callee's variables start untainted and the
   caller's outputs are. *)
Inductive frame_reachable:
[~entry:]
  (!vs0 ctx name fn lbl inst s1.
     ctx.ctx_entry = SOME name /\
     lookup_function name ctx.ctx_functions = SOME fn /\
     fn_entry_label fn = SOME lbl /\
     enters_block fn
       (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>) s1 /\
     active_inst fn inst s1 ==>
     frame_reachable vs0 ctx [] [] FEMPTY entry_taint fn inst s1)
[~next:]
  (!vs0 ctx stk PG G tn fn inst inst' s s' fuel.
     frame_reachable vs0 ctx stk PG G tn fn inst s /\ active_inst fn inst s /\
     ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
     step_inst fuel ctx inst s = OK s' /\
     active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
     frame_reachable vs0 ctx stk PG (step_prov PG G inst s')
       (step_taint inst s s' tn) fn inst'
       (s' with vs_inst_idx := SUC s.vs_inst_idx))
[~block:]
  (!vs0 ctx stk PG G tn fn inst inst' s s' s1 fuel.
     frame_reachable vs0 ctx stk PG G tn fn inst s /\ active_inst fn inst s /\
     is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
     ~s'.vs_halted /\ enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
     frame_reachable vs0 ctx stk PG (entry_prov fn s' G)
       (entry_taint_vars fn s' tn) fn inst' s1)
[~call:]
  (!vs0 ctx stk PG G tn caller inv s nm ops callee args cs s1 inst.
     frame_reachable vs0 ctx stk PG G tn caller inv s /\
     active_inst caller inv s /\
     inv.inst_opcode = INVOKE /\ decode_invoke inv = SOME (nm, ops) /\
     lookup_function nm ctx.ctx_functions = SOME callee /\
     eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
     enters_block callee cs s1 /\ active_inst callee inst s1 ==>
     frame_reachable vs0 ctx
       (<| cf_fn := caller; cf_inst := inv; cf_state := s;
           cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
       (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1)
[~ret:]
  (!vs0 ctx f stk PG G tn fn rinst s ret s_end s' inst' fuel.
     frame_reachable vs0 ctx (f::stk) PG G tn fn rinst s /\
     active_inst fn rinst s /\
     step_inst fuel ctx rinst s = IntRet ret s_end /\
     bind_outputs f.cf_inst.inst_outputs ret.iret_values
       (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) =
       SOME s' /\
     active_inst f.cf_fn inst'
       (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
     frame_reachable vs0 ctx stk f.cf_params
       (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
       (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
       f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx))
End

(* ===== The per-state part and the stage fact ===== *)

(* Each nonempty access ending above lo lies inside the site its address
   operand points into. *)
Definition access_ok_def:
  access_ok lo G inst s <=>
    (!off len.
       MEM (off,len) (source_memory_write_ranges inst s) /\ len <> 0 /\
       lo < off + len ==>
       ?ops v b sz. mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
                    FLOOKUP G v = SOME (b,sz) /\
                    b <= off /\ off + len <= b + sz) /\
    (!off len.
       MEM (off,len) (source_memory_read_ranges inst s) /\ len <> 0 /\
       lo < off + len ==>
       ?ops v b sz. mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
                    FLOOKUP G v = SOME (b,sz) /\
                    b <= off /\ off + len <= b + sz)
End

(* Tainted data is only copied around and stored: a tainted variable is
   only ASSIGNed or stored as the value of a store with an untainted
   address, and tainted memory is only loaded, copied or returned.  Code
   that runs on this contract's storage (DELEGATECALL, CREATE) sees none
   tainted. *)
Definition taint_ok_def:
  taint_ok tn inst s <=>
    (!op. MEM op inst.inst_operands /\ op_taint tn op <> {} ==>
          inst.inst_opcode = ASSIGN \/
          ((inst.inst_opcode = MSTORE \/ inst.inst_opcode = SSTORE \/
            inst.inst_opcode = TSTORE \/ inst.inst_opcode = ISTORE) /\
           ?a. inst.inst_operands = [a; op] /\ op_taint tn a = {})) /\
    (!off len i.
       MEM (off,len) (source_memory_read_ranges inst s) /\
       off <= i /\ i < off + len /\ i IN tn.t_mem ==>
       inst.inst_opcode = MLOAD \/ inst.inst_opcode = ILOAD \/
       inst.inst_opcode = MCOPY \/ inst.inst_opcode = RETURN) /\
    ((inst.inst_opcode = DELEGATECALL \/ inst.inst_opcode = CREATE \/
      inst.inst_opcode = CREATE2) ==>
     tn.t_stor = {} /\ tn.t_trans = {})
End

Definition ctx_has_dalloca_def:
  ctx_has_dalloca ctx <=>
    EXISTS (\fn. EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts fn))
      ctx.ctx_functions
End

(* ALLOCA sites lie below the free memory pointer, so DALLOCA regions never
   overlap them.  Only asked of programs that use DALLOCA: the initial
   free memory pointer is the packed static size, below the bump
   allocator's unpacked total. *)
Definition allocas_below_fmp_def:
  allocas_below_fmp s <=>
    !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
               b + sz <= w2n s.vs_fmp
End

Definition ptr_discipline_def:
  ptr_discipline (lo:num) ctx vs <=>
    ?P. EVERY (fn_ptr_ok P) ctx.ctx_functions /\
        !stk PG G tn fn inst s.
          frame_reachable vs ctx stk PG G tn fn inst s ==>
          access_ok lo G inst s /\ taint_ok tn inst s /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp s)
End

(* ===== The stage relation ===== *)

(* The tainted bytes of the return data a halting step leaves. *)
Definition ret_taint_def:
  ret_taint tn inst s =
    if inst.inst_opcode = RETURN then
      case inst.inst_operands of
        [a; n] =>
          (case (eval_operand a s, eval_operand n s) of
             (SOME off, SOME sz) => {i | i < w2n sz /\ w2n off + i IN tn.t_mem}
           | _ => {})
      | _ => {}
    else {}
End

(* The taint tn and return-data taint R when the run halts in s_h, from
   the instruction that halts it.  An INVOKE whose callee halts is
   excluded: the halting instruction is the callee's. *)
Definition final_taint_def:
  final_taint vs ctx s_h tn R <=>
    ?stk PG G T0 fn inst s fuel.
      frame_reachable vs ctx stk PG G T0 fn inst s /\ active_inst fn inst s /\
      inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = Halt s_h /\
      tn = step_taint inst s s_h T0 /\ R = ret_taint T0 inst s
End

(* The bytes nothing reads, as functions of where they are: the running
   contract's storage and transient storage, the immutables, and the
   return data.  The end-to-end theorem takes them from the source
   program's layout (storage_dead). *)
Datatype:
  dead = <| d_stor : storage -> (bytes32 # num) set;
            d_trans : storage -> (bytes32 # num) set;
            d_imm : (num |-> bytes32) -> (num # num) set;
            d_ret : word8 list -> num set |>
End

(* Taint only ever reaches dead bytes: at each call request (whose
   snapshot is the state before the call) and at the halt. *)
Definition taint_within_def:
  taint_within D ctx vs <=>
    (!stk PG G tn fn inst s fuel s'.
       frame_reachable vs ctx stk PG G tn fn inst s /\ active_inst fn inst s /\
       inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = OK s' /\
       LENGTH s.vs_requests < LENGTH s'.vs_requests ==>
       tn.t_stor SUBSET
         D.d_stor (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
       tn.t_trans SUBSET
         D.d_trans (s.vs_transient s.vs_call_ctx.cc_address)) /\
    (!s_h tn R.
       final_taint vs ctx s_h tn R ==>
       tn.t_stor SUBSET
         D.d_stor (s_h.vs_accounts s_h.vs_call_ctx.cc_address).storage /\
       tn.t_trans SUBSET
         D.d_trans (s_h.vs_transient s_h.vs_call_ctx.cc_address) /\
       tn.t_imm SUBSET D.d_imm s_h.vs_immutables /\
       R SUBSET D.d_ret s_h.vs_returndata)
End

Definition word_agree_except_def:
  word_agree_except m (w1:bytes32) w2 <=>
    !b. b < 32 /\ b NOTIN m ==>
        EL b (word_to_bytes w1 T) = EL b (word_to_bytes w2 T)
End

Definition storage_agree_except_def:
  storage_agree_except X (st1:storage) st2 <=>
    !k. word_agree_except (key_taint X k) (st1 k) (st2 k)
End

(* Equal at every address but addr, whose accounts are equal but for
   their storage, which agrees outside the dead bytes of the first. *)
Definition accounts_agree_except_def:
  accounts_agree_except D addr (a1:evm_accounts) a2 <=>
    (!a. a <> addr ==> a1 a = a2 a) /\
    (a1 addr with storage := (a2 addr).storage) = a2 addr /\
    storage_agree_except (D.d_stor (a1 addr).storage)
      (a1 addr).storage (a2 addr).storage
End

Definition transient_agree_except_def:
  transient_agree_except D addr (t1:transient_storage) t2 <=>
    (!a. a <> addr ==> t1 a = t2 a) /\
    storage_agree_except (D.d_trans (t1 addr)) (t1 addr) (t2 addr)
End

Definition imms_agree_except_def:
  imms_agree_except D (i1:num |-> bytes32) i2 <=>
    FDOM i1 = FDOM i2 /\
    !k. k IN FDOM i1 ==>
        word_agree_except {b | (k,b) IN D.d_imm i1} (i1 ' k) (i2 ' k)
End

Definition request_agree_except_def:
  request_agree_except D addr (r1:call_request) r2 <=>
    r1 with <| cr_accounts := r2.cr_accounts;
               cr_tStorage := r2.cr_tStorage |> = r2 /\
    accounts_agree_except D addr r1.cr_accounts r2.cr_accounts /\
    transient_agree_except D addr r1.cr_tStorage r2.cr_tStorage
End

(* unit_result_rel, but at a halt the runs may differ at the dead bytes of
   the first run's state: in the running contract's storage and transient
   storage (at the end and in each request's snapshot), the immutables and
   the return data. *)
Definition dead_result_rel_def:
  dead_result_rel D res res' <=>
    case (res, res') of
      (Halt s, Halt s') =>
        accounts_agree_except D s.vs_call_ctx.cc_address
          s.vs_accounts s'.vs_accounts /\
        transient_agree_except D s.vs_call_ctx.cc_address
          s.vs_transient s'.vs_transient /\
        imms_agree_except D s.vs_immutables s'.vs_immutables /\
        LENGTH s.vs_returndata = LENGTH s'.vs_returndata /\
        (!i. i < LENGTH s.vs_returndata /\ i NOTIN D.d_ret s.vs_returndata ==>
             EL i s.vs_returndata = EL i s'.vs_returndata) /\
        s.vs_halted = s'.vs_halted /\ s.vs_logs = s'.vs_logs /\
        s.vs_pending_deletions = s'.vs_pending_deletions /\
        LIST_REL (request_agree_except D s.vs_call_ctx.cc_address)
          s.vs_requests s'.vs_requests
    | (Abort a s, Abort a' s') => (a = Revert_abort ==> a' = Revert_abort)
    | _ => F
End

(* The dead bytes are fixed by the bytes that aren't: two states that agree
   outside the first's dead bytes have the same dead bytes.  storage_dead
   has this (dead_bytes_frame), and it makes dead_result_rel transitive. *)
Definition dead_wf_def:
  dead_wf D <=>
    (!st1 st2. storage_agree_except (D.d_stor st1) st1 st2 ==>
               D.d_stor st2 = D.d_stor st1) /\
    (!st1 st2. storage_agree_except (D.d_trans st1) st1 st2 ==>
               D.d_trans st2 = D.d_trans st1) /\
    (!i1 i2. imms_agree_except D i1 i2 ==> D.d_imm i2 = D.d_imm i1) /\
    (!r1 r2. LENGTH r1 = LENGTH r2 /\
             (!i. i < LENGTH r1 /\ i NOTIN D.d_ret r1 ==> EL i r1 = EL i r2) ==>
             D.d_ret r2 = D.d_ret r1)
End

(* ctx_sim up to dead bytes. *)
Definition ctx_sim_dead_def:
  ctx_sim_dead D ctx ctx' vs <=>
    !fuel. terminates (run_context fuel ctx vs) ==>
      ?fuel'. dead_result_rel D (run_context fuel ctx vs)
                (run_context fuel' ctx' vs)
End
