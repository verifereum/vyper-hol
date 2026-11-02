(*
 * The pointer discipline the O1 stages share.
 *
 * ConcretizeMemLoc replaces each ALLOCA's bump-allocated address with a
 * fixed one from a static layout, so the input and output runs agree only
 * if pointer values never become observable and memory is only accessed
 * inside the allocation the address points into, at bytes written since
 * that allocation.  Callees write into buffers their caller allocated, so
 * these facts are stated over the whole call stack, not the current frame.
 *
 * frame_reachable is raw_reachable run small-step through INVOKE, with
 * four ghosts:
 *   stk  the suspended callers, innermost first;
 *   PG   the allocation site each argument of the current call points
 *        into, by position;
 *   G    the allocation site each pointer variable of the current frame
 *        points into (its provenance), as an (offset, size) pair;
 *   W    the bytes written since the site containing them was allocated,
 *        including a callee's writes into its callers' buffers.
 *
 * ptr_discipline ctx vs: for some choice of pointer parameters P (the
 * argument positions of each function that carry pointers), every
 * function's pointers flow only into memory addresses, pointer arithmetic
 * with a non-pointer, ASSIGN/PHI, and INVOKE arguments at P's positions
 * (fn_ptr_ok); and at every frame_reachable state each nonempty access
 * lies inside the site its address operand points into and reads only
 * written bytes (access_ok).
 *
 * Only ALLOCA pointers are covered.  FmpLowering's dynamic pointers
 * (DALLOCA/GETFMP) join this predicate when a source emits them.
 *
 * TOP-LEVEL:
 *   ptr_roots, fn_pv, ptr_use_ok, fn_ptr_ok  - the syntactic part
 *   frame_reachable                           - small-step reachability
 *   access_ok                                 - the per-state part
 *   ptr_discipline                            - the stage fact
 *)

Theory ptrDiscipline
Ancestors
  list pred_set finite_map pair words venomInst venomState
  venomExecSemantics codegenRel contextCodegenRel memLocDefs
  pointerConfinedDefs

(* ===== The syntactic part ===== *)

(* Pointer roots: ALLOCA outputs, and PARAMs at the function's pointer
   parameter positions P fn.fn_name. *)
Definition ptr_roots_def:
  ptr_roots (P:string -> num set) fn =
    alloca_roots fn UNION
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

(* MEMTOP observes the memory size, which the static layout changes. *)
Definition fn_ptr_ok_def:
  fn_ptr_ok P fn <=>
    (!inst. MEM inst (fn_insts fn) ==>
            inst.inst_opcode <> MEMTOP /\ inst.inst_opcode <> DRET /\
            ptr_use_ok P (fn_pv P fn) inst) /\
    affine_pointer_ops fn (ptr_roots P fn)
End

(* ===== Ghost provenance ===== *)

Datatype:
  call_frame = <| cf_fn : ir_function;
                  cf_inst : instruction;
                  cf_state : venom_state;
                  cf_params : (num # num) option list;
                  cf_prov : (string, num # num) fmap |>
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

(* ===== Ghost written bytes ===== *)

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

(* The bytes of the sites a step allocates. *)
Definition new_site_bytes_def:
  new_site_bytes s s' =
    {i | ?aid b sz. aid NOTIN FDOM s.vs_allocas /\
                    FLOOKUP s'.vs_allocas aid = SOME (b,sz) /\
                    b <= i /\ i < b + sz}
End

Definition step_written_def:
  step_written inst s s' W =
    (W DIFF new_site_bytes s s') UNION range_bytes (step_writes inst s s')
End

(* ===== Small-step reachability with a call stack ===== *)

(* Rules: entry, a non-terminator other than INVOKE, a terminator entering
   a block, an INVOKE entering its callee, and a callee's return resuming
   its caller after the INVOKE. *)
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
     frame_reachable vs0 ctx [] [] FEMPTY {} fn inst s1)
[~next:]
  (!vs0 ctx stk PG G W fn inst inst' s s' fuel.
     frame_reachable vs0 ctx stk PG G W fn inst s /\ active_inst fn inst s /\
     ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
     step_inst fuel ctx inst s = OK s' /\
     active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
     frame_reachable vs0 ctx stk PG (step_prov PG G inst s')
       (step_written inst s s' W) fn inst'
       (s' with vs_inst_idx := SUC s.vs_inst_idx))
[~block:]
  (!vs0 ctx stk PG G W fn inst inst' s s' s1 fuel.
     frame_reachable vs0 ctx stk PG G W fn inst s /\ active_inst fn inst s /\
     is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
     ~s'.vs_halted /\ enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
     frame_reachable vs0 ctx stk PG (entry_prov fn s' G) W fn inst' s1)
[~call:]
  (!vs0 ctx stk PG G W caller inv s nm ops callee args cs s1 inst.
     frame_reachable vs0 ctx stk PG G W caller inv s /\
     active_inst caller inv s /\
     inv.inst_opcode = INVOKE /\ decode_invoke inv = SOME (nm, ops) /\
     lookup_function nm ctx.ctx_functions = SOME callee /\
     eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
     enters_block callee cs s1 /\ active_inst callee inst s1 ==>
     frame_reachable vs0 ctx
       (<| cf_fn := caller; cf_inst := inv; cf_state := s;
           cf_params := PG; cf_prov := G |> :: stk)
       (MAP (op_prov G) ops) FEMPTY W callee inst s1)
[~ret:]
  (!vs0 ctx f stk PG G W fn rinst s ret s_end s' inst' fuel.
     frame_reachable vs0 ctx (f::stk) PG G W fn rinst s /\
     active_inst fn rinst s /\
     step_inst fuel ctx rinst s = IntRet ret s_end /\
     bind_outputs f.cf_inst.inst_outputs ret.iret_values
       (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) =
       SOME s' /\
     active_inst f.cf_fn inst'
       (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
     frame_reachable vs0 ctx stk f.cf_params
       (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs))) W
       f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx))
End

(* ===== The per-state part and the stage fact ===== *)

(* Each nonempty access lies inside the site its address operand points
   into, and reads only written bytes. *)
Definition access_ok_def:
  access_ok G W inst s <=>
    (!off len.
       MEM (off,len) (source_memory_write_ranges inst s) /\ len <> 0 ==>
       ?ops v b sz. mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
                    FLOOKUP G v = SOME (b,sz) /\
                    b <= off /\ off + len <= b + sz) /\
    (!off len.
       MEM (off,len) (source_memory_read_ranges inst s) /\ len <> 0 ==>
       (?ops v b sz. mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
                     FLOOKUP G v = SOME (b,sz) /\
                     b <= off /\ off + len <= b + sz) /\
       !i. off <= i /\ i < off + len ==> i IN W)
End

Definition ptr_discipline_def:
  ptr_discipline ctx vs <=>
    ?P. EVERY (fn_ptr_ok P) ctx.ctx_functions /\
        !stk PG G W fn inst s.
          frame_reachable vs ctx stk PG G W fn inst s ==>
          access_ok G W inst s
End
