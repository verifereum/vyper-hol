(*
 * Counted paths for GAS-free fragments.
 *
 * frag_exec and abi_decode_sim say what running a fragment reaches, as a
 * run_from simulation; the counted expression judgments need an actual
 * gas_marked_path to that state.  For a fragment that runs no GAS, INVOKE
 * or PHI and never jumps back to the block it starts in, the fragment
 * judgment gives such a path, with a count of 0.
 *)

Theory exprSimAbiGasBridge
Ancestors
  fragGasMode fragExec exprLoweringProps abiDecoderLoop abiEncoderObserver

(* The code a fragment emitted: the instructions after sa's position in the
   block it started, every block it finished after that, and the
   instructions of the block it left open. *)
Definition frag_code_def:
  frag_code (sa:compile_state) (sb:compile_state) =
    let new = emitted_blocks sa sb in
    if NULL new then emitted_insts sa sb
    else DROP (LENGTH sa.cs_current_insts) (LAST new).bb_instructions ++
         FLAT (MAP (\bb. bb.bb_instructions) (FRONT new)) ++
         sb.cs_current_insts
End

(* The fragment runs no GAS, INVOKE, PHI, STOP or RETURN, never jumps back
   to the block it starts in, and leaves open a block of a label it did not
   finish. *)
Definition frag_gas_free_def:
  frag_gas_free (sa:compile_state) (sb:compile_state) <=>
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> PHI /\ i.inst_opcode <> STOP /\
               i.inst_opcode <> RETURN /\
               ~MEM (Label sa.cs_current_bb) i.inst_operands)
          (frag_code sa sb) /\
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sa sb))
End

(* The run_from simulation of frag_exec, taken in a function where the
   fragment's end is followed by STOP, is an actual path in every function
   that has the fragment's code.  Q may not depend on vs_returndata, which
   that STOP clears; R accepts no Halt, so that the STOP is never mistaken
   for an exit of the fragment. *)
Theorem frag_exec_gas_path:
  !ctx sa sb P Q R fn s.
    frag_exec ctx sa sb P Q R /\ cs_extends sa sb /\ frag_gas_free sa sb /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\ (!h. ~R (Halt h)) /\
    fn_has_code sa sb fn /\
    (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
     !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
          phi_prefix_length bb.bb_instructions = 0) /\
    P s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
    (?r. gas_marked_path F ctx fn s 0 r /\ exit_result r /\ R r)
Proof
  cheat
QED

(* The same for a fragment proved in the abi_decode_sim form, such as the
   ABI encoder and decoder executions. *)
Theorem abi_decode_sim_gas_path:
  !ctx sa sb Q fn s.
    (!fn'. fn_has_code sa sb fn' /\ fn_inst_ids_distinct fn' /\
       (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP ==>
            MEM i (fn_insts fn)) /\
       (sa.cs_blocks = sb.cs_blocks \/
        !bb. lookup_block sb.cs_current_bb fn'.fn_blocks = SOME bb ==>
             phi_prefix_length bb.bb_instructions = 0) ==>
       ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
           t.vs_inst_idx = LENGTH sb.cs_current_insts /\
           abi_decode_sim ctx fn' s t) /\
    cs_extends sa sb /\ frag_gas_free sa sb /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
     !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
          phi_prefix_length bb.bb_instructions = 0) /\
    ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

(* ===== Relabeled entry block ===== *)

(* The entry block renamed to L, with its pre-fragment instructions
   replaced by NOPs with the IDs ids. *)
Definition start_relabel_def:
  start_relabel L ids (sa:compile_state) =
    sa with <| cs_current_bb := L;
               cs_current_insts := MAP (\id. mk_inst id NOP [] []) ids |>
End

(* What a fragment run from start_relabel L ids sa ends in, given that
   the run from sa ends in sb. *)
Definition start_swap_def:
  start_swap (sa:compile_state) L ids (sb:compile_state) =
    let pre = MAP (\id. mk_inst id NOP [] []) ids in
    let p = LENGTH sa.cs_current_insts in
    let new = emitted_blocks sa sb in
    if NULL new then
      sb with <| cs_current_bb := L;
                 cs_current_insts := pre ++ DROP p sb.cs_current_insts |>
    else
      sb with cs_blocks :=
        FRONT new ++
        [LAST new with <| bb_label := L;
                          bb_instructions := pre ++ DROP p (LAST new).bb_instructions |>] ++
        DROP (LENGTH new) sb.cs_blocks
End

(* A fragment's code does not depend on its entry block's label or on the
   instructions already in it. *)
Definition frag_start_oblivious_def:
  frag_start_oblivious (m : compile_state -> 'a # compile_state) <=>
    !sa x sb L ids.
      m sa = (x,sb) /\ LENGTH ids = LENGTH sa.cs_current_insts ==>
      m (start_relabel L ids sa) = (x, start_swap sa L ids sb)
End

(* frag_gas_free's opcode conditions alone. *)
Definition frag_ops_free_def:
  frag_ops_free (sa:compile_state) (sb:compile_state) <=>
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> PHI /\ i.inst_opcode <> STOP /\
               i.inst_opcode <> RETURN) (frag_code sa sb)
End

Theorem frag_exec_gas_path_relabel:
  !ctx sa sb Q R fn s.
    (!L ids fn'.
       LENGTH ids = LENGTH sa.cs_current_insts /\
       fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) fn' /\
       fn_inst_ids_distinct fn' /\ fn'.fn_name = fn.fn_name /\
       (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\
            i.inst_opcode <> NOP ==> MEM i (fn_insts fn)) /\
       (sb.cs_current_insts <> [] \/
        !bb. lookup_block sb.cs_current_bb fn'.fn_blocks = SOME bb ==>
             phi_prefix_length bb.bb_instructions = 0) ==>
       (?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
            t.vs_inst_idx = LENGTH sb.cs_current_insts /\
            !fuel r. run_from fuel ctx fn' t = r /\ (!e. r <> Error e) ==>
                     ?fuel'. run_from fuel' ctx fn' (s with vs_current_bb := L) = r) \/
       (?fuel r. run_from fuel ctx fn' (s with vs_current_bb := L) = r /\
                 exit_result r /\ R r)) /\
    sa.cs_blocks <> sb.cs_blocks /\ cs_extends sa sb /\ frag_ops_free sa sb /\
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
    (!t p. Q t ==> Q (t with vs_prev_bb := p)) /\ (!h. ~R (Halt h)) /\
    (!a t b p. R (Abort a t) ==>
       R (Abort a (t with <| vs_current_bb := b; vs_prev_bb := p |>))) /\
    (!v t b p. R (IntRet v t) ==>
       R (IntRet v (t with <| vs_current_bb := b; vs_prev_bb := p |>))) /\
    fn_has_code sa sb fn /\
    (sb.cs_current_insts <> [] \/
     !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
          phi_prefix_length bb.bb_instructions = 0) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
    (?r. gas_marked_path F ctx fn s 0 r /\ exit_result r /\ R r)
Proof
  cheat
QED

Theorem abi_decode_sim_gas_path_relabel:
  !ctx sa sb Q fn s.
    (!L ids fn'.
       LENGTH ids = LENGTH sa.cs_current_insts /\
       fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) fn' /\
       fn_inst_ids_distinct fn' /\ fn'.fn_name = fn.fn_name /\
       (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\
            i.inst_opcode <> NOP ==> MEM i (fn_insts fn)) /\
       (!bb. lookup_block sb.cs_current_bb fn'.fn_blocks = SOME bb ==>
             phi_prefix_length bb.bb_instructions = 0) ==>
       ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
           t.vs_inst_idx = LENGTH sb.cs_current_insts /\
           abi_decode_sim ctx fn' (s with vs_current_bb := L) t) /\
    sa.cs_blocks <> sb.cs_blocks /\ cs_extends sa sb /\ frag_ops_free sa sb /\
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
    (!t p. Q t ==> Q (t with vs_prev_bb := p)) /\
    fn_has_code sa sb fn /\
    (sb.cs_current_insts <> [] \/
     !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
          phi_prefix_length bb.bb_instructions = 0) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED
