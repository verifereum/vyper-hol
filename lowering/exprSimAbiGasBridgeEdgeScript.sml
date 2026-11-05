(* The relabeled-observer gas bridges without the end-block premise on the
   counted function: when the fragment ends in a fresh empty block, the
   counted path stops at the jump into it, at index 0, before any PHIs
   there run.  The observer-side (fn') premises are unchanged. *)
Theory exprSimAbiGasBridgeEdge
Ancestors
  exprSimAbiGasBridge

Theorem frag_exec_gas_path_relabel_edge:
  !ctx sa sb Q R fn s.
    (!L ids fn'.
       LENGTH ids = LENGTH sa.cs_current_insts /\
       fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) fn' /\
       fn_inst_ids_distinct fn' /\ fn'.fn_name = fn.fn_name /\
       (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\
            i.inst_opcode <> NOP ==> MEM i (fn_insts fn)) /\
       (!i. MEM i (fn_insts fn') ==> i.inst_opcode <> INVOKE) /\
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
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
    (?r. gas_marked_path F ctx fn s 0 r /\ exit_result r /\ R r)
Proof
  cheat
QED

Theorem abi_decode_sim_gas_path_relabel_edge:
  !ctx sa sb Q fn s.
    (!L ids fn'.
       LENGTH ids = LENGTH sa.cs_current_insts /\
       fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) fn' /\
       fn_inst_ids_distinct fn' /\ fn'.fn_name = fn.fn_name /\
       (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\
            i.inst_opcode <> NOP ==> MEM i (fn_insts fn)) /\
       (!i. MEM i (fn_insts fn') ==> i.inst_opcode <> INVOKE) /\
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
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED
