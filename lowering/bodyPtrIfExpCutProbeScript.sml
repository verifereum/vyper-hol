Theory bodyPtrIfExpCutProbe
Ancestors fragGasPathPtr venomInst exprLoweringProps

(* Prefix truncation makes the endpoint unavailable to every edge,
   independently of its instruction's ghost or gas behavior. *)
Theorem ifexp_endpoint_no_edge:
  !D lo ctx fn PG G tn s n G' tn' r bb.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    LENGTH bb.bb_instructions <= s.vs_inst_idx ==>
    ~gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' r
Proof
  rpt strip_tac >>
  gvs[gas_path_ptr_edge_def, get_instruction_def]
QED

(* The caller function cannot actually be replaced while ctx is fixed:
   alloca_room pins it to the unique lookup at its name. *)
Theorem ifexp_frame_function_rigid:
  !ctx fn cut ce cx es s ce' cx' es' s'.
    stmt_state_rel ctx fn ce cx es s /\
    stmt_state_rel ctx cut ce' cx' es' s' /\
    cut.fn_name = fn.fn_name ==> cut = fn
Proof
  rpt strip_tac >>
  gvs[stmt_state_rel_def, alloca_room_def]
QED
