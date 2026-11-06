(* A local counted-edge exclusion; no source reachability is assumed. *)
Theory bodyPtrStructLitCallPath
Ancestors bodyPtrStructLitCallExclusion fragGasPathPtr

Theorem literal_mload_not_gas_path_ptr_edge:
  !D ctx fn PG G tn s n G' tn' r bb inst a.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode = MLOAD /\ inst.inst_operands = [Lit a] /\
    ~in_revert_forward fn s ==>
    ~gas_path_ptr_edge D 0 ctx fn PG G tn s n G' tn' r
Proof
  rpt strip_tac >>
  gvs[gas_path_ptr_edge_def] >>
  metis_tac[literal_mload_not_ptr_safe_step]
QED
