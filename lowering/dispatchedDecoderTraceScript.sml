(* Concrete zero-event trace constructors for actual calldata decoders. *)
Theory dispatchedDecoderTrace
Ancestors
  fragGasOriginPtr fragGasOrigin fragGasPathPtr gasEvents gasCount
  venomExecSemantics venomState venomInst list arithmetic

Theorem dispatched_decoder_joint_step:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst s = OK t /\
  ~is_terminator inst.inst_opcode /\ ~t.vs_halted /\
  gas_events_step fuel ctx fn.fn_name inst s = [] /\
  gas_count_step fuel ctx inst s = 0 /\
  mem_safe_step fuel ctx inst s /\
  (!D. ptr_safe_step D lo fuel ctx fn PG G tn inst s) /\
  (G',tn') = ghost_step fuel ctx PG G tn inst s ==>
  !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK (t with vs_inst_idx := SUC s.vs_inst_idx),G',tn')
Proof
  rpt strip_tac >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG)
     (s,G,tn) [] (OK (t with vs_inst_idx := SUC s.vs_inst_idx),G',tn')` by
    (simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
     conj_tac >> qexists_tac `fuel` >> simp[]) >>
  `~(t with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by simp[] >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

Theorem dispatched_decoder_joint_then:
  gas_origin_ptr_path cx (s,G,tn) [] (OK u,H,v) /\
  gas_origin_ptr_path cx (u,H,v) [] (OK t,Kghost,w) ==>
  gas_origin_ptr_path cx (s,G,tn) [] (OK t,Kghost,w)
Proof
  metis_tac[gas_origin_ptr_path_append, APPEND]
QED
