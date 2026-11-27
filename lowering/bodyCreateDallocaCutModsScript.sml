Theory bodyCreateDallocaCutMods
Ancestors
  bodyFullIfExpReach contextCodegenRelProps contextRawReachable fragGasOriginPtr
  unitTransformDefs venomLayout venomInst venomState words arithmetic

(* Use headroom only at the fetched DALLOCA on the reached path. *)
Theorem create_dalloca_cut_bound_no_phi:
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  MEM func ctx.ctx_functions /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s0,G0,tn0) marks (OK s,G,tn) /\
  (!fn i u. contextRawReachable$frag_reachable ctx func s0 fn i u ==>
     dalloca_fmp_headroom i u) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = DALLOCA /\
  venomLayout$ceil32 n <= 2 ** 255 + 2 ** 64 ==>
  w2n s.vs_fmp + venomLayout$ceil32 n < dimword (:256)
Proof
  strip_tac >>
  `contextRawReachable$frag_reachable ctx func s func inst s` by
    (irule frag_reachable_start >> drule_all_then ACCEPT_TAC lookup_instruction_active) >>
  `dalloca_fmp_headroom inst s` by
    (drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]) >>
  qpat_x_assum `dalloca_fmp_headroom inst s` mp_tac >>
  qpat_x_assum `venomLayout$ceil32 n <= _` mp_tac >>
  simp[dalloca_fmp_headroom_def,MAX_DEF] >>
  rw[] >> decide_tac
QED
