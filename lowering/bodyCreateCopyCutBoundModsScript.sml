(* Headroom at the fetched DALLOCA of the linked copy preparation. *)
Theory bodyCreateCopyCutBoundMods
Ancestors
  bodyFullIfExpReach contextCodegenRelProps contextRawReachable
  dallocaBounds unitTransformDefs venomLayout words

Theorem create_copy_cut_bound_mods:
  gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG)
    (s0,G0,tn0) marks (OK s,G,tn) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn' i u. frag_reachable ctx func s0 fn' i u ==> dalloca_fmp_headroom i u) /\
  LENGTH code <= 24576 /\
  gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG)
    (s,G,tn) [] (OK pre,Ga,ta) /\
  lookup_block pre.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb pre.vs_inst_idx = SOME i /\
  i.inst_opcode = DALLOCA ==>
  w2n pre.vs_fmp + venomLayout$ceil32 (LENGTH code + 32) < dimword (:256)
Proof
  strip_tac >>
  `!fn' j u. frag_reachable ctx func s fn' j u ==> dalloca_fmp_headroom j u` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks _`
       (mp_then (Pat `gas_origin_ptr_path _ _ _ _`) mp_tac
          gas_origin_ptr_path_dalloca_fmp_headroom) >>
     asm_rewrite_tac[]) >>
  `!fn' j u. frag_reachable ctx func pre fn' j u ==> dalloca_fmp_headroom j u` by
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] _`
       (mp_then (Pat `gas_origin_ptr_path _ _ _ _`) mp_tac
          gas_origin_ptr_path_dalloca_fmp_headroom) >>
     asm_rewrite_tac[]) >>
  `frag_reachable ctx func pre func i pre` by
    (irule frag_reachable_start >>
     drule_all lookup_instruction_active >> simp[]) >>
  `dalloca_fmp_headroom i pre` by
    (qpat_assum `!fn' j u. frag_reachable ctx func pre fn' j u ==> _`
       (drule_then ACCEPT_TAC)) >>
  `venomLayout$ceil32 (LENGTH code + 32) <= 2 ** 255 + 2 ** 64` by
    (qspecl_then [`LENGTH code + 32`,`1024`] mp_tac
       (GEN_ALL ceil32_le_multiple) >>
     simp[] >> decide_tac) >>
  qpat_x_assum `dalloca_fmp_headroom i pre` mp_tac >>
  qpat_x_assum `venomLayout$ceil32 (LENGTH code + 32) <= _` mp_tac >>
  simp[dalloca_fmp_headroom_def,arithmeticTheory.MAX_DEF] >>
  rw[] >> decide_tac
QED
