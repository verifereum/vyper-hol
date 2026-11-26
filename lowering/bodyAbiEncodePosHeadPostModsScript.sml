(* The positional head's witnesses come from the actual cons compilation.
   The singleton packed post records resources, not a singleton compilation. *)
Theory bodyAbiEncodePosHeadPostMods
Ancestors
  bodyAbiEncodePackedPostMods contextRawReachable unitTransformDefs
  vyperState list

Definition abi_encode_pos_head_post_mods_def[nocompute]:
  abi_encode_pos_head_post_mods mods DF lo d ctx func ce cx env
      e sa sm ss vv sv copy es s0 G0 tn0 H (res:value + exception) mid Gm tm m <=>
    ?v. res = INL v /\
        abi_encode_saved_row_mods lo ce cx sa ss e sv v sa sm ss vv copy
          H mid Gm tm m /\
        abi_encode_packed_post_mods mods DF lo d ctx func ce cx env
          [e] [sv] sa ss es s0 G0 tn0 H (INL [v]:value list + exception)
          mid Gm tm m /\
        (!fn inst u. frag_reachable ctx func m fn inst u ==>
                     dalloca_fmp_headroom inst u)
End

Theorem abi_encode_pos_head_post_mods_singleton[local]:
  abi_encode_pos_head_post_mods mods DF lo d ctx func ce cx env
    e sa sm ss vv sv copy es s0 G0 tn0 H (INL v) mid Gm tm m ==>
  abi_encode_packed_post_mods mods DF lo d ctx func ce cx env
    [e] [sv] sa ss es s0 G0 tn0 H (INL [v]:value list + exception) mid Gm tm m /\
  LIST_REL (\(x,z) w.
    ?si sm ss' vv copy.
      abi_encode_saved_row_mods lo ce cx sa ss x z w si sm ss' vv copy H mid Gm tm m)
    (ZIP ([e],[sv])) [v]
Proof
  simp[abi_encode_pos_head_post_mods_def] >> strip_tac >>
  qexistsl_tac [`sa`, `sm`, `ss`, `vv`, `copy`] >> simp[]
QED
