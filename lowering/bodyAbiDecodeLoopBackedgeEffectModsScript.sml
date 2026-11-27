Theory bodyAbiDecodeLoopBackedgeEffectMods
Ancestors
  bodyFullAbiDecodeLoopPhasesObserved bodyAbiDecodeGuardedEffectBaseMods
  pred_set
Libs
  bodyAbiDecodeGuardedEffectSyntaxLib bodyFullAbiDecodeLoopObservedSyntaxLib

val observed_backedge = BETA_RULE abi_decode_loop_backedge_observed;
val backedge = concl observed_backedge;
val (pre, rest) = dest_imp backedge;
val (disjoint, rest) = dest_imp rest;
val (origin, backedge_post) = dest_imp rest;

val effect_backedge =
  let
    val (ws, body) = strip_exists backedge_post
    val (t, _, tnf) = bodyAbiDecodeGuardedEffectSyntaxLib.triple "backedge" ws
    val vs = free_vars pre
    val effect_post = effect (param vs "s") (param vs "tn") t tnf
    val post = list_mk_exists (ws, mk_conj (body, effect_post))
  in
    close_statement (checked "observed backedge" backedge
      (list_mk_imp ([pre, disjoint, origin], post)))
  end;

Theorem abi_decode_loop_backedge_effect_observed_mods:
  ^effect_backedge
Proof
  rpt gen_tac >> ntac 3 disch_tac >>
  Q.SUBGOAL_THEN `^backedge_post`
    (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf` assume_tac)))
  >- (mp_tac observed_backedge >> asm_rewrite_tac[]) >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  fs[abi_decode_guarded_effect_core_def, SUBSET_DEF]
QED
