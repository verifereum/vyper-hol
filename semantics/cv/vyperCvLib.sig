signature vyperCvLib =
sig
  include Abbrev

  (* GSYM AND_IMP_INTRO and the constructor rewrites of the given types *)
  val pre_constructor_rules : hol_type list -> thm list

  (* Rewrites a [cv_pre] goal's logical structure only, discarding
     impossible constructor premises before visiting their bodies *)
  val mk_pre_cleanup_conv : Rewrite.rewrites -> conv

  (* Assumes cv_size bounds for the goal's cv_fst/cv_snd/c2n subterms *)
  val cv_bounds_tac : tactic
end
