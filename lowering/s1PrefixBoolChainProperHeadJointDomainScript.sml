(* Strict expression-size domain for an actual proper BoolChain head. *)
Theory s1PrefixBoolChainProperHeadJointDomain
Ancestors
  s1PrefixBoolChainHeadAlternative

Theorem bool_chain_proper_head_joint_domain:
  !cx cenv p rv xl sf shadow_sf DF lo ctx shadow_ctx func PG st0 n e sg
     shadow_sg es0 s0 G0 tn0 a rest sa shadow_sa es s G tn.
    bool_chain_actual_reached cx cenv p rv xl sf shadow_sf DF lo ctx shadow_ctx
      func PG st0 n e sg shadow_sg es0 s0 G0 tn0
      (a::rest) sa shadow_sa es s G tn /\
    (a <> e \/ rest <> []) ==>
    expr_size a < expr_size e
Proof
  rpt gen_tac >> strip_tac >>
  drule bool_chain_reached_list_alternative >>
  strip_tac >>
  gvs[]
QED
