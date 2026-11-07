Theory frameRelocationTokenPersistence
Ancestors frameRelocationTokenPositions frameActivationLifetime
  frameActivationCache frameJointTransition list arithmetic

Definition config_token_positions_def:
  config_token_positions positions
    (JointConfig stk PG G tn fn inst s oms om hs h) ids key =
  token_positions positions ids (fn::MAP (\f. f.cf_fn) stk) key
End

Theorem token_positions_push:
  token <> birth ==>
  token_positions positions (birth::ids) (owner::owners) (token,aid) =
  token_positions positions ids owners (token,aid)
Proof
  simp[token_positions_def]
QED

Theorem config_token_positions_step:
  joint_transition C q ev q' /\ lifetime_ok n ids q /\
  MEM token ids /\ MEM token (lifetime_step n ev ids) ==>
  config_token_positions positions q' (lifetime_step n ev ids) (token,aid) =
  config_token_positions positions q ids (token,aid)
Proof
  simp[Once joint_transition_cases] >> rpt strip_tac >>
  gvs[lifetime_step_def, config_token_positions_def, lifetime_ok_def,
      activation_depth_def]
  >- (`token <> SUC n` by
        (fs[EVERY_MEM] >> first_x_assum drule >> decide_tac) >>
      simp[token_positions_push]) >>
  Cases_on `ids` >> gvs[] >>
  rename1 `~MEM popped tail` >>
  `token <> popped` by metis_tac[] >> simp[token_positions_push]
QED

(* Reusing a stack depth changes the new activation, not a surviving token. *)
Theorem token_positions_reused_depth_probe[local]:
  token <> fresh /\ token <> departed ==>
  token_positions positions (fresh::token::ids) (callee::owner::owners) (token,aid) =
  token_positions positions (departed::token::ids) (old_callee::owner::owners) (token,aid)
Proof
  simp[token_positions_push]
QED
