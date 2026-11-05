Theory frameActivationLookup
Ancestors frameRelocationTokenPositions frameActivationLifetime frameActivationCache
  frameResolvedTrace frameJointTransition frameResolvedOrigins list arithmetic rat

Definition activation_lookup_def:
  activation_lookup default positions [] owners (token,aid) = default /\
  activation_lookup default positions (birth::ids) [] (token,aid) = default /\
  activation_lookup default positions (birth::ids) (owner::owners) (token,aid) =
    if token = birth then positions owner aid
    else activation_lookup default positions ids owners (token,aid)
End

Definition config_activation_lookup_def:
  config_activation_lookup default positions
    (JointConfig stk PG G tn fn inst s oms om hs h) ids key =
  activation_lookup default positions ids (fn::MAP (\f. f.cf_fn) stk) key
End

Theorem activation_lookup_index:
  !ids owners k aid.
  ALL_DISTINCT ids /\ LENGTH ids = LENGTH owners /\ k < LENGTH ids ==>
  activation_lookup default positions ids owners (EL k ids,aid) =
    positions (EL k owners) aid
Proof
  Induct >> simp[] >> Cases_on `owners` >> simp[] >>
  rpt gen_tac >> strip_tac >> Cases_on `k` >>
  gvs[activation_lookup_def] >>
  rename1 `if EL n ids = head then _ else _` >>
  `EL n ids <> head` by metis_tac[MEM_EL] >> simp[activation_lookup_def]
QED

Theorem activation_lookup_compat:
  !ids owners token aid.
  activation_lookup (0:rat) positions ids owners (token,aid) =
    token_positions positions ids owners (token,aid)
Proof
  Induct >> Cases_on `owners` >> rpt gen_tac >>
  simp[activation_lookup_def, token_positions_def]
QED

Theorem resolved_activation_lookup:
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  lifetime_ok n (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  FLOOKUP rv v = SOME ((token,aid),site) ==>
  ?d owner.
    activation_cache (JointConfig stk PG G tn fn inst s oms om hs h) d owner aid site /\
    activation_lookup default positions (birth::ids) (fn::MAP (\f. f.cf_fn) stk)
      (token,aid) = positions owner aid
Proof
  strip_tac >> drule_all resolved_current_owner >> strip_tac >>
  `ALL_DISTINCT (birth::ids) /\ LENGTH ids = LENGTH stk` by
    fs[lifetime_ok_def, activation_depth_def] >>
  `owner = EL k (fn::MAP (\f. f.cf_fn) stk)` by
    (Cases_on `k` >> gvs[activation_cache_def] >>
     `LENGTH stk - SUC (LENGTH stk - SUC n') = n'` by decide_tac >>
     simp[EL_MAP]) >>
  qexistsl_tac [`LENGTH stk-k`, `owner`] >> simp[] >>
  qpat_x_assum `EL k (birth::ids) = token` (SUBST1_TAC o SYM) >>
  irule activation_lookup_index >> simp[]
QED

Theorem resolved_operand_activation_lookup:
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  lifetime_ok n (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  resolved_op rv op = SOME ((token,aid),site) ==>
  ?d owner.
    activation_cache (JointConfig stk PG G tn fn inst s oms om hs h) d owner aid site /\
    activation_lookup default positions (birth::ids) (fn::MAP (\f. f.cf_fn) stk)
      (token,aid) = positions owner aid
Proof
  Cases_on `op` >> simp[resolved_op_def] >>
  metis_tac[resolved_activation_lookup]
QED

Theorem activation_lookup_push:
  token <> birth ==>
  activation_lookup default positions (birth::ids) (owner::owners) (token,aid) =
  activation_lookup default positions ids owners (token,aid)
Proof
  simp[activation_lookup_def]
QED

Theorem config_activation_lookup_step:
  joint_transition C q ev q' /\ lifetime_ok n ids q /\
  MEM token ids /\ MEM token (lifetime_step n ev ids) ==>
  config_activation_lookup default positions q' (lifetime_step n ev ids) (token,aid) =
  config_activation_lookup default positions q ids (token,aid)
Proof
  simp[Once joint_transition_cases] >> rpt strip_tac >>
  gvs[lifetime_step_def, config_activation_lookup_def, lifetime_ok_def,
      activation_depth_def]
  >- (`token <> SUC n` by
        (fs[EVERY_MEM] >> first_x_assum drule >> decide_tac) >>
      simp[activation_lookup_push]) >>
  Cases_on `ids` >> gvs[] >>
  rename1 `~MEM popped tail` >>
  `token <> popped` by metis_tac[] >> simp[activation_lookup_push]
QED
