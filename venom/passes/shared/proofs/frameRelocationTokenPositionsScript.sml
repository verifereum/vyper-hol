Theory frameRelocationTokenPositions
Ancestors frameResolvedTrace frameActivationLifetime frameActivationCache
  frameResolvedOrigins list arithmetic

(* Only live tokens have a promised interpretation; absent tokens default to 0. *)
Definition token_positions_def:
  token_positions positions [] owners (token,aid) = 0 /\
  token_positions positions (birth::ids) [] (token,aid) = 0 /\
  token_positions positions (birth::ids) (owner::owners) (token,aid) =
    if token = birth then positions owner aid
    else token_positions positions ids owners (token,aid)
End

Theorem token_positions_index:
  !ids owners k aid.
  ALL_DISTINCT ids /\ LENGTH ids = LENGTH owners /\ k < LENGTH ids ==>
  token_positions positions ids owners (EL k ids,aid) = positions (EL k owners) aid
Proof
  Induct >> simp[] >> Cases_on `owners` >> simp[] >>
  rpt gen_tac >> strip_tac >> Cases_on `k` >>
  gvs[token_positions_def] >>
  rename1 `if EL n ids = head then _ else _` >>
  `EL n ids <> head` by metis_tac[MEM_EL] >> simp[token_positions_def]
QED

Theorem token_positions_head[simp]:
  token_positions positions (birth::ids) (owner::owners) (birth,aid) =
  positions owner aid
Proof
  simp[token_positions_def]
QED

Theorem token_positions_saved:
  birth <> token ==>
  token_positions positions (birth::token::ids) (current::owner::owners) (token,aid) =
  positions owner aid
Proof
  simp[token_positions_def]
QED

Theorem activation_cache_owner_index[local]:
  k <= LENGTH stk /\
  activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
    (LENGTH stk-k) owner aid site ==>
  owner = EL k (fn::MAP (\f. f.cf_fn) stk)
Proof
  Cases_on `k` >> simp[activation_cache_def] >> rpt strip_tac >> gvs[] >>
  `LENGTH stk - SUC (LENGTH stk - SUC n) = n` by decide_tac >>
  simp[EL_MAP]
QED

Theorem resolved_token_position:
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  lifetime_ok n (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  FLOOKUP rv v = SOME ((token,aid),site) ==>
  ?d owner.
    activation_cache (JointConfig stk PG G tn fn inst s oms om hs h) d owner aid site /\
    token_positions positions (birth::ids) (fn::MAP (\f. f.cf_fn) stk) (token,aid) =
      positions owner aid
Proof
  strip_tac >> drule_all resolved_current_owner >> strip_tac >>
  `ALL_DISTINCT (birth::ids) /\ LENGTH ids = LENGTH stk` by
    fs[lifetime_ok_def, activation_depth_def] >>
  `owner = EL k (fn::MAP (\f. f.cf_fn) stk)` by
    (irule activation_cache_owner_index >>
     (conj_tac >- (fs[] >> decide_tac)) >>
     goal_assum (drule_at Any)) >>
  qexistsl_tac [`LENGTH stk-k`, `owner`] >> simp[] >>
  qpat_x_assum `EL k (birth::ids) = token` (SUBST1_TAC o SYM) >>
  irule token_positions_index >> simp[]
QED

Theorem resolved_operand_position:
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  lifetime_ok n (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  resolved_op rv op = SOME ((token,aid),site) ==>
  ?d owner.
    activation_cache (JointConfig stk PG G tn fn inst s oms om hs h) d owner aid site /\
    token_positions positions (birth::ids) (fn::MAP (\f. f.cf_fn) stk) (token,aid) =
      positions owner aid
Proof
  Cases_on `op` >> simp[resolved_op_def] >>
  metis_tac[resolved_token_position]
QED
