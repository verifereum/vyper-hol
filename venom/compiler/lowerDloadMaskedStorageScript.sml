Theory lowerDloadMaskedStorage
Ancestors
  lowerDloadSharedState lowerDloadOwnership venomExecSemantics
  ptrDiscipline venomState finite_map pred_set combin

(* One key-update interface for both persistent and transient storage. *)
Theorem ld_key_taint_update:
  key_taint (key_update X key m) q =
    if q = key then m INTER count 32 else key_taint X q
Proof
  rw[key_taint_def, key_update_def, EXTENSION] >> metis_tac[]
QED

Theorem ld_storage_masked_update:
  storage_agree_except X st tt /\ word_agree_except (m INTER count 32) x y ==>
  storage_agree_except (key_update X key m)
    ((key =+ x) st) ((key =+ y) tt)
Proof
  simp[storage_agree_except_def, ld_key_taint_update] >>
  rpt strip_tac >> Cases_on `k = key` >> simp[combinTheory.APPLY_UPDATE_THM]
QED

(* The package permits masked differences at EVERY account. A write clears
   the key mask globally, but changes only the current account. This probe
   isolates that mismatch before attempting an invalid closure theorem. *)
Theorem ld_transient_global_mask_probe:
  (!a. storage_agree_except ({0w} CROSS count 32)
    (\k:bytes32. (0w:bytes32)) (\k:bytes32. if k=0w then (1w:bytes32) else (0w:bytes32))) /\
  ~(!a:160 word. storage_agree_except
    (key_update ({0w} CROSS count 32) 0w {})
    ((if a=0w then (0w =+ 0w) (\k:bytes32. (0w:bytes32)) else (\k:bytes32. (0w:bytes32))))
    ((if a=0w then (0w =+ 0w) (\k:bytes32. if k=0w then (1w:bytes32) else (0w:bytes32))
      else (\k:bytes32. if k=0w then (1w:bytes32) else (0w:bytes32)))))
Proof
  conj_tac
  >- (rw[storage_agree_except_def, key_taint_def, word_agree_except_def] >>
      Cases_on `k=0w` >> gvs[] >> REFL_TAC) >>
  disch_then (qspec_then `1w` mp_tac) >>
  simp[storage_agree_except_def] >>
  qexists_tac `0w` >>
  simp[ld_key_taint_update, word_agree_except_def] >>
  qexists_tac `31` >>
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  EVAL_TAC >> simp[] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem ld_noncurrent_identity:
  (!a. a <> s.vs_call_ctx.cc_address ==>
    (s.vs_accounts a).storage = (s.vs_accounts a).storage) /\
  (!a. a <> s.vs_call_ctx.cc_address ==>
    s.vs_transient a = s.vs_transient a)
Proof
  simp[]
QED

Theorem ld_noncurrent_setup_callee:
  (!a. a <> s.vs_call_ctx.cc_address ==>
    (s.vs_accounts a).storage = (t.vs_accounts a).storage) /\
  (!a. a <> s.vs_call_ctx.cc_address ==>
    s.vs_transient a = t.vs_transient a) /\
  setup_callee fn args s = SOME s' /\
  setup_callee gn bs t = SOME t' ==>
  (!a. a <> s'.vs_call_ctx.cc_address ==>
    (s'.vs_accounts a).storage = (t'.vs_accounts a).storage) /\
  (!a. a <> s'.vs_call_ctx.cc_address ==>
    s'.vs_transient a = t'.vs_transient a)
Proof
  simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem ld_noncurrent_merge_callee:
  (!a. a <> cs.vs_call_ctx.cc_address ==>
    (cs.vs_accounts a).storage = (ct.vs_accounts a).storage) /\
  (!a. a <> cs.vs_call_ctx.cc_address ==>
    cs.vs_transient a = ct.vs_transient a) /\
  cs.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
  ct.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address /\
  s.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address ==>
  (!a. a <> (merge_callee_state s cs).vs_call_ctx.cc_address ==>
    ((merge_callee_state s cs).vs_accounts a).storage =
      ((merge_callee_state t ct).vs_accounts a).storage) /\
  (!a. a <> (merge_callee_state s cs).vs_call_ctx.cc_address ==>
    (merge_callee_state s cs).vs_transient a =
      (merge_callee_state t ct).vs_transient a)
Proof
  simp[merge_callee_state_def]
QED
