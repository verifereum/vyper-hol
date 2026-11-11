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

Theorem ld_key_update_mono:
  Y SUBSET X /\ n SUBSET m ==>
  key_update Y key n SUBSET key_update X key m
Proof
  rw[key_update_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ld_shared_sload:
  ld_shared_state tn un s t ==>
  word_agree_except (key_taint tn.t_stor key) (sload key s) (sload key t)
Proof
  simp[ld_shared_state_def, sload_def, contract_storage_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.lookup_storage_def,
       storage_agree_except_def] >> metis_tac[]
QED

Theorem ld_shared_tload:
  ld_shared_state tn un s t ==>
  word_agree_except (key_taint tn.t_trans key) (tload key s) (tload key t)
Proof
  simp[ld_shared_state_def, tload_def, contract_transient_def,
       vfmStateTheory.lookup_storage_def, storage_agree_except_def] >> metis_tac[]
QED

Theorem ld_noncurrent_sstore:
  (!a. a <> s.vs_call_ctx.cc_address ==>
    (s.vs_accounts a).storage = (t.vs_accounts a).storage) /\
  (!a. a <> s.vs_call_ctx.cc_address ==>
    s.vs_transient a = t.vs_transient a) /\
  s.vs_call_ctx = t.vs_call_ctx ==>
  (!a. a <> (sstore key x s).vs_call_ctx.cc_address ==>
    ((sstore key x s).vs_accounts a).storage =
    ((sstore key y t).vs_accounts a).storage) /\
  (!a. a <> (sstore key x s).vs_call_ctx.cc_address ==>
    (sstore key x s).vs_transient a = (sstore key y t).vs_transient a)
Proof
  simp[sstore_def, combinTheory.APPLY_UPDATE_THM] >> metis_tac[]
QED

Theorem ld_noncurrent_tstore:
  (!a. a <> s.vs_call_ctx.cc_address ==>
    (s.vs_accounts a).storage = (t.vs_accounts a).storage) /\
  (!a. a <> s.vs_call_ctx.cc_address ==>
    s.vs_transient a = t.vs_transient a) /\
  s.vs_call_ctx = t.vs_call_ctx ==>
  (!a. a <> (tstore key x s).vs_call_ctx.cc_address ==>
    ((tstore key x s).vs_accounts a).storage =
    ((tstore key y t).vs_accounts a).storage) /\
  (!a. a <> (tstore key x s).vs_call_ctx.cc_address ==>
    (tstore key x s).vs_transient a = (tstore key y t).vs_transient a)
Proof
  simp[tstore_def, combinTheory.APPLY_UPDATE_THM] >> metis_tac[]
QED

Theorem ld_shared_sstore:
  ld_shared_state tn un s t /\
  (!a. a <> s.vs_call_ctx.cc_address ==>
    (s.vs_accounts a).storage = (t.vs_accounts a).storage) /\
  word_agree_except (m INTER count 32) x y /\ n SUBSET m ==>
  ld_shared_state (tn with t_stor := key_update tn.t_stor key m)
    (un with t_stor := key_update un.t_stor key n)
    (sstore key x s) (sstore key y t)
Proof
  strip_tac >>
  `key_update un.t_stor key n SUBSET key_update tn.t_stor key m` by
    (irule ld_key_update_mono >> gvs[ld_shared_state_def]) >>
  gvs[ld_shared_state_def, sstore_def, vfmStateTheory.lookup_account_def,
      vfmStateTheory.update_storage_def] >>
  conj_tac
  >- (gen_tac >> Cases_on `a = t.vs_call_ctx.cc_address` >>
      simp[combinTheory.APPLY_UPDATE_THM] >>
      qpat_x_assum `!a. _ with storage := _ = _`
        (qspec_then `t.vs_call_ctx.cc_address` mp_tac) >>
      simp[vfmStateTheory.account_state_component_equality]) >>
  gen_tac >> Cases_on `a = t.vs_call_ctx.cc_address`
  >- (simp[combinTheory.APPLY_UPDATE_THM] >>
      irule ld_storage_masked_update >> simp[]) >>
  simp[combinTheory.APPLY_UPDATE_THM, storage_agree_except_def,
       word_agree_except_def]
QED

Theorem ld_shared_tstore:
  ld_shared_state tn un s t /\
  (!a. a <> s.vs_call_ctx.cc_address ==>
    s.vs_transient a = t.vs_transient a) /\
  word_agree_except (m INTER count 32) x y /\ n SUBSET m ==>
  ld_shared_state (tn with t_trans := key_update tn.t_trans key m)
    (un with t_trans := key_update un.t_trans key n)
    (tstore key x s) (tstore key y t)
Proof
  strip_tac >>
  `key_update un.t_trans key n SUBSET key_update tn.t_trans key m` by
    (irule ld_key_update_mono >> gvs[ld_shared_state_def]) >>
  gvs[ld_shared_state_def, tstore_def, vfmStateTheory.update_storage_def] >>
  gen_tac >> Cases_on `a = t.vs_call_ctx.cc_address`
  >- (simp[combinTheory.APPLY_UPDATE_THM] >>
      irule ld_storage_masked_update >> simp[]) >>
  simp[combinTheory.APPLY_UPDATE_THM, storage_agree_except_def,
       word_agree_except_def]
QED
