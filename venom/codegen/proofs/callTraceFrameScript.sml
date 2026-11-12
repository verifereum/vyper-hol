(*
 * Account frame laws for the entries of a frame's call trace: a predicate
 * of one account's state and transient storage that every re-entry into the
 * account preserves holds of an entry's outcome snapshot whenever it holds
 * of its request snapshot.
 *
 * TOP-LEVEL: call_trace_account_transient_frame
 *)
Theory callTraceFrame
Ancestors
  callTrace frameObsStep vfmExecution vfmExecutionProp vfmAccountFrame
  vfmState vfmSameFrame callTraceCallEffects callTraceCreateEffects
  callTraceFrameProvenance callTraceChildFrame

Theorem observable_same_depth_fields[local]:
  wf_state s /\
  (FST (HD s.contexts)).msgParams.callee = a /\
  observable_call (FST (HD s.contexts)) /\
  step s = (INL u,t) /\ LENGTH t.contexts = LENGTH s.contexts ==>
  (lookup_account a t.rollback.accounts).code =
    (lookup_account a s.rollback.accounts).code /\
  (lookup_account a t.rollback.accounts).storage =
    (lookup_account a s.rollback.accounts).storage /\
  t.rollback.tStorage a = s.rollback.tStorage a
Proof
  strip_tac >> `s.contexts <> []` by gvs[wf_state_def] >>
  Cases_on `LENGTH (FST (HD s.contexts)).msgParams.code <=
            (FST (HD s.contexts)).pc` >>
  gvs[observable_call_def, next_opcode_def] >>
  qpat_x_assum `step s = _` mp_tac >>
  simp[step_def, get_current_context_def, bind_def, ignore_bind_def,
       return_def, step_inst_def, inc_pc_or_jump_def, is_call_def,
       handle_def] >>
  qmatch_goalsub_abbrev_tac
    `case result of (INL x,ss) => (INL (),ss) | (INR e,ss) => (INR e,ss)` >>
  Cases_on `result` >> Cases_on `q` >> simp[] >> strip_tac >>
  gvs[markerTheory.Abbrev_def]
  >>~- ([`_ = step_call op s`],
        irule handled_call_same_depth_fields >> simp[handle_def] >>
        qexists_tac `op` >>
        qpat_x_assum `_ = step_call op s` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  rename1 `_ = step_create two s` >>
  irule handled_create_same_depth_fields >> simp[handle_def] >>
  qexists_tac `two` >>
  qpat_x_assum `_ = step_create two s` (fn th => rewrite_tac[GSYM th]) >> simp[]
QED

Theorem observable_push_initializes_account[local]:
  wf_state s /\
  (FST (HD s.contexts)).msgParams.callee = a /\
  observable_call (FST (HD s.contexts)) /\
  step s = (INL u,c) /\ LENGTH s.contexts < LENGTH c.contexts /\
  (!acc acc' ts. P (acc,ts) /\ foreign_account_change acc acc' ==> P (acc',ts)) /\
  (!acc acc' ts. P (acc,ts) /\ acc'.code = acc.code /\
                  acc'.storage = acc.storage ==> P (acc',ts)) /\
  P (lookup_account a s.rollback.accounts,s.rollback.tStorage a) ==>
  P (lookup_account a c.rollback.accounts,c.rollback.tStorage a) /\
  P (lookup_account a (SND (HD c.contexts)).accounts,
     (SND (HD c.contexts)).tStorage a)
Proof
  strip_tac
  >> `s.contexts <> []` by gvs[wf_state_def]
  >> drule_all step_push_transient >> strip_tac
  >> drule_all vfmRunCallTheory.step_grow_dispatch >> strip_tac
  >- (drule_all step_call_push_foreign_accounts >> metis_tac[])
  >> drule_all vfmStoragePredicatesTheory.step_create_reaches_proceed_create
  >> strip_tac
  >> drule_all vfmStoragePredicatesTheory.call_prefix_contexts >> strip_tac
  >> drule_all vfmStoragePredicatesTheory.proceed_create_frame_effects >> strip_tac
  >> gvs[vfmStaticCallsTheory.cp_rel_def]
  >> reverse conj_tac
  >- (first_x_assum irule
      >> qexists_tac `lookup_account (FST (HD s.contexts)).msgParams.callee s.rollback.accounts`
      >> simp[increment_nonce_def, lookup_account_def, update_account_def,
              combinTheory.APPLY_UPDATE_THM])
  >> qmatch_goalsub_abbrev_tac `transfer_value sender address value accounts`
  >> `((lookup_account sender (transfer_value sender address value accounts)).code =
        (lookup_account sender s.rollback.accounts).code /\
       (lookup_account sender (transfer_value sender address value accounts)).storage =
        (lookup_account sender s.rollback.accounts).storage) \/
      foreign_account_change (lookup_account sender s.rollback.accounts)
        (lookup_account sender (transfer_value sender address value accounts))` by
    (Cases_on `sender = address`
     >> simp[Abbr `accounts`, foreign_account_change_def,
             transfer_value_preserves_code, transfer_value_preserves_storage,
             increment_nonce_def, clear_storage_def, lookup_account_def,
             update_account_def, combinTheory.APPLY_UPDATE_THM]
     >> gvs[lookup_account_def])
  >> metis_tac[]
QED

(* a is the account the frame executes as.  P must survive what a frame not
   executing as a can do to a (foreign_account_change), and what a's own frame
   does to a's account when it issues a call or create without entering a
   frame that executes as a (balance and nonce; code and storage stay).
   The rely covers the frames executing as a entered during a child's run:
   either pushed non-statically by a frame not executing as a (as in
   run_call_account_transient_frame), or pushed directly by this frame at an
   observable call.

   Why it holds (a sketch, not a prescription): every entry is either
   - recorded at a same-depth observable step of es's frame (precompile calls,
     which push, run and pop inside one step; calls and creates that abort;
     a create collision): a's code and storage stay, tStorage is untouched,
     so the second closure applies; or
   - recorded when a child c, pushed at an observable step, returns:
     P (c.rollback) and P (c's saved rollback) follow from P (s.rollback) by
     the closures (value transfer, the creator's nonce bump; a create whose
     address is a itself, where a is not yet created, by the first closure),
     and the outcome is the rollback run_call c ends at.  If c's callee is a,
     the rely's second disjunct covers c directly; otherwise
     run_call_account_transient_frame applies to c, its rely obligations
     falling under the first disjunct via run_call_reaches_trans.
   Pushes the trace doesn't record (CALLCODE) add no entry, and each entry
   carries its own P on its request, so nothing is needed between entries. *)
Theorem call_trace_account_transient_frame:
  wf_state es /\
  (FST (HD es.contexts)).msgParams.callee = a /\
  (!acc acc' ts. P (acc, ts) /\ foreign_account_change acc acc' ==>
                 P (acc', ts)) /\
  (!acc acc' ts. P (acc, ts) /\ acc'.code = acc.code /\
                 acc'.storage = acc.storage ==> P (acc', ts)) /\
  (!e r e'.
     (FST (HD e.contexts)).msgParams.callee = a /\
     wf_state e /\
     P (lookup_account a e.rollback.accounts, e.rollback.tStorage a) /\
     (2 <= LENGTH e.contexts ==>
        P (lookup_account a (SND (HD e.contexts)).accounts,
           (SND (HD e.contexts)).tStorage a)) /\
     (?s u. run_call_reaches es s /\
            LENGTH es.contexts <= LENGTH s.contexts /\
            wf_state s /\
            P (lookup_account a s.rollback.accounts, s.rollback.tStorage a) /\
            step s = (INL u, e) /\
            LENGTH s.contexts < LENGTH e.contexts /\
            ((FST (HD s.contexts)).msgParams.callee <> a /\
             ~(FST (HD e.contexts)).msgParams.static \/
             LENGTH s.contexts = LENGTH es.contexts /\
             observable_call (FST (HD s.contexts)))) /\
     run_call e = SOME (r, e') ==>
     P (lookup_account a e'.rollback.accounts, e'.rollback.tStorage a)) /\
  MEM (rq, oc) (call_trace es) /\
  P (lookup_account a rq.cr_accounts, rq.cr_tStorage a) ==>
  P (lookup_account a oc.co_accounts, oc.co_tStorage a)
Proof
  strip_tac
  >> drule_all call_trace_entry_provenance >> strip_tac
  >- (drule_all observable_same_depth_fields >> strip_tac
      >> gvs[] >> metis_tac[])
  >> `LENGTH s.contexts < LENGTH c.contexts` by decide_tac
  >> `P (lookup_account a s.rollback.accounts,s.rollback.tStorage a)` by gvs[]
  >> drule_all observable_push_initializes_account >> strip_tac
  >> `wf_state c` by
       (drule vfmRunCallTheory.step_preserves_wf_state >> simp[])
  >> `P (lookup_account a t.rollback.accounts,t.rollback.tStorage a)` by
       (irule observable_child_account_transient_frame
        >> conj_tac >- first_assum ACCEPT_TAC
        >> qexistsl [`c`,`es`,`INL ()`,`s`,`u`]
        >> conj_tac >- (qpat_x_assum `!e r e'. _` MATCH_ACCEPT_TAC)
        >> rpt conj_tac >> asm_rewrite_tac[])
  >> gvs[]
QED
