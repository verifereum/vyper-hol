(* Selected allocation identities for safety-only target-prefix coverage. *)
Theory lowerDloadSafetyRelation
Ancestors
  lowerDloadSafetyKernel lowerDloadLiveAllocation lowerDloadScratchSafety
  lowerDloadConfiguredOrigins ptrDiscipline unitShapeDefs finite_map pred_set
  list rich_list venomExecSemantics venomState

Datatype:
  ld_frame = <| lf_serial : num; lf_supply : ir_supply; lf_fn : ir_function;
                lf_src : venom_state; lf_tgt : venom_state;
                lf_H : (string, ld_site) fmap; lf_Q : ld_site option list;
                lf_E : num set; lf_tv : (string, num set) fmap |>
End

Definition ld_charge_def:
  ld_charge frames = SUM (MAP (\f. CARD f.lf_E) frames)
End

Definition ld_image_def:
  ld_image f = FST (lower_dload_function_supply f.lf_supply f.lf_fn)
End

Definition ld_envelope_def:
  ld_envelope u fn s j X p <=>
    ?bb bi ub ui.
      bi < LENGTH fn.fn_blocks /\ EL bi fn.fn_blocks = bb /\
      bb.bb_label = s.vs_current_bb /\ j < LENGTH bb.bb_instructions /\
      ub = SND (lower_dload_blocks_supply u (TAKE bi fn.fn_blocks)) /\
      ui = SND (lower_dload_insts_supply ub (TAKE j bb.bb_instructions)) /\
      X = FST (lower_dload_inst_supply ui (EL j bb.bb_instructions)) /\
      p = LENGTH (FST (lower_dload_insts_supply ub (TAKE j bb.bb_instructions)))
End

Definition ld_private_def:
  ld_private f d ai <=>
    ?bb j bi ub ui inst X.
      bi < LENGTH f.lf_fn.fn_blocks /\ EL bi f.lf_fn.fn_blocks = bb /\
      j < LENGTH bb.bb_instructions /\ EL j bb.bb_instructions = inst /\
      inst.inst_id = d /\ inst.inst_opcode = DLOAD /\
      (?op out. inst.inst_operands = [op] /\ inst.inst_outputs = [out]) /\
      ub = SND (lower_dload_blocks_supply f.lf_supply (TAKE bi f.lf_fn.fn_blocks)) /\
      ui = SND (lower_dload_insts_supply ub (TAKE j bb.bb_instructions)) /\
      X = FST (lower_dload_inst_supply ui inst) /\
      LENGTH X = 4 /\ ai = (HD X).inst_id
End

Definition ld_vars_def:
  ld_vars P A f <=>
    DRESTRICT f.lf_tgt.vs_vars (set (fn_ir_vars f.lf_fn)) =
      DRESTRICT f.lf_tgt.vs_vars (FDOM f.lf_src.vs_vars) /\
    FDOM f.lf_src.vs_vars SUBSET set (fn_ir_vars f.lf_fn) /\
    (!v. v IN set (fn_ir_vars f.lf_fn) ==>
      (v IN FDOM f.lf_src.vs_vars <=> v IN FDOM f.lf_tgt.vs_vars)) /\
    FDOM f.lf_H SUBSET FDOM f.lf_src.vs_vars /\
    FDOM f.lf_H SUBSET fn_pv P f.lf_fn /\
    (!v x y. FLOOKUP f.lf_src.vs_vars v = SOME x /\
              FLOOKUP f.lf_tgt.vs_vars v = SOME y ==>
      if retpc_var f.lf_fn v then T
      else case FLOOKUP f.lf_H v of
        SOME a => ld_wordrel A (SOME a) x y
      | NONE => word_agree_except
          (case FLOOKUP f.lf_tv v of NONE => {} | SOME m => m) x y) /\
    LENGTH f.lf_src.vs_params = LENGTH f.lf_tgt.vs_params /\
    (!j. j < LENGTH f.lf_src.vs_params ==>
      ld_wordrel A (if j < LENGTH f.lf_Q then EL j f.lf_Q else NONE)
        (EL j f.lf_src.vs_params) (EL j f.lf_tgt.vs_params))
End

Definition ld_maps_def:
  ld_maps A f <=>
    FINITE f.lf_E /\
    (!d. d IN f.lf_E ==> ?ai. ld_private f d ai) /\
    (!aid b n. FLOOKUP f.lf_src.vs_allocas aid = SOME (b,n) ==>
      ?c. FLOOKUP A (f.lf_serial,aid) = SOME (b,c,n) /\
          FLOOKUP f.lf_tgt.vs_allocas aid = SOME (c,n)) /\
    (!ai c n. FLOOKUP f.lf_tgt.vs_allocas ai = SOME (c,n) ==>
      (?b. FLOOKUP f.lf_src.vs_allocas ai = SOME (b,n) /\
            FLOOKUP A (f.lf_serial,ai) = SOME (b,c,n)) \/
      (n = 32 /\ ?d. d IN f.lf_E /\ ld_private f d ai)) /\
    (!d ai. d IN f.lf_E /\ ld_private f d ai ==>
      ?c. FLOOKUP f.lf_tgt.vs_allocas ai = SOME (c,32))
End

Definition ld_slots_def:
  ld_slots (A:ld_alloc) frames = {k | ?f aid b c n.
    MEM f frames /\ k = (f.lf_serial,aid) /\
    FLOOKUP f.lf_src.vs_allocas aid = SOME (b,n) /\
    FLOOKUP A k = SOME (b,c,n)}
End

Definition ld_intervals_def:
  ld_intervals lo s <=>
    (!aid b n. FLOOKUP s.vs_allocas aid = SOME (b,n) ==>
      lo <= b /\ b+n <= s.vs_alloca_next) /\
    (!a b n a' b' n'.
      FLOOKUP s.vs_allocas a = SOME (b,n) /\
      FLOOKUP s.vs_allocas a' = SOME (b',n') /\ a <> a' /\ 0 < n /\ 0 < n' ==>
      b+n <= b' \/ b'+n' <= b)
End

Definition ld_sites_def:
  ld_sites frames source = {(j,aid,b,n) | ?f.
    j < LENGTH frames /\ f = EL j frames /\
    FLOOKUP (if source then f.lf_src.vs_allocas else f.lf_tgt.vs_allocas)
      aid = SOME (b,n)}
End

Definition ld_global_def:
  ld_global lo (A:ld_alloc) frames <=>
    (!source j aid b n. (j,aid,b,n) IN ld_sites frames source ==>
      lo <= b /\ b+n <=
        (if source then (HD frames).lf_src.vs_alloca_next
                   else (HD frames).lf_tgt.vs_alloca_next)) /\
    (!source j aid b n j' aid' b' n'.
      (j,aid,b,n) IN ld_sites frames source /\
      (j',aid',b',n') IN ld_sites frames source /\
      (j,aid) <> (j',aid') /\ 0 < n /\ 0 < n' ==>
      b+n <= b' \/ b'+n' <= b) /\
    (!f a. MEM f frames /\
      (a IN FRANGE f.lf_H \/ MEM (SOME a) f.lf_Q) ==> a IN FDOM A)
End

Definition ld_sync_def:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N <=>
    frames <> [] /\ (HD frames).lf_fn = fn /\ (HD frames).lf_src = s /\
    (HD frames).lf_tgt = t /\ (HD frames).lf_tv = tn.t_var /\
    frame_reachable vs0 C stk PG G tn fn inst s /\ active_inst fn inst s /\
    EVERY (fn_ptr_ok P) C.ctx_functions /\
    LENGTH frames = SUC (LENGTH stk) /\
    G = ld_erase A o_f (HD frames).lf_H /\
    PG = MAP (OPTION_MAP (ld_erase A)) (HD frames).lf_Q /\
    ALL_DISTINCT (MAP (\f. f.lf_serial) frames) /\
    EVERY (\f. f.lf_serial < N /\ ld_maps A f /\ ld_vars P A f /\
      ld_intervals lo f.lf_src /\ ld_intervals lo f.lf_tgt /\
      f.lf_src.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
      f.lf_src.vs_current_bb = f.lf_tgt.vs_current_bb /\
      MEM f.lf_fn C.ctx_functions) frames /\
    FDOM A = ld_slots A frames /\
    (!j. j < LENGTH frames ==>
      (EL j frames).lf_tgt.vs_alloca_next =
      (EL j frames).lf_src.vs_alloca_next + 32 * ld_charge (DROP j frames)) /\
    (!j. j < LENGTH frames ==>
      ?X p. ld_envelope (EL j frames).lf_supply (EL j frames).lf_fn
                (EL j frames).lf_src (EL j frames).lf_src.vs_inst_idx X p /\
            (EL j frames).lf_tgt.vs_inst_idx = p) /\
    (!j. j < LENGTH stk ==>
      (EL j stk).cf_fn = (EL (SUC j) frames).lf_fn /\
      (EL j stk).cf_state = (EL (SUC j) frames).lf_src /\
      (EL j stk).cf_prov = ld_erase A o_f (EL (SUC j) frames).lf_H /\
      (EL j stk).cf_params = MAP (OPTION_MAP (ld_erase A)) (EL (SUC j) frames).lf_Q /\
      (EL j stk).cf_tvar = (EL (SUC j) frames).lf_tv) /\
    ld_charge frames <= ctx_dload_count C /\
    ld_memory lo A tn s t /\ ld_nonghost tn s t
End

Definition ld_pair_def:
  ld_pair lo P names Sigma C C' vs0 fn' ti t <=>
    ?stk PG G tn fn inst s t0 A frames N X p h.
      ld_sync lo P C vs0 stk PG G tn fn inst s t0 A frames N /\
      ld_global lo A frames /\
      EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames /\
      (!j k. j < k /\ k < LENGTH frames ==>
        list_precedes (EL j frames).lf_fn.fn_name
                      (EL k frames).lf_fn.fn_name names) /\
      fn' = ld_image (HD frames) /\
      ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
      ld_prefix C' fn' X p h t0 t /\ ti = EL h X
End

Theorem ld_sync_source:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N ==>
  frame_reachable vs0 C stk PG G tn fn inst s /\ active_inst fn inst s
Proof
  simp[ld_sync_def]
QED

Theorem ld_sync_active:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N ==>
  frames <> [] /\ (HD frames).lf_fn = fn /\ (HD frames).lf_src = s /\
  (HD frames).lf_tgt = t /\ (HD frames).lf_tv = tn.t_var /\
  ld_maps A (HD frames) /\ ld_vars P A (HD frames) /\
  ld_intervals lo s /\ ld_intervals lo t
Proof
  simp[ld_sync_def, EVERY_MEM] >> rpt strip_tac >>
  `MEM (HD frames) frames` by (Cases_on `frames` >> gvs[]) >>
  metis_tac[]
QED

Theorem ld_sync_control:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N ==>
  s.vs_current_bb = t.vs_current_bb /\
  s.vs_prev_bb = t.vs_prev_bb
Proof
  simp[ld_sync_def, EVERY_MEM] >> rpt strip_tac >>
  `MEM (HD frames) frames` by (Cases_on `frames` >> gvs[]) >>
  metis_tac[]
QED

Theorem ld_sync_ghosts:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N ==>
  G = ld_erase A o_f (HD frames).lf_H /\
  PG = MAP (OPTION_MAP (ld_erase A)) (HD frames).lf_Q /\
  (!j. j < LENGTH stk ==>
    (EL j stk).cf_fn = (EL (SUC j) frames).lf_fn /\
    (EL j stk).cf_state = (EL (SUC j) frames).lf_src /\
    (EL j stk).cf_prov = ld_erase A o_f (EL (SUC j) frames).lf_H /\
    (EL j stk).cf_params = MAP (OPTION_MAP (ld_erase A)) (EL (SUC j) frames).lf_Q /\
    (EL j stk).cf_tvar = (EL (SUC j) frames).lf_tv)
Proof
  simp[ld_sync_def]
QED

Theorem ld_sync_memory:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N ==>
  ld_memory lo A tn s t /\ ld_nonghost tn s t
Proof
  simp[ld_sync_def]
QED

Theorem ld_sync_frontier:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N ==>
  ld_charge frames <= ctx_dload_count C /\
  t.vs_alloca_next = s.vs_alloca_next + 32 * ld_charge frames
Proof
  simp[ld_sync_def] >> rpt strip_tac >>
  qpat_x_assum `!j. j < LENGTH frames ==> _ = _`
    (qspec_then `0` mp_tac) >>
  Cases_on `frames` >> gvs[]
QED

Theorem ld_maps_original:
  ld_maps A f /\ FLOOKUP f.lf_src.vs_allocas aid = SOME (b,n) ==>
  ?c. FLOOKUP A (f.lf_serial,aid) = SOME (b,c,n) /\
      FLOOKUP f.lf_tgt.vs_allocas aid = SOME (c,n)
Proof
  simp[ld_maps_def]
QED

Theorem ld_maps_private:
  ld_maps A f /\ d IN f.lf_E /\ ld_private f d ai ==>
  ?c. FLOOKUP f.lf_tgt.vs_allocas ai = SOME (c,32)
Proof
  simp[ld_maps_def] >> metis_tac[]
QED

Theorem ld_intervals_exec_alloca:
  ld_intervals lo s /\ lo <= s.vs_alloca_next /\
  exec_alloca inst s sz = OK t ==> ld_intervals lo t
Proof
  simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def, ld_intervals_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  qpat_assum `!aid b n. FLOOKUP _ aid = SOME (b,n) ==> _ /\ _`
    (fn th => imp_res_tac th) >>
  simp[] >> metis_tac[]
QED

(* A newly introduced slot requires no comparison of stale bytes: every
   source byte of that slot must already be covered by the new taint mask. *)
Theorem ld_memory_new_slot:
  ld_memory lo A tn s t /\ tn.t_mem SUBSET tn'.t_mem /\
  (!j. j < n ==> b+j IN tn'.t_mem) ==>
  ld_memory lo (A |+ (k,(b,c,n))) tn' s t
Proof
  simp[ld_memory_def, FLOOKUP_UPDATE, pred_setTheory.SUBSET_DEF] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_private_cong:
  f.lf_supply = g.lf_supply /\ f.lf_fn = g.lf_fn ==>
  (ld_private f d ai <=> ld_private g d ai)
Proof
  simp[NoAsms, ld_private_def] >> rpt strip_tac >> gvs[]
QED

Theorem ld_maps_fresh_original:
  ld_maps A f /\ inst.inst_outputs = [out] /\
  FLOOKUP f.lf_src.vs_allocas inst.inst_id = NONE /\
  FLOOKUP f.lf_tgt.vs_allocas inst.inst_id = NONE /\
  (f.lf_serial,inst.inst_id) NOTIN FDOM A /\
  (!d. ~ld_private f d inst.inst_id) /\
  exec_alloca inst f.lf_src sz = OK s' /\
  exec_alloca inst f.lf_tgt sz = OK t' ==>
  ld_maps (A |+ ((f.lf_serial,inst.inst_id),
    (f.lf_src.vs_alloca_next,f.lf_tgt.vs_alloca_next,w2n sz)))
    (f with <| lf_src := s'; lf_tgt := t' |> )
Proof
  strip_tac >>
  `!d ai. ld_private (f with <| lf_src := s'; lf_tgt := t' |>) d ai = ld_private f d ai` by
    (rpt gen_tac >> irule ld_private_cong >> simp[]) >>
  gvs[exec_alloca_def, update_var_def] >>
  gvs[ld_maps_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_maps_cached_original:
  ld_maps A f /\ FLOOKUP f.lf_src.vs_allocas inst.inst_id = SOME (b,n) /\
  exec_alloca inst f.lf_src sz = OK s' /\
  exec_alloca inst f.lf_tgt sz = OK t' ==>
  ld_maps A (f with <| lf_src := s'; lf_tgt := t' |>)
Proof
  strip_tac >> drule_all ld_maps_original >> strip_tac >>
  `!d ai. ld_private (f with <| lf_src := s'; lf_tgt := t' |>) d ai = ld_private f d ai` by
    (rpt gen_tac >> irule ld_private_cong >> simp[]) >>
  gvs[exec_alloca_def, AllCaseEqs(), update_var_def] >>
  gvs[ld_maps_def] >> metis_tac[]
QED


(* Pure lookup constructor: neither execution records nor word arithmetic
   occur in the proof of the map invariant. *)
Theorem ld_maps_insert_scratch:
  ld_maps A f /\ g.lf_supply = f.lf_supply /\ g.lf_fn = f.lf_fn /\
  g.lf_serial = f.lf_serial /\
  g.lf_src.vs_allocas = f.lf_src.vs_allocas /\
  g.lf_tgt.vs_allocas = f.lf_tgt.vs_allocas |+ (ai,(c,32)) /\
  g.lf_E = d INSERT f.lf_E /\
  ld_private f d ai /\ (!a. ld_private f d a ==> a = ai) /\
  FLOOKUP f.lf_src.vs_allocas ai = NONE ==>
  ld_maps A g
Proof
  strip_tac >>
  `!x y. ld_private g x y = ld_private f x y` by
    (rpt gen_tac >> irule ld_private_cong >> simp[]) >>
  fs[ld_maps_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `aid <> ai` by (strip_tac >> gvs[]) >>
      simp[FLOOKUP_UPDATE] >> metis_tac[]) >>
  conj_tac
  >- (simp[FLOOKUP_UPDATE, AllCaseEqs()] >> rpt strip_tac >>
      metis_tac[]) >>
  rpt strip_tac >>
  Cases_on `ai' = ai` >- simp[FLOOKUP_UPDATE] >>
  simp[FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem ld_maps_target:
  ld_maps A f /\ FLOOKUP f.lf_tgt.vs_allocas ai = SOME (c,n) ==>
  (?b. FLOOKUP f.lf_src.vs_allocas ai = SOME (b,n) /\
        FLOOKUP A (f.lf_serial,ai) = SOME (b,c,n)) \/
  (n = 32 /\ ?d. d IN f.lf_E /\ ld_private f d ai)
Proof
  simp[ld_maps_def] >> metis_tac[]
QED

Theorem ld_maps_scratch:
  ld_maps A f /\ inst.inst_outputs = [out] /\
  ld_private f d inst.inst_id /\
  (!ai. ld_private f d ai ==> ai = inst.inst_id) /\
  FLOOKUP f.lf_src.vs_allocas inst.inst_id = NONE /\
  exec_alloca inst f.lf_tgt (32w:bytes32) = OK t' ==>
  ld_maps A (f with <| lf_tgt := t'; lf_E := d INSERT f.lf_E |>)
Proof
  strip_tac >>
  `w2n (32w:bytes32) = 32` by
    (`dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
     pop_assum (fn th => simp[NoAsms, th, wordsTheory.dimword_def])) >>
  Cases_on `FLOOKUP f.lf_tgt.vs_allocas inst.inst_id`
  >- (irule ld_maps_insert_scratch >>
      qexistsl_tac [`inst.inst_id`, `f.lf_tgt.vs_alloca_next`, `d`, `f`] >>
      gvs[exec_alloca_def, update_var_def]) >>
  PairCases_on `x` >>
  drule_all ld_maps_target >> strip_tac >> gvs[] >>
  irule ld_maps_insert_scratch >>
  qexistsl_tac [`inst.inst_id`, `x0`, `d`, `f`] >>
  gvs[exec_alloca_def, update_var_def] >>
  sym_tac >> irule finite_mapTheory.FUPDATE_ELIM >>
  qpat_x_assum `FLOOKUP f.lf_tgt.vs_allocas _ = SOME _` mp_tac >>
  simp[FLOOKUP_DEF, AllCaseEqs()]
QED

(* Charge is local to the active frame; saved caller charges are unchanged. *)
Theorem ld_charge_scratch:
  ld_maps A f ==>
  ld_charge ((f with <|lf_tgt := t'; lf_E := d INSERT f.lf_E|>)::frames) =
  ld_charge (f::frames) + (if d IN f.lf_E then 0 else 1)
Proof
  strip_tac >>
  `FINITE f.lf_E` by fs[ld_maps_def] >>
  simp[ld_charge_def, CARD_INSERT] >>
  Cases_on `d IN f.lf_E` >> simp[]
QED

Theorem ld_charge_drop_cons:
  ld_charge (DROP j (f::frames)) =
  if j = 0 then CARD f.lf_E + ld_charge frames
  else ld_charge (DROP (j-1) frames)
Proof
  Cases_on `j` >> simp[ld_charge_def]
QED

Theorem ld_charge_empty_push:
  f.lf_E = {} ==> ld_charge (f::frames) = ld_charge frames
Proof
  simp[ld_charge_def]
QED

Theorem ld_charge_drop_scratch:
  ld_maps A f ==>
  ld_charge (DROP j ((f with <|lf_tgt := t'; lf_E := d INSERT f.lf_E|>)::frames)) =
  ld_charge (DROP j (f::frames)) +
    (if j = 0 /\ d NOTIN f.lf_E then 1 else 0)
Proof
  strip_tac >> Cases_on `j` >> simp[] >>
  drule ld_charge_scratch >>
  disch_then (qspecl_then [`t'`, `frames`, `d`] mp_tac) >>
  Cases_on `d IN f.lf_E` >> simp[]
QED

Theorem ld_sites_insert_head:
  g.lf_src.vs_allocas = f.lf_src.vs_allocas |+ (ai,(b,n)) /\
  g.lf_tgt.vs_allocas = f.lf_tgt.vs_allocas |+ (ai,(c,n)) ==>
  ld_sites (g::frames) source SUBSET
    ld_sites (f::frames) source UNION {(0,ai,if source then b else c,n)}
Proof
  strip_tac >>
  simp[SUBSET_DEF, ld_sites_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `j` >> gvs[FLOOKUP_UPDATE, AllCaseEqs()] >>
  Cases_on `source` >> gvs[FLOOKUP_UPDATE, AllCaseEqs()]
QED


Theorem ld_slots_cons:
  ld_slots A (f::frames) = ld_slots A [f] UNION ld_slots A frames
Proof
  simp[ld_slots_def, EXTENSION] >> metis_tac[]
QED

Theorem ld_slots_head_cong:
  g.lf_serial = f.lf_serial /\
  g.lf_src.vs_allocas = f.lf_src.vs_allocas ==>
  ld_slots A (g::frames) = ld_slots A (f::frames)
Proof
  simp[ld_slots_def, EXTENSION] >> metis_tac[]
QED

Theorem ld_slots_empty_push:
  f.lf_src.vs_allocas = FEMPTY ==>
  ld_slots A (f::frames) = ld_slots A frames
Proof
  strip_tac >> once_rewrite_tac[ld_slots_cons] >>
  `ld_slots A [f] = {}` by simp[ld_slots_def, EXTENSION] >>
  simp[]
QED

Theorem ld_slots_restrict:
  ld_slots (DRESTRICT A keep) frames = ld_slots A frames INTER keep
Proof
  simp[ld_slots_def, EXTENSION, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> eq_tac >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_slots_serials:
  k IN ld_slots A frames ==> ?f aid. MEM f frames /\ k = (f.lf_serial,aid)
Proof
  simp[ld_slots_def] >> metis_tac[]
QED

Theorem ld_slots_pop_domain:
  FDOM A = ld_slots A (f::frames) /\
  (!g. MEM g frames ==> g.lf_serial <> f.lf_serial) ==>
  FDOM (DRESTRICT A {k | FST k <> f.lf_serial}) =
  ld_slots (DRESTRICT A {k | FST k <> f.lf_serial}) frames
Proof
  strip_tac >>
  simp[FDOM_DRESTRICT, ld_slots_restrict] >>
  once_rewrite_tac[ld_slots_cons] >>
  simp[EXTENSION, ld_slots_def] >> gen_tac >>
  PairCases_on `x` >> simp[] >> metis_tac[]
QED

Theorem ld_slots_insert_head:
  g.lf_serial = f.lf_serial /\
  g.lf_src.vs_allocas = f.lf_src.vs_allocas |+ (ai,(b,n)) /\
  (!h. MEM h frames ==> h.lf_serial <> f.lf_serial) ==>
  ld_slots (A |+ ((f.lf_serial,ai),(b,c,n))) (g::frames) =
  (f.lf_serial,ai) INSERT ld_slots A (f::frames)
Proof
  strip_tac >>
  simp[ld_slots_def, EXTENSION] >> gen_tac >> PairCases_on `x` >>
  Cases_on `x0 = f.lf_serial` >> Cases_on `x1 = ai` >>
  gvs[FLOOKUP_UPDATE, AllCaseEqs(), SF DNF_ss] >> metis_tac[]
QED

Theorem ld_maps_restrict:
  ld_maps A f /\ (!aid. (f.lf_serial,aid) IN keep) ==>
  ld_maps (DRESTRICT A keep) f
Proof
  simp[ld_maps_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem ld_global_bounds:
  ld_global lo A frames /\ (j,aid,b,n) IN ld_sites frames source ==>
  lo <= b /\ b+n <= (if source then (HD frames).lf_src.vs_alloca_next
                    else (HD frames).lf_tgt.vs_alloca_next)
Proof
  simp[ld_global_def] >> metis_tac[]
QED

Theorem ld_global_separate:
  ld_global lo A frames /\
  (j,aid,b,n) IN ld_sites frames source /\
  (j',aid',b',n') IN ld_sites frames source /\
  (j,aid) <> (j',aid') /\ 0 < n /\ 0 < n' ==>
  b+n <= b' \/ b'+n' <= b
Proof
  simp[ld_global_def] >> metis_tac[]
QED

Theorem ld_global_selected:
  ld_global lo A frames /\ MEM f frames /\
  (a IN FRANGE f.lf_H \/ MEM (SOME a) f.lf_Q) ==> a IN FDOM A
Proof
  simp[ld_global_def] >> metis_tac[]
QED

(* A single extension interface covers both ordinary and private sites.
   The source increment is zero for a private target-only allocation. *)
Theorem ld_global_extend_head:
  ld_global lo A (f::frames) /\ FDOM A SUBSET FDOM B /\
  lo <= f.lf_src.vs_alloca_next /\ lo <= f.lf_tgt.vs_alloca_next /\
  (!source. ld_sites (g::frames) source SUBSET
    ld_sites (f::frames) source UNION
      {(0,ai,if source then f.lf_src.vs_alloca_next else f.lf_tgt.vs_alloca_next,sz source)}) /\
  g.lf_src.vs_alloca_next = f.lf_src.vs_alloca_next + sz T /\
  g.lf_tgt.vs_alloca_next = f.lf_tgt.vs_alloca_next + sz F /\
  g.lf_H = f.lf_H /\ g.lf_Q = f.lf_Q ==>
  ld_global lo B (g::frames)
Proof
  strip_tac >>
  qpat_x_assum `!source. _ SUBSET _` (mp_tac o SIMP_RULE (srw_ss()) [SUBSET_DEF]) >>
  strip_tac >>
  rewrite_tac[ld_global_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `((j,aid,b,n) IN ld_sites (f::frames) source) \/
        (j = 0 /\ aid = ai /\
         b = (if source then f.lf_src.vs_alloca_next else f.lf_tgt.vs_alloca_next) /\ n = sz source)` by
        metis_tac[pairTheory.PAIR_EQ] >>
      gvs[]
      >- (drule_all ld_global_bounds >> simp[] >>
          Cases_on `source` >> simp[]) >>
      Cases_on `source` >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `((j,aid,b,n) IN ld_sites (f::frames) source) \/
        (j = 0 /\ aid = ai /\
         b = (if source then f.lf_src.vs_alloca_next else f.lf_tgt.vs_alloca_next) /\ n = sz source)` by
        metis_tac[pairTheory.PAIR_EQ] >>
      `((j',aid',b',n') IN ld_sites (f::frames) source) \/
        (j' = 0 /\ aid' = ai /\
         b' = (if source then f.lf_src.vs_alloca_next else f.lf_tgt.vs_alloca_next) /\ n' = sz source)` by
        metis_tac[pairTheory.PAIR_EQ] >>
      gvs[]
      >- (`(j,aid) <> (j',aid')` by simp[] >>
          drule_all ld_global_separate >> simp[])
      >- (drule_all ld_global_bounds >> simp[])
      >> (drule_all ld_global_bounds >> simp[])) >>
  drule ld_global_selected >> simp[] >> strip_tac >>
  rpt strip_tac >> gvs[] >> fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem ld_global_insert_head:
  ld_global lo A (f::frames) /\ FDOM A SUBSET FDOM B /\
  lo <= f.lf_src.vs_alloca_next /\ lo <= f.lf_tgt.vs_alloca_next /\
  g.lf_src.vs_allocas = f.lf_src.vs_allocas |+ (ai,(f.lf_src.vs_alloca_next,n)) /\
  g.lf_tgt.vs_allocas = f.lf_tgt.vs_allocas |+ (ai,(f.lf_tgt.vs_alloca_next,n)) /\
  g.lf_src.vs_alloca_next = f.lf_src.vs_alloca_next + n /\
  g.lf_tgt.vs_alloca_next = f.lf_tgt.vs_alloca_next + n /\
  g.lf_H = f.lf_H /\ g.lf_Q = f.lf_Q ==>
  ld_global lo B (g::frames)
Proof
  strip_tac >> irule ld_global_extend_head >>
  qexistsl_tac [`A`, `ai`, `f`, `\source. n`] >>
  simp[] >> gen_tac >> irule ld_sites_insert_head >> simp[]
QED

Theorem ld_global_insert_private:
  ld_global lo A (f::frames) /\
  lo <= f.lf_src.vs_alloca_next /\ lo <= f.lf_tgt.vs_alloca_next /\
  g.lf_src.vs_allocas = f.lf_src.vs_allocas /\
  g.lf_tgt.vs_allocas = f.lf_tgt.vs_allocas |+ (ai,(f.lf_tgt.vs_alloca_next,n)) /\
  g.lf_src.vs_alloca_next = f.lf_src.vs_alloca_next /\
  g.lf_tgt.vs_alloca_next = f.lf_tgt.vs_alloca_next + n /\
  g.lf_H = f.lf_H /\ g.lf_Q = f.lf_Q ==>
  ld_global lo A (g::frames)
Proof
  strip_tac >> irule ld_global_extend_head >>
  qexistsl_tac [`A`, `ai`, `f`, `\source. if source then 0 else n`] >>
  simp[] >> gen_tac >>
  simp[SUBSET_DEF, ld_sites_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `j` >> gvs[] >>
  Cases_on `source` >> gvs[FLOOKUP_UPDATE, AllCaseEqs()]
QED

Theorem ld_global_head_cong:
  ld_global lo A (f::frames) /\
  g.lf_src.vs_allocas = f.lf_src.vs_allocas /\
  g.lf_tgt.vs_allocas = f.lf_tgt.vs_allocas /\
  g.lf_src.vs_alloca_next = f.lf_src.vs_alloca_next /\
  g.lf_tgt.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
  g.lf_H = f.lf_H /\ g.lf_Q = f.lf_Q ==>
  ld_global lo A (g::frames)
Proof
  strip_tac >>
  `!source. ld_sites (g::frames) source = ld_sites (f::frames) source` by
    (gen_tac >> simp[ld_sites_def, EXTENSION] >>
     gen_tac >> PairCases_on `x` >> simp[] >>
     Cases_on `x0` >> simp[]) >>
  fs[ld_global_def] >> metis_tac[]
QED

Theorem ld_frontiers_scratch:
  ld_maps A f /\
  (!j. j < LENGTH (f::frames) ==>
    (EL j (f::frames)).lf_tgt.vs_alloca_next =
    (EL j (f::frames)).lf_src.vs_alloca_next +
      32 * ld_charge (DROP j (f::frames))) /\
  t'.vs_alloca_next = f.lf_tgt.vs_alloca_next +
    32 * (if d IN f.lf_E then 0 else 1) ==>
  !j. j < LENGTH (f::frames) ==>
    (EL j ((f with <|lf_tgt := t'; lf_E := d INSERT f.lf_E|>)::frames)).lf_tgt.vs_alloca_next =
    (EL j ((f with <|lf_tgt := t'; lf_E := d INSERT f.lf_E|>)::frames)).lf_src.vs_alloca_next +
      32 * ld_charge (DROP j ((f with <|lf_tgt := t'; lf_E := d INSERT f.lf_E|>)::frames))
Proof
  strip_tac >> gen_tac >> Cases_on `j` >> simp[]
  >- (drule ld_charge_scratch >>
      disch_then (qspecl_then [`t'`, `frames`, `d`] assume_tac) >>
      first_x_assum (qspec_then `0` mp_tac) >>
      simp[arithmeticTheory.LEFT_ADD_DISTRIB]) >>
  first_x_assum (qspec_then `SUC n` mp_tac) >> simp[]
QED

Theorem ld_frontiers_original:
  (!j. j < LENGTH (f::frames) ==>
    (EL j (f::frames)).lf_tgt.vs_alloca_next =
    (EL j (f::frames)).lf_src.vs_alloca_next +
      32 * ld_charge (DROP j (f::frames))) /\
  g.lf_E = f.lf_E /\
  g.lf_src.vs_alloca_next = f.lf_src.vs_alloca_next + n /\
  g.lf_tgt.vs_alloca_next = f.lf_tgt.vs_alloca_next + n ==>
  !j. j < LENGTH (g::frames) ==>
    (EL j (g::frames)).lf_tgt.vs_alloca_next =
    (EL j (g::frames)).lf_src.vs_alloca_next +
      32 * ld_charge (DROP j (g::frames))
Proof
  strip_tac >> gen_tac >> Cases_on `j` >> simp[]
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[ld_charge_def]) >>
  first_x_assum (qspec_then `SUC n'` mp_tac) >> simp[]
QED

Theorem ld_frontiers_tail:
  (!j. j < LENGTH (f::frames) ==>
    (EL j (f::frames)).lf_tgt.vs_alloca_next =
    (EL j (f::frames)).lf_src.vs_alloca_next +
      32 * ld_charge (DROP j (f::frames))) ==>
  !j. j < LENGTH frames ==>
    (EL j frames).lf_tgt.vs_alloca_next =
    (EL j frames).lf_src.vs_alloca_next + 32 * ld_charge (DROP j frames)
Proof
  strip_tac >> gen_tac >> first_x_assum (qspec_then `SUC j` mp_tac) >> simp[]
QED

Theorem ld_frontiers_empty_push:
  f.lf_E = {} /\
  f.lf_tgt.vs_alloca_next = f.lf_src.vs_alloca_next + 32 * ld_charge frames /\
  (!j. j < LENGTH frames ==>
    (EL j frames).lf_tgt.vs_alloca_next =
    (EL j frames).lf_src.vs_alloca_next + 32 * ld_charge (DROP j frames)) ==>
  !j. j < LENGTH (f::frames) ==>
    (EL j (f::frames)).lf_tgt.vs_alloca_next =
    (EL j (f::frames)).lf_src.vs_alloca_next +
      32 * ld_charge (DROP j (f::frames))
Proof
  strip_tac >> gen_tac >> Cases_on `j` >> simp[ld_charge_empty_push]
QED

(* A target-only allocation is disjoint from every live translated slot. *)
Theorem ld_private_slot_separation:
  ld_global lo A (f::fs) /\ EVERY (ld_maps A) (f::fs) /\
  FDOM A = ld_slots A (f::fs) /\
  FLOOKUP f.lf_src.vs_allocas ai = NONE /\
  FLOOKUP f.lf_tgt.vs_allocas ai = SOME (d,m) /\ 0 < m ==>
  lo <= d /\
  (!k b c n. FLOOKUP A k = SOME (b,c,n) /\ 0 < n ==>
    c+n <= d \/ d+m <= c)
Proof
  strip_tac >>
  `(0,ai,d,m) IN ld_sites (f::fs) F` by
    (simp[ld_sites_def] >> qexists_tac `0` >> simp[]) >>
  conj_tac
  >- (drule_all ld_global_bounds >> simp[]) >>
  rpt strip_tac >>
  `k IN ld_slots A (f::fs)` by
    (`k IN FDOM A` by (gvs[FLOOKUP_DEF] >> metis_tac[]) >> metis_tac[]) >>
  `?g aid. MEM g (f::fs) /\ k = (g.lf_serial,aid) /\
    FLOOKUP g.lf_src.vs_allocas aid = SOME (b,n) /\
    FLOOKUP g.lf_tgt.vs_allocas aid = SOME (c,n)` by
    (qpat_x_assum `k IN ld_slots _ _` mp_tac >>
     simp_tac std_ss [ld_slots_def, GSPECIFICATION] >> strip_tac >>
     rename1 `MEM g (f::fs)` >>
     `ld_maps A g` by (fs[EVERY_MEM] >> metis_tac[]) >>
     drule_all ld_maps_original >> strip_tac >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `MEM g (f::fs)` mp_tac >>
  pure_rewrite_tac[MEM_EL] >>
  disch_then (qx_choose_then `j` strip_assume_tac) >> gvs[] >>
  `(j,aid,c,n) IN ld_sites (f::fs) F` by
    (simp[ld_sites_def] >> metis_tac[]) >>
  `(j,aid) <> (0,ai)` by (strip_tac >> gvs[]) >>
  irule ld_global_separate >> simp[] >>
  goal_assum (drule_at (Pat `ld_global _ _ _`)) >>
  metis_tac[]
QED

val _ = if null (hyp ld_private_slot_separation) then ()
  else raise Fail "private slot separation has hypotheses";
