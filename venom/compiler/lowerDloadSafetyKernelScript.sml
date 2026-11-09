(* Minimal safety-only relocation kernel. No paired execution is asserted. *)
Theory lowerDloadSafetyKernel
Ancestors
  lowerDloadSafetyBoundary ptrDiscipline finite_map pred_set list rich_list

Type ld_site = ``:num # num``;
Type ld_alloc = ``:(ld_site, num # num # num) fmap``;

Definition ld_erase_def:
  ld_erase (A:ld_alloc) k =
    case FLOOKUP A k of SOME (b,c,n) => (b,n) | NONE => (0,0)
End

Definition ld_wordrel_def:
  ld_wordrel (A:ld_alloc) k (x:bytes32) y <=>
    case k of NONE => x = y
    | SOME a => ?b c n. FLOOKUP A a = SOME (b,c,n) /\
                        y = x + n2w c - n2w b
End

Definition ld_memory_def:
  ld_memory lo (A:ld_alloc) tn s t <=>
    (!i. i < lo /\ i NOTIN tn.t_mem ==>
         read_byte i s.vs_memory = read_byte i t.vs_memory) /\
    (!k b c n j. FLOOKUP A k = SOME (b,c,n) /\ j < n /\
                   b+j NOTIN tn.t_mem ==>
         read_byte (b+j) s.vs_memory = read_byte (c+j) t.vs_memory)
End

Definition ld_nonghost_def:
  ld_nonghost tn s t <=>
    s.vs_call_ctx = t.vs_call_ctx /\ s.vs_tx_ctx = t.vs_tx_ctx /\
    s.vs_block_ctx = t.vs_block_ctx /\ s.vs_returndata = t.vs_returndata /\
    s.vs_outcomes = t.vs_outcomes /\ s.vs_gas_readings = t.vs_gas_readings /\
    s.vs_data_section = t.vs_data_section /\
    s.vs_labels = t.vs_labels /\ s.vs_code = t.vs_code /\
    s.vs_fmp = t.vs_fmp /\ s.vs_call_entry_fmp = t.vs_call_entry_fmp /\
    s.vs_initial_fmp = t.vs_initial_fmp /\ s.vs_prev_hashes = t.vs_prev_hashes /\
    s.vs_halted = t.vs_halted /\
    FDOM s.vs_immutables = FDOM t.vs_immutables /\
    (!k x y. FLOOKUP s.vs_immutables k = SOME x /\
              FLOOKUP t.vs_immutables k = SOME y ==>
       word_agree_except (key_taint tn.t_imm k) x y) /\
    (!a. (s.vs_accounts a with storage := (t.vs_accounts a).storage) =
           t.vs_accounts a /\
      storage_agree_except
        (if a = s.vs_call_ctx.cc_address then tn.t_stor else {})
        (s.vs_accounts a).storage (t.vs_accounts a).storage) /\
    (!a. storage_agree_except
        (if a = s.vs_call_ctx.cc_address then tn.t_trans else {})
        (s.vs_transient a) (t.vs_transient a))
End

Theorem ld_wordrel_NONE[simp]:
  ld_wordrel A NONE x y <=> x = y
Proof
  simp[ld_wordrel_def]
QED

Theorem ld_wordrel_SOME:
  ld_wordrel A (SOME a) x y <=>
  ?b c n. FLOOKUP A a = SOME (b,c,n) /\ y = x + n2w c - n2w b
Proof
  simp[ld_wordrel_def]
QED

Theorem ld_memory_low:
  ld_memory lo A tn s t /\ i < lo /\ i NOTIN tn.t_mem ==>
  read_byte i s.vs_memory = read_byte i t.vs_memory
Proof
  simp[ld_memory_def]
QED

Theorem ld_memory_slot:
  ld_memory lo A tn s t /\ FLOOKUP A k = SOME (b,c,n) /\
  j < n /\ b+j NOTIN tn.t_mem ==>
  read_byte (b+j) s.vs_memory = read_byte (c+j) t.vs_memory
Proof
  simp[ld_memory_def] >> metis_tac[]
QED

Theorem ld_nonghost_refl[simp]:
  ld_nonghost tn s s
Proof
  simp[ld_nonghost_def, storage_agree_except_def, word_agree_except_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem ld_wordrel_restrict:
  ld_wordrel A k x y /\ (!a. k = SOME a ==> a IN keep) ==>
  ld_wordrel (DRESTRICT A keep) k x y
Proof
  Cases_on `k` >> simp[ld_wordrel_SOME, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem ld_memory_restrict:
  ld_memory lo A tn s t ==> ld_memory lo (DRESTRICT A keep) tn s t
Proof
  simp[ld_memory_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem ld_erase_restrict_compose:
  FRANGE H SUBSET keep ==>
  ld_erase (DRESTRICT A keep) o_f H = ld_erase A o_f H
Proof
  strip_tac >> simp[fmap_eq_flookup, FLOOKUP_o_f] >> gen_tac >>
  Cases_on `FLOOKUP H x` >> simp[] >>
  `x' IN keep` by metis_tac[SUBSET_DEF, FRANGE_FLOOKUP] >>
  simp[ld_erase_def, FLOOKUP_DRESTRICT]
QED

Theorem ld_wordrel_fresh_update:
  k NOTIN FDOM A /\ ld_wordrel A q x y ==>
  ld_wordrel (A |+ (k,v)) q x y
Proof
  Cases_on `q` >> simp[ld_wordrel_SOME, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  `x' <> k` by (strip_tac >> gvs[FLOOKUP_DEF]) >>
  simp[] >> metis_tac[]
QED

Definition ld_prefix_def:
  ld_prefix C fn X p h t0 t <=>
    h < LENGTH X /\ ?R.
      LENGTH R = SUC h /\ HD R = t0 /\ LAST R = t /\
      (!j. j < h ==> ?u.
        active_inst fn (EL j X) (EL j R) /\
        step_inst 0 C (EL j X) (EL j R) = OK u /\
        EL (SUC j) R = (u with vs_inst_idx := SUC (p+j))) /\
      active_inst fn (EL h X) t
End

Theorem ld_prefix_zero:
  ld_prefix C fn X p 0 t0 t <=>
  0 < LENGTH X /\ t = t0 /\ active_inst fn (EL 0 X) t0
Proof
  simp[ld_prefix_def] >> eq_tac
  >- (rpt strip_tac >>
      Cases_on `R` >> gvs[] >> Cases_on `t'` >> gvs[]) >>
  strip_tac >> gvs[] >> qexists_tac `[t]` >> simp[]
QED

Theorem ld_prefix_bound:
  ld_prefix C fn X p h t0 t ==> h < LENGTH X
Proof
  simp[ld_prefix_def]
QED

Theorem ld_prefix_active:
  ld_prefix C fn X p h t0 t ==> active_inst fn (EL h X) t
Proof
  simp[ld_prefix_def] >> metis_tac[]
QED

Theorem ld_prefix_extend:
  ld_prefix C fn X p h t0 t /\ SUC h < LENGTH X /\
  step_inst 0 C (EL h X) t = OK u /\
  t' = (u with vs_inst_idx := SUC (p+h)) /\
  active_inst fn (EL (SUC h) X) t' ==>
  ld_prefix C fn X p (SUC h) t0 t'
Proof
  simp[ld_prefix_def] >> rpt strip_tac >>
  `R <> []` by (Cases_on `R` >> gvs[]) >>
  qexists_tac `R ++ [t']` >>
  simp[LENGTH_APPEND, HD_APPEND_NOT_NIL, LAST_APPEND] >>
  rpt strip_tac >> Cases_on `j < h`
  >- (simp[EL_APPEND1] >> first_x_assum drule >>
      strip_tac >> qexists_tac `u'` >> simp[EL_APPEND1]) >>
  `j = h` by decide_tac >> gvs[] >>
  simp[EL_APPEND1, EL_APPEND2] >>
  `LAST R = EL h R` by simp[LAST_EL] >>
  qexists_tac `u` >> gvs[]
QED

Theorem ld_prefix_predecessor:
  ld_prefix C fn X p (SUC h) t0 t' ==>
  ?t u. ld_prefix C fn X p h t0 t /\
        step_inst 0 C (EL h X) t = OK u /\
        t' = (u with vs_inst_idx := SUC (p+h))
Proof
  simp[ld_prefix_def] >> rpt strip_tac >>
  `R <> []` by (Cases_on `R` >> gvs[]) >>
  qpat_x_assum `LAST R = t'` mp_tac >> simp[LAST_EL] >> strip_tac >>
  qpat_assum `!j. j < SUC h ==> _` (qspec_then `h` mp_tac) >>
  simp[NoAsms] >> strip_tac >>
  qexistsl_tac [`EL h R`, `u`] >> gvs[] >>
  qexists_tac `TAKE (SUC h) R` >>
  simp[LENGTH_TAKE, HD_TAKE, LAST_EL, EL_TAKE] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `u'` >> simp[EL_TAKE]
QED

(* Prefix positions are exposed without replaying the stored trace. *)
Theorem ld_prefix_position:
  ld_prefix C fn X p h t0 t /\ t0.vs_inst_idx = p ==>
  t.vs_inst_idx = p+h
Proof
  Cases_on `h`
  >- simp[ld_prefix_zero] >>
  strip_tac >> drule ld_prefix_predecessor >> strip_tac >> gvs[]
QED

Theorem ld_prefix_next:
  ld_prefix C fn X p h t0 t /\ t0.vs_inst_idx = p /\
  SUC h < LENGTH X /\ step_inst 0 C (EL h X) t = OK u /\
  active_inst fn (EL (SUC h) X) (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ld_prefix C fn X p (SUC h) t0 (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >>
  `t.vs_inst_idx = p+h` by (irule ld_prefix_position >> metis_tac[]) >>
  irule ld_prefix_extend >> simp[] >> goal_assum (drule_at Any) >> simp[]
QED
