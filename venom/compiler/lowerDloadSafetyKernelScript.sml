(* Minimal safety-only relocation kernel. No paired execution is asserted. *)
Theory lowerDloadSafetyKernel
Ancestors
  lowerDloadSafetyBoundary ptrDiscipline finite_map pred_set

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
    s.vs_outcomes = t.vs_outcomes /\ s.vs_data_section = t.vs_data_section /\
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
