Theory extRetNumericLedgerPtr
Ancestors
  abiEncoderInput list rich_list arithmetic

(* Conditional numeric ledgers only: no semantic metadata premise is
   manufactured by these arithmetic facts.  MAP permits head, memory and
   tail offsets to share the same interface. *)

Theorem encoder_ledger_prefix_suc:
  !f xs j H. j < LENGTH xs ==>
    H + SUM (MAP f (TAKE (SUC j) xs)) =
    H + SUM (MAP f (TAKE j xs)) + f (EL j xs)
Proof
  rpt strip_tac >> metis_tac[TAKE_SUC_BY_TAKE, MAP_SNOC, SUM_SNOC, ADD_ASSOC]
QED

Theorem encoder_ledger_prefix_bound:
  !f xs j H. H + SUM (MAP f (TAKE j xs)) <= H + SUM (MAP f xs)
Proof
  rpt gen_tac >> Cases_on `j < LENGTH xs`
  >- (drule abi_encoder_prefix_sum_bound >>
      disch_then (qspec_then `f` mp_tac) >> decide_tac)
  >> simp[TAKE_LENGTH_TOO_LONG]
QED

Theorem encoder_ledger_endpoints:
  (!f xs H. H + SUM (MAP f (TAKE 0 xs)) = H) /\
  (!f xs H. H + SUM (MAP f (TAKE (LENGTH xs) xs)) =
    H + SUM (MAP f xs)) /\
  (!f H j. H + SUM (MAP f (TAKE j [])) = H)
Proof
  simp[]
QED

Theorem encoder_ledger_prefix_mono:
  !f xs i j H. i <= j ==>
    H + SUM (MAP f (TAKE i xs)) <= H + SUM (MAP f (TAKE j xs))
Proof
  rpt strip_tac >>
  qspecl_then [`f`, `TAKE j xs`, `i`, `H`] mp_tac encoder_ledger_prefix_bound >>
  simp[TAKE_TAKE_T]
QED

Theorem encoder_ledger_child_capacity:
  !f xs j H overhead cap.
    j < LENGTH xs /\ overhead + H + SUM (MAP f xs) <= cap ==>
    overhead + (H + SUM (MAP f (TAKE j xs))) + f (EL j xs) <= cap
Proof
  rpt strip_tac >> drule abi_encoder_prefix_sum_bound >>
  disch_then (qspec_then `f` mp_tac) >> decide_tac
QED

Theorem encoder_ledger_child_remaining:
  !f xs j H overhead cap.
    j < LENGTH xs /\ overhead + H + SUM (MAP f xs) <= cap ==>
    f (EL j xs) <= cap - (overhead + H + SUM (MAP f (TAKE j xs)))
Proof
  rpt strip_tac >> drule_all encoder_ledger_child_capacity >> decide_tac
QED

Theorem encoder_ledger_child_address_bound:
  !f xs j H overhead cap base limit.
    j < LENGTH xs /\ overhead + H + SUM (MAP f xs) <= cap /\
    base + cap < limit ==>
    base + overhead + H + SUM (MAP f (TAKE j xs)) + f (EL j xs) < limit
Proof
  rpt strip_tac >> drule_all encoder_ledger_child_capacity >> decide_tac
QED

(* All entries may be zero, including source-memory strides. *)
Theorem encoder_ledger_zero_entries:
  !xs j H. H + SUM (MAP (\x. 0) (TAKE j xs)) = H
Proof
  Induct >> simp[] >> Cases_on `j` >> gvs[]
QED
