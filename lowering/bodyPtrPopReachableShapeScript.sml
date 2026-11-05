Theory bodyPtrPopReachableShape
Ancestors
  vyperTypeStoragePreservation vyperStorageLayoutSafety vyperLookupStorage
  vyperStorage vyperState words list

(* The proposed two-level singleton outcome cannot pass the oracle boundary:
   its live child's length is larger than its declared capacity. *)
Theorem pop_live_child_overcapacity_probe:
  read_slot raw off = (1w:bytes32) /\
  read_slot raw (off + 1) = (2w:bytes32) ==>
  ~slots_in_range raw off
    (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (Dynamic 1))
Proof
  strip_tac >>
  simp[Once slots_in_range_def, dimword_def, SF wordsLib.SIZES_ss] >>
  CONV_TAC (DEPTH_CONV numLib.num_CONV) >>
  simp[slots_in_range_def, dimword_def, SF wordsLib.SIZES_ss]
QED

Theorem pop_live_child_contract_exclusion:
  declared_storage_region cx mid name subs = SOME (b,slot,
    ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (Dynamic 1)) /\
  get_storage_backend cx b st = (INL raw,st') /\
  read_slot raw (w2n slot) = (1w:bytes32) /\
  read_slot raw (w2n slot + 1) = (2w:bytes32) ==>
  ~contract_storage_well_formed cx st
Proof
  rpt strip_tac >>
  drule pop_live_child_overcapacity_probe >>
  disch_then drule >>
  gvs[contract_storage_well_formed_def] >>
  metis_tac[]
QED

Theorem pop_live_child_oracle_exclusion:
  st.outcomes = SOME os /\ MEM co os /\
  declared_storage_region cx mid name subs = SOME (b,slot,
    ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (Dynamic 1)) /\
  get_storage_backend cx b
    (st with <|accounts := co.co_accounts; tStorage := co.co_tStorage|>) =
    (INL raw,st') /\
  read_slot raw (w2n slot) = (1w:bytes32) /\
  read_slot raw (w2n slot + 1) = (2w:bytes32) ==>
  ~oracle_storage_ok cx st
Proof
  rpt strip_tac >>
  drule_all pop_live_child_contract_exclusion >>
  gvs[oracle_storage_ok_def, EVERY_MEM] >>
  metis_tac[]
QED
