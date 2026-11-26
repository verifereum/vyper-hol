Theory bodyMakeElementsMods
Ancestors
  bodyMakeElementsContractMods bodyMakeElementsDriverMods bodyMakeSlotBindMods
  bodyMakeSlotWordMods bodyMakeSlotNonwordMods bodyMakeElementStoreMods

Theorem make_elements_from_transfer_mods:
  make_elements_contract_mods
Proof
  irule make_elements_from_slot_mods >>
  irule make_slot_from_landings_mods >>
  simp_tac bool_ss [make_slot_word_landing_mods] >>
  irule make_slot_nonword_from_transfer_mods >>
  rpt gen_tac >> MATCH_ACCEPT_TAC make_element_transfer_mods
QED
