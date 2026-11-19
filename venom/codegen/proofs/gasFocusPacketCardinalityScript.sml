Theory gasFocusPacketCardinality
Ancestors
  dftFinitePacket fnSimSpec finite_map pred_set list

(* Keys are charged to direct source positions, not to the observed readings.
   Thus the estimate includes the unobserved (NONE) slots. *)
Theorem dft_focus_packet_slots_charge:
  dft_focus_packet_rel (N:num) C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,order,NONE,NONE) /\
  (!key.
    MEM key (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e)))) order)) ==>
    ?a e bb bt ps xs ys rho in_state h0 body_entry count front closed brest r.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
      r < LENGTH xs /\ (EL r xs).inst_opcode = GAS /\
      key = (a,e,(EL r xs).inst_id)) ==>
  LENGTH raw_slots <= CARD (FDOM blocks) * context_inst_count C7
Proof
  strip_tac >>
  `!a e bb bt ps xs ys rho in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) ==>
    LENGTH xs <= context_inst_count C7` by suspend "row_length" >>
  qabbrev_tac `keys = FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e)))) order)` >>
  `ALL_DISTINCT keys /\ LENGTH raw_slots = LENGTH keys` by
    (qpat_assum `FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,order,NONE,NONE)`
       (mk_asm "root") >>
     qhdtm_assum `dft_focus_packet_rel` mp_tac >>
     rewrite_tac[dft_focus_packet_rel_def] >> strip_tac >>
     qpat_x_assum `ALL_DISTINCT (AK [])` mp_tac >>
     qpat_x_assum `LENGTH (AM []) = LENGTH (AK [])` mp_tac >>
     qpat_x_assum `raw_slots = AM []` mp_tac >>
     qpat_x_assum `AK = _` mp_tac >>
     qpat_x_assum `Abbrev (keys = _)` mp_tac >>
     asm "root" mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> gvs[markerTheory.Abbrev_def]) >>
  qabbrev_tac `charge = \(k,r).
    (FST k,SND k,(EL r (FST (SND (SND (SND (blocks ' k)))))).inst_id)` >>
  `set keys SUBSET IMAGE charge (FDOM blocks CROSS count (context_inst_count C7))`
    by suspend "charge" >>
  `CARD (set keys) <=
    CARD (IMAGE charge (FDOM blocks CROSS count (context_inst_count C7)))` by
    (irule CARD_SUBSET >> simp[]) >>
  `CARD (IMAGE charge (FDOM blocks CROSS count (context_inst_count C7))) <=
    CARD (FDOM blocks CROSS count (context_inst_count C7))` by
    (irule CARD_IMAGE >> simp[]) >>
  gvs[ALL_DISTINCT_CARD_LIST_TO_SET, CARD_CROSS] >> decide_tac
QED

Resume dft_focus_packet_slots_charge[row_length]:
  rpt strip_tac >>
  qpat_assum `FLOOKUP blocks (a,e) = _` (mk_asm "row") >>
  qhdtm_assum `dft_focus_packet_rel` mp_tac >>
  rewrite_tac[dft_focus_packet_rel_def] >> strip_tac >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,count,front,closed,brest) ==> _`
    mp_tac >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _` (mp_tac o cj 1) >>
  asm "row" mp_tac >> POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,count,front,closed,brest) ==> _`
    drule >> strip_tac >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _` drule >> strip_tac >>
  `MEM bb sf.fn_blocks` by
    (irule venomExecPropsTheory.lookup_block_MEM >> goal_assum (drule_at Any)) >>
  `LENGTH bb.bb_instructions <= context_inst_count C7` by
    (irule context_inst_count_block >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `LENGTH bb.bb_instructions <= _` mp_tac >>
  qpat_x_assum `bb.bb_instructions = ps ++ xs` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[]
QED

Resume dft_focus_packet_slots_charge[charge]:
  simp[SUBSET_DEF] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[IN_IMAGE] >> qexists `((a,e),r)` >>
  simp[IN_CROSS, Abbr `charge`] >>
  gvs[flookup_thm] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Finalise dft_focus_packet_slots_charge
