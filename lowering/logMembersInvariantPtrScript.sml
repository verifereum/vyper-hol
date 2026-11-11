(* Semantic input boundaries for the scalar ABI member traversal. *)
Theory logMembersInvariantPtr
Ancestors
  abiEncoderInputFrame robustCopyTransportPtr representationCleanPtr
  bodyPtrDefs valueEncoding valueEncodingProofs list arithmetic
  stmtSimLogEncodeLayout stmtSimLogScalarMembers abiDecodeRanges

Theorem robust_abi_encoder_input_copy_transport:
  mem_bytes_at db cap mem' = mem_bytes_at sb cap mem /\
  (!i. i < cap ==> (db+i IN m' <=> sb+i IN m)) /\
  (!q. mem_agree_outside m mem q ==>
       abi_encoder_input ei at av sb cap q) ==>
  !q. mem_agree_outside m' mem' q ==>
      abi_encoder_input ei at av db cap q
Proof
  rpt strip_tac >> drule_all copied_window_agree_witness >>
  disch_then (qx_choose_then `mix` strip_assume_tac) >>
  `abi_encoder_input ei at av sb cap mix` by metis_tac[] >>
  drule abi_encoder_input_relocate >>
  disch_then (qspecl_then [`db`, `q`] mp_tac) >> simp[]
QED

Theorem robust_abi_encoder_input_separated_write:
  (!q. mem_agree_outside m mem q ==>
       abi_encoder_input ei at av a cap q) /\
  mem_agree_outside writes mem' mem /\
  (!i. a <= i /\ i < a+cap ==> i NOTIN writes) /\
  (!i. a <= i /\ i < a+cap ==> (i IN m' <=> i IN m)) ==>
  !q. mem_agree_outside m' mem' q ==>
      abi_encoder_input ei at av a cap q
Proof
  rpt strip_tac >> irule robust_abi_encoder_input_copy_transport >>
  qexistsl_tac [`m`, `m'`, `mem`, `mem'`, `a`] >> simp[] >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `i < cap` >>
  `a+i NOTIN writes` by (first_x_assum irule >> decide_tac) >>
  `mem_bytes_at (a+i) 1 mem' = mem_bytes_at (a+i) 1 mem` by
    metis_tac[mem_agree_outside_def] >>
  pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

(* The gap between head and tail is not claimed clean. *)
Theorem clean_head_tail_advance:
  ho+hn <= hl /\
  (!i. d <= i /\ i < d+ho ==> i NOTIN m) /\
  (!i. d+hl <= i /\ i < d+hl+tl ==> i NOTIN m) /\
  (!i. d+ho <= i /\ i < d+ho+hn ==> i NOTIN m') /\
  (!i. d+hl+tl <= i /\ i < d+hl+tl+tn ==> i NOTIN m') /\
  (!i. ~(d+ho <= i /\ i < d+ho+hn) /\
       ~(d+hl+tl <= i /\ i < d+hl+tl+tn) ==>
       (i IN m' <=> i IN m)) ==>
  (!i. d <= i /\ i < d+(ho+hn) ==> i NOTIN m') /\
  (!i. d+hl <= i /\ i < d+hl+(tl+tn) ==> i NOTIN m')
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >> Cases_on `i < d+ho`
      >- (`d <= i /\ i < d+ho /\
           ~(d+ho <= i /\ i < d+ho+hn) /\
           ~(d+hl+tl <= i /\ i < d+hl+tl+tn)` by decide_tac >>
          metis_tac[]) >>
      `d+ho <= i /\ i < d+ho+hn` by decide_tac >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `i < d+hl+tl`
  >- (`d+hl <= i /\ i < d+hl+tl /\
       ~(d+ho <= i /\ i < d+ho+hn) /\
       ~(d+hl+tl <= i /\ i < d+hl+tl+tn)` by decide_tac >>
      metis_tac[]) >>
  `d+hl+tl <= i /\ i < d+hl+tl+tn` by decide_tac >> metis_tac[]
QED

Theorem log_members_layout_empty_head:
  log_members_layout [] [] [] pre pvs sb so ho d hl outcap mem ==>
  ho = hl
Proof
  simp[log_members_layout_def, head_lengths_acc]
QED

Theorem log_members_layout_complete_clean:
  log_members_layout [] [] [] pre pvs sb so ho d hl outcap mem /\
  (!i. d <= i /\ i < d+ho ==> i NOTIN m) /\
  (!i. d+hl <= i /\ i < d+hl+LENGTH (FLAT (abi_tuple_tails pre pvs)) ==>
       i NOTIN m) ==>
  !i. d <= i /\ i < d+LENGTH (enc (Tuple pre) (ListV pvs)) ==>
      i NOTIN m
Proof
  strip_tac >> drule log_members_layout_final_length >> strip_tac >>
  drule log_members_layout_empty_head >> strip_tac >>
  rpt strip_tac >> Cases_on `i < d+hl`
  >- metis_tac[] >>
  `d+hl <= i /\ i < d+hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`
    by decide_tac >> metis_tac[]
QED

Theorem log_members_layout_advance_clean:
  log_members_layout ((ei,asz,mz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs sb so ho d hl outcap mem /\
  tl = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  tn = (if dyn then LENGTH (enc ty av) else 0) /\
  (!i. d <= i /\ i < d+ho ==> i NOTIN m) /\
  (!i. d+hl <= i /\ i < d+hl+tl ==> i NOTIN m) /\
  (!i. d+ho <= i /\ i < d+ho+asz ==> i NOTIN m') /\
  (!i. d+hl+tl <= i /\ i < d+hl+tl+tn ==> i NOTIN m') /\
  (!i. ~(d+ho <= i /\ i < d+ho+asz) /\
       ~(d+hl+tl <= i /\ i < d+hl+tl+tn) ==>
       (i IN m' <=> i IN m)) ==>
  (!i. d <= i /\ i < d+SUM (MAP abi_member_head_size (pre++[ty])) ==>
       i NOTIN m') /\
  (!i. d+hl <= i /\
       i < d+hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av]))) ==>
       i NOTIN m')
Proof
  strip_tac >>
  drule log_members_layout_bounds >> strip_tac >>
  drule_all clean_head_tail_advance >> strip_tac >>
  drule log_members_layout_cons_input >> strip_tac >>
  drule log_members_layout_offsets >>
  disch_then (qspecl_then [`ty`, `av`] strip_assume_tac) >>
  asm_simp_tac bool_ss []
QED
