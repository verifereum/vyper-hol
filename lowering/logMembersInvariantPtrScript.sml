(* Semantic input boundaries for the scalar ABI member traversal. *)
Theory logMembersInvariantPtr
Ancestors
  abiEncoderInputFrame robustCopyTransportPtr representationCleanPtr
  bodyPtrDefs valueEncoding valueEncodingProofs list arithmetic

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
