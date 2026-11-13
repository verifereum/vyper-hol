(* Raw ABI tuple stores: robust encoder windows tolerate copied padding. *)
Theory abiEncTuplePtrStore
Ancestors
  abiTupleEncodePrepare robustCopyTransportPtr abiEncoderInputFrame bodyPtrDefs
  abiEncTuplePtrMaterializeStore assignBasePtrMcopyTransport valueEncodingProps

Theorem abi_tuple_store_robust_copy:
  mem_bytes_at dst cap mem' = mem_bytes_at src cap mem /\
  (!i. i < cap ==> (dst+i IN tn' <=> src+i IN tn)) /\
  (!m. mem_agree_outside tn mem m ==>
    abi_encoder_input ei at av src cap m) ==>
  !m. mem_agree_outside tn' mem' m ==>
    abi_encoder_input ei at av dst cap m
Proof
  rpt strip_tac >> drule_all copied_window_agree_witness >>
  disch_then (qx_choose_then `mix` strip_assume_tac) >>
  `abi_encoder_input ei at av src cap mix` by metis_tac[] >>
  drule abi_encoder_input_relocate >>
  disch_then (qspecl_then [`dst`, `m`] mp_tac) >> simp[]
QED

Theorem abi_tuple_store_mcopy_input:
  eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
  eval_operand count_op s = SOME n /\ cap <= w2n n /\
  u = mcopy (w2n b) (w2n a) (w2n n) s /\
  tf = step_taint (mk_inst id MCOPY [dst;src;count_op] []) s u tn /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    abi_encoder_input ei at av (w2n a) cap m) ==>
  !m. mem_agree_outside tf.t_mem u.vs_memory m ==>
    abi_encoder_input ei at av (w2n b) cap m
Proof
  strip_tac >>
  `!i. i < w2n n ==>
    (w2n b+i IN tf.t_mem <=> w2n a+i IN tn.t_mem)` by
    (drule_all assign_base_mcopy_taint_window >> simp[]) >>
  rpt strip_tac >> irule abi_tuple_store_robust_copy >>
  qexistsl [`s.vs_memory`, `u.vs_memory`, `w2n a`, `tn.t_mem`, `tf.t_mem`] >> simp[] >>
  irule EQ_SYM >> irule (SRULE [] (Q.SPEC `0` (Q.GEN `i` (SPEC_ALL mem_bytes_at_translated_window)))) >>
  qexists `w2n n` >> simp[mcopy_mem_bytes_at_same]
QED
