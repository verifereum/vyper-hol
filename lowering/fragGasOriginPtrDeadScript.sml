(* The joint gas-origin and pointer path is monotone in the dead bytes:
   the path's pointer check is, edge by edge (ptrSafetyTransport). *)
Theory fragGasOriginPtrDead
Ancestors
  fragGasOriginPtr ptrSafetyTransport fragGasPathPtr

Theorem gas_origin_ptr_path_dead_mono:
  !D lo explicit ctx func PG s G tn marks r G' tn'.
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
      (s, G, tn) marks (r, G', tn') ==>
    !D'. (!a st. D.d_stor a st SUBSET D'.d_stor a st) /\
         (!a st. D.d_trans a st SUBSET D'.d_trans a st) /\
         (!i. D.d_imm i SUBSET D'.d_imm i) /\
         (!r. D.d_ret r SUBSET D'.d_ret r) ==>
         gas_origin_ptr_path (D', lo, explicit, ctx, func, PG)
           (s, G, tn) marks (r, G', tn')
Proof
  qsuff_tac
    `!cx st marks out.
       gas_origin_ptr_path cx st marks out ==>
       !D lo explicit ctx func PG D'.
         cx = (D, lo, explicit, ctx, func, PG) /\
         (!a st. D.d_stor a st SUBSET D'.d_stor a st) /\
         (!a st. D.d_trans a st SUBSET D'.d_trans a st) /\
         (!i. D.d_imm i SUBSET D'.d_imm i) /\
         (!r. D.d_ret r SUBSET D'.d_ret r) ==>
         gas_origin_ptr_path (D', lo, explicit, ctx, func, PG) st marks out`
  >- metis_tac[] >>
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac >> rpt strip_tac >>
  gvs[gas_origin_ptr_edge_def]
  >- simp[gas_origin_ptr_path_rules]
  >- (irule (cj 2 gas_origin_ptr_path_rules) >>
      simp[gas_origin_ptr_edge_def] >>
      metis_tac[gas_path_ptr_edge_dead_mono])
  >> irule (cj 3 gas_origin_ptr_path_rules) >>
  simp[gas_origin_ptr_edge_def] >>
  metis_tac[gas_path_ptr_edge_dead_mono]
QED

Theorem gas_origin_ptr_path_from_no_dead:
  gas_origin_ptr_path
    (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
        d_ret := K {} |>, lo, explicit, ctx, func, PG)
    (s, G, tn) marks (r, G', tn') ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (s, G, tn) marks (r, G', tn')
Proof
  strip_tac >> drule gas_origin_ptr_path_dead_mono >> simp[]
QED
