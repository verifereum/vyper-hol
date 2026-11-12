(* Checked interfaces for relabeled ABI-encoder execution. *)
Theory exprSimAbiEncodeBoundaryProbe
Ancestors
  exprSimAbiEncodeRegistration abiTupleProps abiDecoderAllocation arithmetic

Theorem abi_encode_relabel_registered_room:
  obs.fn_name = func.fn_name /\ alloca_room ctx func s /\
  ALL_DISTINCT (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts obs)) /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\
       i.inst_opcode <> NOP ==> MEM i (fn_insts func)) ==>
  alloca_room (ctx with ctx_functions := [obs]) obs s
Proof
  strip_tac >> irule abi_encode_registered_alloca_room >>
  simp[] >> qexists_tac `func` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem abi_encode_tuple_staging_same_blocks:
  compile_store_abi_tuple cenv buf off xs st = ((),st') /\
  eval_operand buf ss = SOME (n2w baddr) /\ fresh_vars_wrt st ss /\
  baddr+off+abi_tuple_bytes cenv xs <= dimword (:256) /\
  abi_tuple_starts cenv (baddr+off) xs /\
  abi_tuple_inputs cenv xs tvs vs ss (baddr+off)
    (baddr+off+abi_tuple_bytes cenv xs) ==>
  same_blocks st st'
Proof
  strip_tac >> drule_all compile_store_abi_tuple_correct >>
  strip_tac >> simp[]
QED

(* This constructs a budget, but deliberately leaves its word bound and
   allocated-site size obligations visible to the resource producer. *)
Theorem abi_encode_canonical_scratch_budget:
  let cap = s.vs_alloca_next + 32 * CARD (abi_decoder_missing first last s) in
  cap < dimword (:256) /\
  (!id off sz. id IN abi_decoder_ids first last /\
     FLOOKUP s.vs_allocas id = SOME (off,sz) ==>
     sz = 32 /\ off + 32 <= s.vs_alloca_next) /\
  (!i j p q. i IN abi_decoder_ids first last /\
     j IN abi_decoder_ids first last /\ i <> j /\
     FLOOKUP s.vs_allocas i = SOME (p,32) /\
     FLOOKUP s.vs_allocas j = SOME (q,32) ==>
     p+32 <= q \/ q+32 <= p) ==>
  abi_decoder_budget first last 0 cap s
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  simp_tac bool_ss [abi_decoder_budget_def, ADD_CLAUSES, ZERO_LESS_EQ,
                    LESS_EQ_REFL] >> metis_tac[]
QED
