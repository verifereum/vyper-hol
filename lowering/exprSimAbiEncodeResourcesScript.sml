(* Resource boundaries for a registered ABI encoder observer. *)
Theory exprSimAbiEncodeResources
Ancestors
  exprLoweringProps venomExecSemantics venomInst venomState
  finite_map list rich_list words

Theorem abi_encode_weighted_subset:
  !xs ys (w:'a -> num).
    ALL_DISTINCT xs /\ (!x. MEM x xs ==> MEM x ys) ==>
    SUM (MAP w xs) <= SUM (MAP w ys)
Proof
  Induct_on `xs`
  >- simp[]
  >> rpt gen_tac >> simp[ALL_DISTINCT] >> strip_tac
  >> `MEM h ys` by metis_tac[]
  >> qpat_x_assum `MEM h ys` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT])
  >> gvs[]
  >> first_x_assum (qspecl_then [`l1 ++ l2`, `w`] mp_tac)
  >> impl_tac >- (simp[] >> metis_tac[])
  >> simp[MAP_APPEND, SUM_APPEND]
QED

Theorem abi_encode_pending_credit:
  ALL_DISTINCT (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts obs)) /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) ==>
  pending_alloca_size obs s <= pending_alloca_size func s
Proof
  strip_tac
  >> `ALL_DISTINCT
        (FILTER (\i. i.inst_id NOTIN FDOM s.vs_allocas)
          (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts obs)))` by
       (irule FILTER_ALL_DISTINCT >> simp[])
  >> fs[FILTER_FILTER, CONJ_COMM]
  >> rewrite_tac[pending_alloca_size_def]
  >> irule abi_encode_weighted_subset
  >> simp[MEM_FILTER] >> metis_tac[]
QED

Theorem abi_encode_observer_credit:
  ALL_DISTINCT (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts obs)) /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) /\
  alloca_room ctx func s ==>
  s.vs_alloca_next + pending_alloca_size obs s < dimword (:256)
Proof
  strip_tac
  >> `pending_alloca_size obs s <= pending_alloca_size func s` by
       (irule abi_encode_pending_credit >> simp[])
  >> gvs[alloca_room_def]
QED

Theorem abi_encode_room_charge:
  alloca_room ctx func s /\
  t.vs_alloca_next + pending_alloca_size func t <=
    s.vs_alloca_next + pending_alloca_size func s ==>
  alloca_room ctx func t
Proof
  simp[alloca_room_def] >> rpt strip_tac >> simp[]
QED

Theorem abi_encode_room_exec_alloca:
  alloca_room ctx func s /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit n] /\
  exec_alloca inst s n = OK t ==> alloca_room ctx func t
Proof
  strip_tac >> irule abi_encode_room_charge >> qexists_tac `s`
  >> simp[] >> irule exec_alloca_static_charge >> metis_tac[]
QED

Theorem abi_encode_room_fields:
  alloca_room ctx func s /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next ==> alloca_room ctx func t
Proof
  strip_tac >> irule abi_encode_room_charge >> qexists_tac `s`
  >> simp[pending_alloca_size_def]
QED

Theorem abi_encode_fmp_room_fields:
  fmp_room ctx func s /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp ==>
  fmp_room ctx func t
Proof
  strip_tac >> irule fmp_room_static_charge >> qexists_tac `s`
  >> simp[pending_alloca_size_def]
QED
