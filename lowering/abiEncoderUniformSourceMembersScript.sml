(* Finite choice retains a single family of representatives across memories. *)
Theory abiEncoderUniformSourceMembers
Ancestors
  abiEncoderSourceAggregate abiEncoderOpenInput vyperABI vyperValue
  vyperTyping valueEncoding contractABI list rich_list arithmetic

Theorem abi_encoder_uniform_source_members:
 source_reps env ts infos cts /\ LENGTH tvs = LENGTH ts /\
 LENGTH vs = LENGTH ts /\ LENGTH avs = LENGTH ts /\
 (!i. i < LENGTH ts ==>
   evaluate_type env (EL i ts) = SOME (EL i tvs) /\
   value_has_type (EL i tvs) (EL i vs) /\
   vyper_to_abi env (EL i ts) (EL i vs) = SOME (EL i avs) /\
   val_in_memory (EL i tvs) (EL i vs)
     (sb + SUM (MAP type_memory_size (TAKE i tvs))) mem0) /\
 (!i. i < LENGTH ts ==>
   ?rv. enc (EL i cts) rv = enc (vyper_to_abi_type env (EL i ts)) (EL i avs) /\
     !mem. val_in_memory (EL i tvs) (EL i vs)
       (sb + SUM (MAP type_memory_size (TAKE i tvs))) mem ==>
       abi_encoder_open_input (FST (EL i infos)) (EL i cts) rv
         (sb + SUM (MAP type_memory_size (TAKE i tvs)))
         (type_memory_size (EL i tvs)) mem) ==>
 ?rvs. LENGTH rvs = LENGTH ts /\
   (!i. i < LENGTH ts ==>
     enc (EL i cts) (EL i rvs) =
       enc (vyper_to_abi_type env (EL i ts)) (EL i avs)) /\
   !mem. (!i. i < LENGTH ts ==>
     val_in_memory (EL i tvs) (EL i vs)
       (sb + SUM (MAP type_memory_size (TAKE i tvs))) mem) ==>
     !i ei abi_sz mem_sz dyn.
       i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
       abi_sz = abi_member_head_size (EL i cts) /\
       dyn = is_dynamic (EL i cts) /\
       abi_encoder_open_input ei (EL i cts) (EL i rvs)
         (sb + abi_encoder_member_span (TAKE i infos)) mem_sz mem
Proof
  strip_tac >>
  `!i. i < LENGTH ts ==> evaluate_type env (EL i ts) = SOME (EL i tvs)` by simp[] >>
  drule_all source_reps_span >> disch_tac >>
  drule source_reps_lengths >> strip_tac >>
  qpat_x_assum `!i. _ ==> ?rv. _` mp_tac >>
  CONV_TAC (LAND_CONV (BINDER_CONV (HO_REWR_CONV (GSYM RIGHT_EXISTS_IMP_THM)))) >>
  CONV_TAC (LAND_CONV (HO_REWR_CONV SKOLEM_THM)) >>
  disch_then (qx_choose_then `f` assume_tac) >>
  qexists_tac `GENLIST f (LENGTH ts)` >> simp[] >>
  rpt strip_tac >>
  drule_all source_reps_index >> strip_tac >>
  qpat_assum `!i. i < LENGTH ts ==> evaluate_type _ _ = _ /\ _`
    (qspec_then `i` mp_tac) >>
  gvs[] >>
  qpat_x_assum `!i. i < LENGTH ts ==> enc _ (f i) = _ /\ _`
    (qspec_then `i` mp_tac) >> simp[]
QED
