Theory dftPacketPreterminalRows
Ancestors
  dftPacketRetainedOracle finite_map venomExecSemantics list rich_list

Theorem dft_packet_preterminal_filling_extension:
  LENGTH ms = LENGTH ordered + 1 /\ EL (LENGTH ordered) ms = [] /\
  LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
    (TAKE (LENGTH ordered) ms) kgss ==>
  LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
    ms (kgss ++ [[]]) /\ FLAT (kgss ++ [[]]) = FLAT kgss
Proof
  strip_tac >>
  `ms = TAKE (LENGTH ordered) ms ++ [[]]` by
    (qpat_x_assum `EL _ ms = []` (fn th => rewrite_tac[GSYM th]) >>
     qspecl_then [`ms`,`LENGTH ordered`] mp_tac TAKE_EL_SNOC >>
     simp[SNOC_APPEND] >> metis_tac[TAKE_LENGTH_ID]) >>
  conj_tac
  >- (qpat_x_assum `ms = _` (fn th => once_rewrite_tac[th]) >>
      irule LIST_REL_APPEND_suff >> simp[]) >> simp[]
QED

Theorem dft_packet_preterminal_empty_terminal:
  xs = ordered ++ [term] /\ term.inst_opcode <> GAS /\
  term.inst_opcode <> INVOKE /\
  (!q. q < LENGTH xs /\ (EL q xs).inst_opcode <> GAS /\
    (EL q xs).inst_opcode <> INVOKE ==>
    EL q ms = [] /\ EL q ess = [] /\ EL q ks = []) ==>
  EL (LENGTH ordered) ms = [] /\ EL (LENGTH ordered) ess = [] /\
  EL (LENGTH ordered) ks = []
Proof
  strip_tac >> first_x_assum (qspec_then `LENGTH ordered` mp_tac) >>
  simp[EL_LENGTH_APPEND_0]
QED

Theorem dft_packet_preterminal_rows_some:
  !(acts : ((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (calls : (gas_event, num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap).
  xs = ordered ++ [term] /\ LENGTH ms = LENGTH xs /\
  ALL_DISTINCT (MAP FST obs) /\
  (!q. q < LENGTH xs ==>
    ((EL q xs).inst_opcode = GAS ==>
      EL q ms = [ALOOKUP obs (a,e,(EL q xs).inst_id)]) /\
    ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
      EL q ms = []) /\
    ((EL q xs).inst_opcode = INVOKE ==>
      (case FLOOKUP calls (a,e,(EL q xs).inst_id) of
        NONE => EL q ms = []
      | SOME call => EL q ms = AM ((e,(EL q xs).inst_id)::a)))) /\
  (!q. q < LENGTH ordered /\ (EL q xs).inst_opcode = GAS ==>
    ?w. MEM ((a,e,(EL q xs).inst_id),w) obs) /\
  (!q. q < LENGTH ordered /\ (EL q xs).inst_opcode = INVOKE ==>
    ?h b0 done_at_call child_entry ir child_out caller_post.
      FLOOKUP calls (a,e,(EL q xs).inst_id) =
        SOME (q,h,b0,done_at_call,child_entry,SOME (ir,child_out,caller_post))) /\
  (!a e cid q h b0 done_at_call child_entry ir child_out caller_post.
    FLOOKUP calls (a,e,cid) =
      SOME (q,h,b0,done_at_call,child_entry,SOME (ir,child_out,caller_post)) ==>
    ?csf ctf child_order child_res child_rest.
      FLOOKUP acts ((e,cid)::a) =
        SOME (csf,ctf,e,child_entry,child_order,child_res,child_rest) /\
      child_res = SOME (IntRet ir child_out)) /\
  (!a sf tf inc entry order r8 u0.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==>
    !v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==> EVERY IS_SOME (AM a)) /\
  (!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    (res = NONE <=> nrest = NONE)) ==>
  EVERY IS_SOME (FLAT (TAKE (LENGTH ordered) ms))
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[EVERY_FLAT] >> once_rewrite_tac[EVERY_EL] >>
  simp[EL_TAKE] >> rpt strip_tac >>
  `n < LENGTH ordered /\ n < LENGTH xs` by gvs[] >>
  qpat_x_assum `!q. q < LENGTH xs ==> _` (qspec_then `n` mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `(EL n xs).inst_opcode = GAS`
  >- (`?w. MEM ((a,e,(EL n xs).inst_id),w) obs` by metis_tac[] >>
      `ALOOKUP obs (a,e,(EL n xs).inst_id) = SOME w` by
        metis_tac[alistTheory.ALOOKUP_ALL_DISTINCT_MEM] >> gvs[]) >>
  Cases_on `(EL n xs).inst_opcode = INVOKE` >- (
    `?h b0 done_at_call child_entry ir child_out caller_post.
      FLOOKUP calls (a,e,(EL n xs).inst_id) =
        SOME (n,h,b0,done_at_call,child_entry,SOME (ir,child_out,caller_post))`
      by metis_tac[] >>
    gvs[] >>
    qpat_x_assum `!a e cid q h b0 done_at_call child_entry ir child_out caller_post. _`
      (drule_then strip_assume_tac) >> gvs[] >>
    `?rest. child_rest = SOME rest` by
      (Cases_on `child_rest` >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
    gvs[] >> metis_tac[]) >>
  gvs[]
QED
