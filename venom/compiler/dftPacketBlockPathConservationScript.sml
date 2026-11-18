Theory dftPacketBlockPathConservation
Ancestors
  dftPacketPseudoKeyFreshness dftPacketCallInsertionConservation
  list rich_list finite_map arithmetic pred_set

(* An absent block address is absent from every retained key aggregate.
   The synchronized insertion equations below are list equations only;
   neither freshness nor observation conservation is assumed. *)
Theorem dft_packet_block_path_conservation:
  !(acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls:(gas_event,
      num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (ks_tab:(((num # num) list # num),gas_event list list) fmap)
    AK (AM:(num # num) list -> bytes32 option list)
    (AE:(num # num) list -> (string # num) list)
    p d fresh_xs sf rsf rtf rinc rentry rorder rres rrest
    cm ce ck lm rm le re lk rk mnew enew knew.
    AK = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    (!a sf tf inc entry order res rest f.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,rest) /\ MEM f order ==>
      (a,f) IN FDOM blocks) /\
    (!a f bb bt ps xs ys rho hin h0 body count front closed brest.
      FLOOKUP blocks (a,f) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) ==>
      (case body of
        NONE => FLOOKUP ks_tab (a,f) = SOME []
      | SOME be => ?ks.
          FLOOKUP ks_tab (a,f) = SOME ks /\ LENGTH ks = LENGTH xs /\
          (!q. q < LENGTH xs ==>
            ((EL q xs).inst_opcode = GAS ==>
              EL q ks = [(a,f,(EL q xs).inst_id)]) /\
            ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
              EL q ks = []) /\
            ((EL q xs).inst_opcode = INVOKE ==>
              (case FLOOKUP calls (a,f,(EL q xs).inst_id) of
                NONE => EL q ks = []
              | SOME call => ?csf ctf cinc centry corder cres crest.
                  FLOOKUP acts ((f,(EL q xs).inst_id)::a) =
                    SOME (csf,ctf,cinc,centry,corder,cres,crest) /\
                  EL q ks = FLAT (MAP (\g. FLAT
                    (THE (FLOOKUP ks_tab (((f,(EL q xs).inst_id)::a),g)))) corder)))))) /\
    FLOOKUP acts [] = SOME (rsf,rtf,rinc,rentry,rorder,rres,rrest) /\
    (p,SUC d) NOTIN FDOM blocks /\
    ALL_DISTINCT (MAP (\i. i.inst_id) fresh_xs) /\ ALL_DISTINCT (AK []) /\
    ((cm = [] /\ ce = [] /\ ck = []) \/
     (cm = GENLIST (\q. if (EL q fresh_xs).inst_opcode = GAS
        then [NONE] else []) (LENGTH fresh_xs) /\
      ce = GENLIST (\q. if (EL q fresh_xs).inst_opcode = GAS
        then [(sf.fn_name,(EL q fresh_xs).inst_id)] else []) (LENGTH fresh_xs) /\
      ck = GENLIST (\q. if (EL q fresh_xs).inst_opcode = GAS
        then [(p,SUC d,(EL q fresh_xs).inst_id)] else []) (LENGTH fresh_xs))) /\
    AM [] = lm ++ rm /\ AE [] = le ++ re /\ AK [] = lk ++ rk /\
    mnew = lm ++ FLAT cm ++ rm /\ enew = le ++ FLAT ce ++ re /\
    knew = lk ++ FLAT ck ++ rk /\
    LENGTH lm = LENGTH le /\ LENGTH lm = LENGTH lk /\
    LENGTH rm = LENGTH re /\ LENGTH rm = LENGTH rk ==>
    LENGTH (FLAT cm) = LENGTH (FLAT ce) /\
    LENGTH (FLAT cm) = LENGTH (FLAT ck) /\
    EVERY (\x. x = NONE) (FLAT cm) /\
    ALL_DISTINCT (FLAT ck) /\
    (!key. MEM key (FLAT ck) ==> ~MEM key (AK [])) /\
    LENGTH mnew = LENGTH enew /\ LENGTH mnew = LENGTH knew /\
    MAP THE (FILTER IS_SOME mnew) = MAP THE (FILTER IS_SOME (AM [])) /\
    MAP (\(key,slot). (key,THE slot))
      (FILTER (\(key,slot). IS_SOME slot) (ZIP (knew,mnew))) =
    MAP (\(key,slot). (key,THE slot))
      (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK [],AM []))) /\
    ALL_DISTINCT knew
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!cid. ~MEM (p,SUC d,cid) (AK [])` by
    (gen_tac >> strip_tac >>
     drule_all dft_packet_retained_key_origin_clauses >> strip_tac >>
     metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME]) >>
  `LENGTH (FLAT cm) = LENGTH (FLAT ce) /\
   LENGTH (FLAT cm) = LENGTH (FLAT ck) /\
   EVERY (\x. x = NONE) (FLAT cm) /\
   ALL_DISTINCT (FLAT ck) /\
   (!key. MEM key (FLAT ck) ==> ~MEM key (AK []))` by
    suspend "fresh" >>
  simp[] >> conj_tac >- suspend "observed" >>
  conj_tac >- suspend "keyed" >> suspend "root_distinct"
QED

Resume dft_packet_block_path_conservation[fresh]:
  qpat_x_assum `(_ /\ _ /\ _) \/ _` strip_assume_tac
  >- simp[] >>
  `cm = MAP (\i. if i.inst_opcode = GAS then [NONE] else []) fresh_xs` by
    simp[LIST_EQ_REWRITE,EL_MAP,EL_GENLIST] >>
  `ce = MAP (\i. if i.inst_opcode = GAS then [(sf.fn_name,i.inst_id)] else []) fresh_xs` by
    simp[LIST_EQ_REWRITE,EL_MAP,EL_GENLIST] >>
  `ck = MAP (\i. if i.inst_opcode = GAS then [(p,SUC d,i.inst_id)] else []) fresh_xs` by
    simp[LIST_EQ_REWRITE,EL_MAP,EL_GENLIST] >>
  conj_tac >- suspend "lengths_sites" >>
  conj_tac >- suspend "lengths_keys" >>
  conj_tac >- (asm_rewrite_tac[] >> POP_ASSUM_LIST (K ALL_TAC) >>
    Induct_on `fresh_xs` >> simp[] >>
    Cases_on `h.inst_opcode = GAS` >> simp[]) >>
  conj_tac >- suspend "distinct" >>
  simp[MEM_FLAT,MEM_MAP] >> rpt strip_tac >>
  Cases_on `i.inst_opcode = GAS` >> gvs[]
QED

Resume dft_packet_block_path_conservation[lengths_sites]:
  asm_rewrite_tac[] >> POP_ASSUM_LIST (K ALL_TAC) >>
  Induct_on `fresh_xs` >> simp[] >>
  Cases_on `h.inst_opcode = GAS` >> simp[]
QED

Resume dft_packet_block_path_conservation[lengths_keys]:
  asm_rewrite_tac[] >> POP_ASSUM_LIST (K ALL_TAC) >>
  Induct_on `fresh_xs` >> simp[] >>
  Cases_on `h.inst_opcode = GAS` >> simp[]
QED

Resume dft_packet_block_path_conservation[distinct]:
  asm_rewrite_tac[] >>
  qpat_x_assum `ALL_DISTINCT (MAP (\i. i.inst_id) fresh_xs)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  Induct_on `fresh_xs` >> simp[MEM_FLAT,MEM_MAP] >>
  rpt strip_tac >> Cases_on `h.inst_opcode = GAS` >> gvs[] >>
  strip_tac >> gvs[MEM_FLAT,MEM_MAP,AllCaseEqs()] >> metis_tac[]
QED

Resume dft_packet_block_path_conservation[observed]:
  `FILTER IS_SOME (FLAT cm) = []` by
    (simp[FILTER_EQ_NIL,EVERY_MEM] >>
     gvs[EVERY_MEM] >> metis_tac[optionTheory.IS_SOME_DEF]) >>
  simp[FILTER_APPEND,MAP_APPEND]
QED

Resume dft_packet_block_path_conservation[keyed]:
  irule (cj 4 dft_packet_call_insertion_conservation) >> simp[] >>
  conj_tac >- (qexists_tac `REPLICATE (LENGTH (FLAT ck)) ARB` >> simp[]) >>
  conj_tac >- (qexists_tac `REPLICATE (LENGTH lk) ARB` >> simp[]) >>
  qexists_tac `REPLICATE (LENGTH rk) ARB` >> simp[]
QED

Resume dft_packet_block_path_conservation[root_distinct]:
  qpat_x_assum `AK = _` kall_tac >>
  gvs[ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Finalise dft_packet_block_path_conservation
