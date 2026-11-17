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

Theorem preterminal_flat_aligned[local]:
  !xs ys. LIST_REL (\x y. LENGTH x = LENGTH y) xs ys ==>
    LENGTH (FLAT xs) = LENGTH (FLAT ys)
Proof
  Induct >> Cases_on `ys` >> simp[] >> gvs[LENGTH_FLAT]
QED

Theorem preterminal_flat_length[local]:
  !ord. (!e. MEM e ord ==> LENGTH (keys e) = LENGTH (masks e)) ==>
    LENGTH (FLAT (MAP keys ord)) = LENGTH (FLAT (MAP masks ord))
Proof
  Induct >> simp[]
QED

Theorem preterminal_flat_pair[local]:
  !ord. (!e. MEM e ord ==> LENGTH (keys e) = LENGTH (masks e)) /\
    MEM e ord /\ MEM kv (ZIP (keys e,masks e)) ==>
    MEM kv (ZIP (FLAT (MAP keys ord),FLAT (MAP masks ord)))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `LENGTH (keys h) = LENGTH (masks h)` by metis_tac[] >>
  `LENGTH (FLAT (MAP keys ord)) = LENGTH (FLAT (MAP masks ord))` by
    (irule preterminal_flat_length >> metis_tac[]) >>
  simp[GSYM ZIP_APPEND] >> metis_tac[]
QED

Theorem preterminal_row_pair[local]:
  !rows keyrows q.
    LIST_REL (\m k. LENGTH m = LENGTH k) rows keyrows /\
    q < LENGTH rows /\ MEM kv (ZIP (EL q keyrows,EL q rows)) ==>
    MEM kv (ZIP (FLAT keyrows,FLAT rows))
Proof
  Induct >> Cases_on `keyrows` >> simp[] >> rpt gen_tac >> strip_tac >>
  drule preterminal_flat_aligned >> disch_tac >>
  simp[GSYM ZIP_APPEND] >> Cases_on `q` >> gvs[] >> metis_tac[]
QED

Theorem preterminal_activation_root[local]:
  (!e cid a sf tf inc entry order res nrest kv.
    FLOOKUP acts ((e,cid)::a) = SOME (sf,tf,inc,entry,order,res,nrest) /\
    MEM kv (ZIP (AK ((e,cid)::a),AM ((e,cid)::a))) ==>
    (?sf tf inc entry order res nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)) /\
    MEM kv (ZIP (AK a,AM a))) ==>
  !a sf tf inc entry order res nrest kv.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    MEM kv (ZIP (AK a,AM a)) ==> MEM kv (ZIP (AK [],AM []))
Proof
  strip_tac >> Induct >- simp[] >> rpt strip_tac >> PairCases_on `h` >>
  qpat_x_assum `!e cid a sf tf inc entry order res nrest kv. _`
    (drule_then strip_assume_tac) >> metis_tac[]
QED

Theorem preterminal_unflat_lookup[local]:
  !R rows keys.
    LIST_REL (\r k. LENGTH r = LENGTH k) rows keys /\
    LIST_REL R (FLAT keys) (FLAT rows) ==>
    LIST_REL (LIST_REL R) keys rows
Proof
  gen_tac >> Induct >> Cases_on `keys` >> simp[] >>
  rpt strip_tac >> gvs[LIST_REL_APPEND_EQ]
QED

Theorem preterminal_flat_prefix_lookup[local]:
  !R ks ms. LIST_REL (LIST_REL R) ks ms ==>
    !q. LIST_REL R (FLAT (TAKE q ks)) (FLAT (TAKE q ms))
Proof
  gen_tac >> Induct >> Cases_on `ms` >> simp[] >>
  rpt gen_tac >> strip_tac >> gen_tac >> Cases_on `q` >> simp[] >>
  irule LIST_REL_APPEND_suff >> simp[]
QED

Theorem dft_packet_preterminal_row_lookup:
  !(acts : ((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks : (((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls : (gas_event, num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap).
  AM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AK = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  FDOM blocks = FDOM ms_tab /\ FDOM blocks = FDOM ks_tab /\
  (!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    (!e. MEM e order <=> (a,e) IN FDOM blocks) /\
    (!e cid parent. a = (e,cid)::parent ==>
      ?q h b0 done_at_call ret.
        FLOOKUP calls (parent,e,cid) = SOME (q,h,b0,done_at_call,entry,ret))) /\
  (!a e bb bt ps xs ys rho in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) ==>
    (?sf tf inc entry order res nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\ MEM e order) /\
    (body_entry = NONE ==>
      FLOOKUP ms_tab (a,e) = SOME [] /\ FLOOKUP ks_tab (a,e) = SOME [])) /\
  (!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ks.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks ==>
    LENGTH ms = LENGTH xs /\
    LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\
    (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
      (case FLOOKUP calls (a,e,(EL q xs).inst_id) of
        NONE => EL q ms = [] /\ EL q ks = []
      | SOME call =>
          EL q ms = AM ((e,(EL q xs).inst_id)::a) /\
          EL q ks = AK ((e,(EL q xs).inst_id)::a)))) /\
  (!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) ==>
    ?bb bt ps xs ys rho in_state h0 be hbe count front closed brest c.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) /\
      q < LENGTH xs /\ c = EL q xs /\ c.inst_id = cid /\ c.inst_opcode = INVOKE) /\
  ALL_DISTINCT (MAP FST obs) /\ ALL_DISTINCT (AK []) /\
  LENGTH (AM []) = LENGTH (AK []) /\
  PERM (MAP (\(key,slot). (key,THE slot))
    (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK [],AM [])))) obs /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks ==>
  !q. LIST_REL (\key slot. slot = ALOOKUP obs key)
    (FLAT (TAKE q ks)) (FLAT (TAKE q ms))
Proof
  rpt gen_tac >> strip_tac >>
  `!a e. (a,e) IN FDOM blocks ==>
    LIST_REL (\m keys. LENGTH m = LENGTH keys)
      (THE (FLOOKUP ms_tab (a,e))) (THE (FLOOKUP ks_tab (a,e)))`
    by suspend "row_alignment" >>
  `!a e rows keyrows kv.
    FLOOKUP ms_tab (a,e) = SOME rows /\
    FLOOKUP ks_tab (a,e) = SOME keyrows /\
    MEM kv (ZIP (FLAT keyrows,FLAT rows)) ==>
    MEM kv (ZIP (AK a,AM a))`
    by suspend "block_embedding" >>
  `!ec cid parent sf tf inc entry order res nrest kv.
    FLOOKUP acts ((ec,cid)::parent) = SOME (sf,tf,inc,entry,order,res,nrest) /\
    MEM kv (ZIP (AK ((ec,cid)::parent),AM ((ec,cid)::parent))) ==>
    (?sf tf inc entry order res nrest.
      FLOOKUP acts parent = SOME (sf,tf,inc,entry,order,res,nrest)) /\
    MEM kv (ZIP (AK parent,AM parent))`
    by suspend "parent_embedding" >>
  drule preterminal_activation_root >> disch_tac >>
  `LIST_REL (\key slot. slot = ALOOKUP obs key) (AK []) (AM [])` by
    (irule dft_packet_retained_key_lookup >> simp[]) >>
  qpat_x_assum `AM = _` kall_tac >> qpat_x_assum `AK = _` kall_tac >>
  `(a,e) IN FDOM blocks` by metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  `LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks` by
    metis_tac[optionTheory.THE_DEF] >>
  `?sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)` by
    (Cases_on `FLOOKUP blocks (a,e)` >- gvs[FLOOKUP_DEF] >>
     PairCases_on `x` >>
     qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 body_entry count front closed brest.
       FLOOKUP blocks (a,e) = _ ==> _` (drule_then strip_assume_tac) >>
     metis_tac[]) >>
  `LIST_REL (\key slot. slot = ALOOKUP obs key) (FLAT ks) (FLAT ms)`
    by suspend "selected_lookup" >>
  drule_all preterminal_unflat_lookup >>
  metis_tac[preterminal_flat_prefix_lookup]
QED

Resume dft_packet_preterminal_row_lookup[row_alignment]:
  rpt strip_tac >>
  Cases_on `FLOOKUP blocks (a',e')` >- gvs[FLOOKUP_DEF] >>
  PairCases_on `x` >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _`
    (drule_then strip_assume_tac) >>
  Cases_on `x8` >- gvs[] >> PairCases_on `x` >>
  Cases_on `FLOOKUP ms_tab (a',e')` >- gvs[FLOOKUP_DEF] >>
  Cases_on `FLOOKUP ks_tab (a',e')` >- gvs[FLOOKUP_DEF] >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ks. _`
    drule >> simp[]
QED

Resume dft_packet_preterminal_row_lookup[block_embedding]:
  rpt strip_tac >>
  Cases_on `FLOOKUP blocks (a',e')` >- gvs[FLOOKUP_DEF] >>
  PairCases_on `x` >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!a sf tf inc entry order res nrest. _`
    (drule_then strip_assume_tac) >>
  simp[] >> irule preterminal_flat_pair >>
  reverse conj_tac >- (qexists_tac `e'` >> simp[]) >>
  rpt strip_tac >> simp[] >> irule EQ_SYM >>
  irule preterminal_flat_aligned >> metis_tac[]
QED

Resume dft_packet_preterminal_row_lookup[parent_embedding]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `AM = _` kall_tac >> qpat_x_assum `AK = _` kall_tac >>
  qpat_x_assum `!a sf tf inc entry order res nrest. _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!e cid parent. _`
    (qspecl_then [`ec`,`cid`,`parent`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret. _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _`
    (drule_then strip_assume_tac) >>
  conj_tac >- metis_tac[] >>
  Cases_on `FLOOKUP ms_tab (parent,ec)` >- gvs[FLOOKUP_DEF] >>
  Cases_on `FLOOKUP ks_tab (parent,ec)` >- gvs[FLOOKUP_DEF] >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ks. _`
    drule >> simp[] >> strip_tac >>
  qpat_x_assum `!q. q < LENGTH xs /\ _ ==> _` (qspec_then `q` mp_tac) >>
  gvs[] >> strip_tac >>
  qpat_x_assum `!a e rows keyrows kv. _` irule >>
  goal_assum (drule_at Any) >> simp[] >>
  irule preterminal_row_pair >> goal_assum (drule_at Any) >>
  qexists_tac `q` >> simp[]
QED

Resume dft_packet_preterminal_row_lookup[selected_lookup]:
  `LENGTH (FLAT ks) = LENGTH (FLAT ms)` by metis_tac[preterminal_flat_aligned] >>
  simp[LIST_REL_EVERY_ZIP, EVERY_MEM, pairTheory.FORALL_PROD] >>
  qx_gen_tac `key` >> qx_gen_tac `slot` >> strip_tac >>
  `MEM (key,slot) (ZIP (AK a,AM a))` by metis_tac[] >>
  `MEM (key,slot) (ZIP (AK [],AM []))` by metis_tac[] >>
  qpat_x_assum `LIST_REL _ (AK []) (AM [])`
    (mp_tac o REWRITE_RULE [LIST_REL_EVERY_ZIP, EVERY_MEM]) >>
  disch_then (qspec_then `(key,slot)` mp_tac o CONJUNCT2) >> simp[]
QED

Finalise dft_packet_preterminal_row_lookup
