Theory o1MakeSsaPhiGeneration
Ancestors
  makeSsaCurrentDefs makeSsaDefs irSupply list alist pair

(* Finite local insertion log. Records include operations at absent labels;
   this function neither assumes nor asserts CFG reachability. *)
Definition frontier_generation_def:
  frontier_generation d s x pm li bbs rest hp [] =
    ((bbs,rest,hp,s),[]) /\
  frontier_generation d s x pm li bbs rest hp (f::fs) =
    if MEM f hp then frontier_generation d s x pm li bbs rest hp fs
    else if ~(case ALOOKUP li f of NONE => F | SOME vs => MEM x vs) then
      frontier_generation d s x pm li bbs rest (f::hp) fs
    else
      let preds = case ALOOKUP pm f of NONE => [] | SOME ps => ps in
      let (id,t) = fresh_inst_id s in
      let phi = build_phi_inst_supply id x preds in
      let next = MAP (\bb. if bb.bb_label = f then insert_phi_at_block phi bb else bb) bbs in
      let (result,records) = frontier_generation d t x pm li next (f::rest) (f::hp) fs in
        (result,(d,f,id)::records)
End

Theorem frontier_generation_erasure:
  !fs d s x pm li bbs rest hp.
    FST (frontier_generation d s x pm li bbs rest hp fs) =
      process_frontiers_supply s x pm li bbs rest hp fs
Proof
  Induct >> simp[frontier_generation_def,process_frontiers_supply_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >> IF_CASES_TAC >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> simp[] >> metis_tac[FST]
QED

Inductive phi_generation:
  (!s x df pm li bbs hp.
    phi_generation s x df pm li bbs [] hp bbs s []) /\
  (!s x df pm li bbs d rest hp next pending seen t local out u tail.
    frontier_generation d s x pm li bbs rest hp
      (case ALOOKUP df d of NONE => [] | SOME fs => fs) =
      ((next,pending,seen,t),local) /\
    phi_generation t x df pm li next
      (FILTER (frontier_work_needed df seen) pending) seen out u tail ==>
    phi_generation s x df pm li bbs (d::rest) hp out u (local ++ tail))
End

Theorem frontier_generation_result:
  frontier_generation d s x pm li bbs rest hp fs = (result,records) ==>
  process_frontiers_supply s x pm li bbs rest hp fs = result
Proof
  metis_tac[frontier_generation_erasure,FST]
QED

Theorem phi_generation_erasure:
  !s x df pm li bbs roots hp out t records.
    phi_generation s x df pm li bbs roots hp out t records ==>
    insert_phis_for_var_supply s x df pm li bbs roots hp = (out,t)
Proof
  Induct_on `phi_generation` >> rpt strip_tac >>
  simp[Once insert_phis_for_var_supply_def] >>
  drule frontier_generation_result >> simp[]
QED

Theorem phi_generation_exists:
  !s x df pm li bbs roots hp.
    ?out t records. phi_generation s x df pm li bbs roots hp out t records
Proof
  recInduct insert_phis_for_var_supply_ind >> conj_tac
  >- (rpt gen_tac >> metis_tac[phi_generation_rules]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `phi_generation s x df pm li bbs (d::rest) hp` >>
  Cases_on `frontier_generation d s x pm li bbs rest hp
    (case ALOOKUP df d of NONE => [] | SOME fs => fs)` >>
  PairCases_on `q` >>
  drule frontier_generation_result >> strip_tac >>
  gvs[] >> metis_tac[phi_generation_rules]
QED

Definition generation_children_def:
  generation_children records = MAP (\(d,f,id). f) records
End

Definition generation_steps_def:
  generation_steps x pm [] bbs = bbs /\
  generation_steps x pm ((d,f,id)::records) bbs =
    generation_steps x pm records
      (MAP (\bb. if bb.bb_label = f then
        insert_phi_at_block (build_phi_inst_supply id x
          (case ALOOKUP pm f of NONE => [] | SOME ps => ps)) bb else bb) bbs)
End

Theorem generation_steps_append:
  !pre post bbs. generation_steps x pm (pre ++ post) bbs =
    generation_steps x pm post (generation_steps x pm pre bbs)
Proof
  Induct >> simp[generation_steps_def] >> Cases_on `h` >> Cases_on `r` >>
  simp[generation_steps_def]
QED

Theorem frontier_generation_steps:
  !fs d s x pm li bbs rest hp out pending seen t records.
    frontier_generation d s x pm li bbs rest hp fs =
      ((out,pending,seen,t),records) ==>
    out = generation_steps x pm records bbs
Proof
  Induct >> simp[frontier_generation_def,generation_steps_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[]
  >- metis_tac[] >>
  IF_CASES_TAC >> simp[]
  >- metis_tac[] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  simp[generation_steps_def] >> metis_tac[]
QED

Theorem frontier_generation_sources:
  !fs d s x pm li bbs rest hp out pending seen t records.
    frontier_generation d s x pm li bbs rest hp fs =
      ((out,pending,seen,t),records) ==>
    EVERY (\(a,f,id). a = d /\ MEM f fs /\
      ?vs. ALOOKUP li f = SOME vs /\ MEM x vs) records /\
    (!l. MEM l pending ==> MEM l rest \/ MEM l (generation_children records))
Proof
  Induct >> simp[frontier_generation_def,generation_children_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[]
  >- (strip_tac >> first_x_assum drule >>
      simp[EVERY_MEM,FORALL_PROD,generation_children_def] >> metis_tac[]) >>
  IF_CASES_TAC >> simp[]
  >- (strip_tac >> first_x_assum drule >>
      simp[EVERY_MEM,FORALL_PROD,generation_children_def] >> metis_tac[]) >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  first_x_assum drule >>
  simp[EVERY_MEM,FORALL_PROD,generation_children_def] >>
  Cases_on `ALOOKUP li h` >> gvs[] >> metis_tac[]
QED

Definition generation_order_def:
  generation_order roots [] = T /\
  generation_order roots ((d,f,id)::records) =
    (MEM d roots /\ generation_order (f::roots) records)
End

Theorem generation_order_cong:
  !records roots more.
    (!l. MEM l roots <=> MEM l more) ==>
    (generation_order roots records <=> generation_order more records)
Proof
  Induct >> simp[generation_order_def] >> Cases_on `h` >> Cases_on `r` >>
  simp[generation_order_def] >> metis_tac[MEM]
QED

Theorem generation_order_append:
  !pre post roots. generation_order roots (pre ++ post) <=>
    generation_order roots pre /\
    generation_order (generation_children pre ++ roots) post
Proof
  Induct >> simp[generation_order_def,generation_children_def] >>
  Cases_on `h` >> Cases_on `r` >>
  simp[generation_order_def,generation_children_def] >>
  rpt gen_tac >>
  `generation_order (MAP (\(d,f,id). f) pre ++ q'::roots) post =
   generation_order (q'::(MAP (\(d,f,id). f) pre ++ roots)) post` by
    (irule generation_order_cong >> simp[MEM_APPEND] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem generation_order_parent:
  !records roots d.
    MEM d roots /\ EVERY (\(a,f,id). a = d) records ==>
    generation_order roots records
Proof
  Induct >> simp[generation_order_def] >> Cases_on `h` >> Cases_on `r` >>
  simp[generation_order_def] >> metis_tac[MEM]
QED

Theorem phi_generation_steps:
  !s x df pm li bbs roots hp out t records.
    phi_generation s x df pm li bbs roots hp out t records ==>
    out = generation_steps x pm records bbs
Proof
  Induct_on `phi_generation` >> rpt strip_tac
  >- simp[generation_steps_def] >>
  drule frontier_generation_steps >> simp[generation_steps_append]
QED

Theorem phi_generation_order:
  !s x df pm li bbs roots hp out t records.
    phi_generation s x df pm li bbs roots hp out t records ==>
    !initial. (!l. MEM l roots ==> MEM l initial) ==>
      generation_order initial records
Proof
  Induct_on `phi_generation` >> rpt strip_tac
  >- simp[generation_order_def] >>
  drule frontier_generation_sources >> strip_tac >>
  simp[generation_order_append] >> conj_tac
  >- (irule generation_order_parent >> qexists `d` >>
      gvs[EVERY_MEM,FORALL_PROD] >> metis_tac[]) >>
  first_x_assum irule >> simp[MEM_FILTER,MEM_APPEND] >> metis_tac[MEM]
QED

Theorem phi_generation_sources:
  !s x df pm li bbs roots hp out t records.
    phi_generation s x df pm li bbs roots hp out t records ==>
    EVERY (\(d,f,id).
      (?fs. ALOOKUP df d = SOME fs /\ MEM f fs) /\
      (?vs. ALOOKUP li f = SOME vs /\ MEM x vs)) records
Proof
  Induct_on `phi_generation` >> rpt strip_tac >> simp[] >>
  drule frontier_generation_sources >> strip_tac >>
  simp[EVERY_APPEND] >>
  Cases_on `ALOOKUP df d` >> gvs[EVERY_MEM,FORALL_PROD] >> metis_tac[]
QED

Theorem generation_order_prefix:
  !records roots.
    generation_order roots records ==>
    !pre d f id post. records = pre ++ [(d,f,id)] ++ post ==>
      MEM d roots \/ MEM d (generation_children pre)
Proof
  Induct >> simp[generation_order_def] >>
  Cases_on `h` >> Cases_on `r` >> simp[generation_order_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> Cases_on `pre`
  >- (simp[generation_children_def] >> rpt strip_tac >> gvs[]) >>
  simp[generation_children_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[generation_children_def] >> metis_tac[MEM]
QED

Definition generation_prefix_def:
  generation_prefix x pm l records =
    REVERSE (MAP (\(d,f,id). build_phi_inst_supply id x
      (case ALOOKUP pm f of NONE => [] | SOME ps => ps))
      (FILTER (\(d,f,id). f = l) records))
End

Theorem generation_steps_blocks:
  !records bbs. generation_steps x pm records bbs =
    MAP (\bb. bb with bb_instructions :=
      generation_prefix x pm bb.bb_label records ++ bb.bb_instructions) bbs
Proof
  Induct >> simp[generation_steps_def,generation_prefix_def]
  >> Cases_on `h` >> Cases_on `r` >>
  simp[generation_steps_def,generation_prefix_def,MAP_MAP_o] >>
  rpt gen_tac >> irule MAP_CONG >> simp[] >> rpt strip_tac >>
  rename1 `MEM bb bbs` >> Cases_on `bb.bb_label = q'` >>
  simp[insert_phi_at_block_def,generation_prefix_def,APPEND_ASSOC] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND] >> REFL_TAC
QED

Theorem generation_prefix_member:
  MEM inst (generation_prefix x pm l records) ==>
  ?d id. MEM (d,l,id) records /\
    inst = build_phi_inst_supply id x
      (case ALOOKUP pm l of NONE => [] | SOME ps => ps)
Proof
  simp[generation_prefix_def,MEM_MAP,MEM_FILTER] >>
  strip_tac >> PairCases_on `y` >> gvs[] >> metis_tac[]
QED

Theorem insertion_generation_certificate:
  insert_phis_for_var_supply s x df pm li bbs roots hp = (out,t) ==>
  ?records.
    phi_generation s x df pm li bbs roots hp out t records /\
    generation_order roots records /\
    EVERY (\(d,f,id).
      (?fs. ALOOKUP df d = SOME fs /\ MEM f fs) /\
      (?vs. ALOOKUP li f = SOME vs /\ MEM x vs)) records /\
    out = MAP (\bb. bb with bb_instructions :=
      generation_prefix x pm bb.bb_label records ++ bb.bb_instructions) bbs
Proof
  strip_tac >>
  qspecl_then [`s`,`x`,`df`,`pm`,`li`,`bbs`,`roots`,`hp`] strip_assume_tac
    phi_generation_exists >>
  drule phi_generation_erasure >> strip_tac >> gvs[] >>
  qexists `records` >>
  drule phi_generation_steps >>
  simp[generation_steps_blocks] >> strip_tac >>
  metis_tac[phi_generation_order,phi_generation_sources]
QED

(* The certificate gives an exact block-position-preserving prefix, including
   duplicate labels/instructions. generation_prefix_member exposes every new
   instruction; generation_order_prefix gives its finite earlier-parent
   ancestry. Logs can include absent-label insertion operations.
   It proves no copy/PHI connectivity, default-name saturation, CFG dominance,
   or reachability. Unreachable visited writers and first spelling reuse
   remain mandatory cases for the semantic checkpoint. *)
