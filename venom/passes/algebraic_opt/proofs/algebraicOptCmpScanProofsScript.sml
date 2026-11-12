Theory algebraicOptCmpScanProofs
Ancestors
  algebraicOptDefs dfgDefs venomInst list passSimulationDefs dfgAnalysisProps

Definition ao_cmp_source_def:
  ao_cmp_source dfg inst op w v after <=>
    is_comparator inst.inst_opcode /\
    inst.inst_operands = [op; Lit w] /\ inst.inst_outputs = [v] /\
    dfg_get_uses dfg v = [after] /\
    (after.inst_opcode = ISZERO \/ after.inst_opcode = ASSERT) /\
    (?lo never hi.
      (if inst.inst_opcode = SGT \/ inst.inst_opcode = SLT
       then ao_signed_boundaries (inst.inst_opcode = GT \/ inst.inst_opcode = SGT)
       else ao_unsigned_boundaries (inst.inst_opcode = GT \/ inst.inst_opcode = SGT))
        = (lo,never,hi) /\ w <> never)
End

Definition ao_cmp_flip_cert_def:
  ao_cmp_flip_cert dfg inst action <=>
    ?op w v after. ao_cmp_source dfg inst op w v after /\
      action = (inst.inst_id, flip_comparison_opcode inst.inst_opcode,
        (if inst.inst_opcode = GT \/ inst.inst_opcode = SGT
         then w + 1w else w - 1w), op)
End

Definition ao_cmp_remove_cert_def:
  ao_cmp_remove_cert dfg inst id <=>
    ?op w v after iz_out. ao_cmp_source dfg inst op w v after /\
      after.inst_opcode = ISZERO /\ after.inst_id = id /\
      after.inst_outputs = [iz_out] /\
      LENGTH (dfg_get_uses dfg iz_out) = 1 /\
      (HD (dfg_get_uses dfg iz_out)).inst_opcode <> ASSERT
End

Definition ao_cmp_insert_cert_def:
  ao_cmp_insert_cert dfg inst action <=>
    ?op w v after. ao_cmp_source dfg inst op w v after /\
      after.inst_opcode = ASSERT /\
      action = (after.inst_id, v, inst.inst_id)
End

Theorem ao_cmp_flip_cert_intro:
  ao_cmp_source dfg inst op w v after ==>
  ao_cmp_flip_cert dfg inst
    (inst.inst_id, flip_comparison_opcode inst.inst_opcode,
     (if inst.inst_opcode = GT \/ inst.inst_opcode = SGT
      then w + 1w else w - 1w), op)
Proof
  simp[ao_cmp_flip_cert_def] >> metis_tac[]
QED

Theorem ao_cmp_remove_cert_intro:
  ao_cmp_source dfg inst op w v after /\
  after.inst_opcode = ISZERO /\ after.inst_outputs = [iz] /\
  LENGTH (dfg_get_uses dfg iz) = 1 /\
  (HD (dfg_get_uses dfg iz)).inst_opcode <> ASSERT ==>
  ao_cmp_remove_cert dfg inst after.inst_id
Proof
  simp[ao_cmp_remove_cert_def] >> metis_tac[]
QED

Theorem ao_cmp_insert_cert_intro:
  ao_cmp_source dfg inst op w v after /\ after.inst_opcode = ASSERT ==>
  ao_cmp_insert_cert dfg inst (after.inst_id, v, inst.inst_id)
Proof
  simp[ao_cmp_insert_cert_def] >> metis_tac[]
QED

Theorem ao_cmp_flip_cert_origin:
  ao_cmp_flip_cert dfg inst (id,opc,w',op) ==>
  ?w v after lo never hi.
    inst.inst_id = id /\ is_comparator inst.inst_opcode /\
    inst.inst_operands = [op; Lit w] /\ inst.inst_outputs = [v] /\
    dfg_get_uses dfg v = [after] /\
    (after.inst_opcode = ISZERO \/ after.inst_opcode = ASSERT) /\
    opc = flip_comparison_opcode inst.inst_opcode /\
    w' = (if inst.inst_opcode = GT \/ inst.inst_opcode = SGT
          then w + 1w else w - 1w) /\
    (if inst.inst_opcode = SGT \/ inst.inst_opcode = SLT
     then ao_signed_boundaries (inst.inst_opcode = GT \/ inst.inst_opcode = SGT)
     else ao_unsigned_boundaries (inst.inst_opcode = GT \/ inst.inst_opcode = SGT))
      = (lo,never,hi) /\ w <> never
Proof
  simp[ao_cmp_flip_cert_def, ao_cmp_source_def] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Definition ao_cmp_origins_def:
  ao_cmp_origins dfg xs fs rs ins <=>
    EVERY (\a. ?i. MEM i xs /\ ao_cmp_flip_cert dfg i a) fs /\
    EVERY (\a. ?i. MEM i xs /\ ao_cmp_remove_cert dfg i a) rs /\
    EVERY (\a. ?i. MEM i xs /\ ao_cmp_insert_cert dfg i a) ins
End

Theorem ao_cmp_origins_empty:
  ao_cmp_origins dfg [] [] [] []
Proof
  simp[ao_cmp_origins_def]
QED

Theorem ao_cmp_origins_extend:
  ao_cmp_origins dfg xs fs rs ins ==>
  ao_cmp_origins dfg (h::xs) fs rs ins
Proof
  simp[ao_cmp_origins_def, EVERY_MEM] >> metis_tac[]
QED

Theorem ao_cmp_origins_remove:
  ao_cmp_origins dfg xs fs rs ins /\
  ao_cmp_flip_cert dfg h f /\ ao_cmp_remove_cert dfg h r ==>
  ao_cmp_origins dfg (h::xs) (f::fs) (r::rs) ins
Proof
  strip_tac >> drule ao_cmp_origins_extend >>
  disch_then (qspec_then `h` mp_tac) >>
  simp[ao_cmp_origins_def] >> metis_tac[]
QED

Theorem ao_cmp_origins_insert:
  ao_cmp_origins dfg xs fs rs ins /\
  ao_cmp_flip_cert dfg h f /\ ao_cmp_insert_cert dfg h a ==>
  ao_cmp_origins dfg (h::xs) (f::fs) rs (a::ins)
Proof
  strip_tac >> drule ao_cmp_origins_extend >>
  disch_then (qspec_then `h` mp_tac) >>
  simp[ao_cmp_origins_def] >> metis_tac[]
QED

Theorem ao_cmp_origins_head:
  ao_cmp_flip_scan dfg xs = (fs,rs,ins) /\
  ao_cmp_origins dfg xs fs rs ins /\
  ao_cmp_flip_scan dfg (h::xs) = (fs',rs',ins') ==>
  ao_cmp_origins dfg (h::xs) fs' rs' ins'
Proof
  strip_tac >>
  drule ao_cmp_origins_extend >>
  disch_then (qspec_then `h` assume_tac) >>
  qpat_x_assum `ao_cmp_flip_scan dfg (h::xs) = _` mp_tac >>
  simp[Once ao_cmp_flip_scan_def] >> disch_tac >>
  Cases_on `is_comparator h.inst_opcode` >> gvs[] >>
  Cases_on `h.inst_operands` >> gvs[] >>
  rename1 `h.inst_operands = op::ops` >>
  Cases_on `ops` >> gvs[] >>
  rename1 `h.inst_operands = op::arg::ops` >>
  Cases_on `ops` >> gvs[] >>
  Cases_on `arg` >> gvs[] >>
  Cases_on `h.inst_outputs` >> gvs[] >>
  rename1 `h.inst_outputs = v::outs` >>
  Cases_on `outs` >> gvs[] >>
  Cases_on `LENGTH (dfg_get_uses dfg v) = 1` >> gvs[] >>
  Cases_on `(HD (dfg_get_uses dfg v)).inst_opcode = ISZERO \/
            (HD (dfg_get_uses dfg v)).inst_opcode = ASSERT`
  >- (pairarg_tac >> gvs[] >>
      Cases_on `c = never` >> gvs[] >>
      `dfg_get_uses dfg v = [HD (dfg_get_uses dfg v)]` by
        (Cases_on `dfg_get_uses dfg v` >> gvs[] >>
         rename1 `LENGTH tail = 0` >> Cases_on `tail` >> gvs[]) >>
      `ao_cmp_source dfg h op c v (HD (dfg_get_uses dfg v))` by
        (simp[ao_cmp_source_def] >> metis_tac[]) >>
      Cases_on `(HD (dfg_get_uses dfg v)).inst_opcode = ISZERO` >> gvs[]
      >- (Cases_on `(HD (dfg_get_uses dfg v)).inst_outputs` >> gvs[] >>
          rename1 `(HD (dfg_get_uses dfg v)).inst_outputs = iz::outs` >>
          Cases_on `outs` >> gvs[] >>
          Cases_on `LENGTH (dfg_get_uses dfg iz) = 1` >> gvs[] >>
          Cases_on `(HD (dfg_get_uses dfg iz)).inst_opcode = ASSERT` >> gvs[] >>
          irule ao_cmp_origins_remove >>
          metis_tac[ao_cmp_flip_cert_intro, ao_cmp_remove_cert_intro]) >>
      irule ao_cmp_origins_insert >>
      metis_tac[ao_cmp_flip_cert_intro, ao_cmp_insert_cert_intro]) >>
  gvs[]
QED

Theorem ao_cmp_flip_scan_origins:
  !xs dfg fs rs ins.
    ao_cmp_flip_scan dfg xs = (fs,rs,ins) ==>
    ao_cmp_origins dfg xs fs rs ins
Proof
  Induct >> rpt gen_tac
  >- simp[ao_cmp_flip_scan_def, ao_cmp_origins_empty] >>
  Cases_on `ao_cmp_flip_scan dfg xs` >>
  rename1 `ao_cmp_flip_scan dfg xs = (fs0, rest)` >>
  Cases_on `rest` >> strip_tac >>
  irule ao_cmp_origins_head >> metis_tac[]
QED

Theorem ao_cmp_flip_scan_flip_origin:
  !dfg xs flips removes inserts id opc w' op.
    ao_cmp_flip_scan dfg xs = (flips, removes, inserts) /\
    MEM (id,opc,w',op) flips ==>
    ?inst w v after lo never hi.
      MEM inst xs /\ inst.inst_id = id /\
      is_comparator inst.inst_opcode /\
      inst.inst_operands = [op; Lit w] /\ inst.inst_outputs = [v] /\
      dfg_get_uses dfg v = [after] /\
      (after.inst_opcode = ISZERO \/ after.inst_opcode = ASSERT) /\
      opc = flip_comparison_opcode inst.inst_opcode /\
      w' = (if inst.inst_opcode = GT \/ inst.inst_opcode = SGT
            then w + 1w else w - 1w) /\
      (if inst.inst_opcode = SGT \/ inst.inst_opcode = SLT
       then ao_signed_boundaries (inst.inst_opcode = GT \/ inst.inst_opcode = SGT)
       else ao_unsigned_boundaries (inst.inst_opcode = GT \/ inst.inst_opcode = SGT))
        = (lo,never,hi) /\ w <> never
Proof
  rpt strip_tac >> drule ao_cmp_flip_scan_origins >>
  simp[ao_cmp_origins_def, EVERY_MEM] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule ao_cmp_flip_cert_origin >> strip_tac >>
  qexists_tac `i` >> gvs[] >> metis_tac[]
QED

Theorem ao_cmp_flip_scan_remove_origin:
  !dfg xs flips removes inserts id.
    ao_cmp_flip_scan dfg xs = (flips,removes,inserts) /\ MEM id removes ==>
    ?inst op w v after iz_out lo never hi.
      MEM inst xs /\ is_comparator inst.inst_opcode /\
      inst.inst_operands = [op; Lit w] /\ inst.inst_outputs = [v] /\
      dfg_get_uses dfg v = [after] /\
      after.inst_opcode = ISZERO /\ after.inst_id = id /\
      after.inst_outputs = [iz_out] /\
      LENGTH (dfg_get_uses dfg iz_out) = 1 /\
      (HD (dfg_get_uses dfg iz_out)).inst_opcode <> ASSERT /\
      (if inst.inst_opcode = SGT \/ inst.inst_opcode = SLT
       then ao_signed_boundaries (inst.inst_opcode = GT \/ inst.inst_opcode = SGT)
       else ao_unsigned_boundaries (inst.inst_opcode = GT \/ inst.inst_opcode = SGT))
        = (lo,never,hi) /\ w <> never
Proof
  rpt strip_tac >> drule ao_cmp_flip_scan_origins >>
  simp[ao_cmp_origins_def, EVERY_MEM] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `ao_cmp_remove_cert _ _ _` mp_tac >>
  simp[ao_cmp_remove_cert_def, ao_cmp_source_def] >> strip_tac >>
  qexists_tac `i` >> gvs[] >> metis_tac[]
QED

Theorem ao_cmp_flip_scan_insert_origin:
  !dfg xs flips removes inserts id v cmp_id.
    ao_cmp_flip_scan dfg xs = (flips,removes,inserts) /\
    MEM (id,v,cmp_id) inserts ==>
    ?inst op w after lo never hi.
      MEM inst xs /\ inst.inst_id = cmp_id /\
      is_comparator inst.inst_opcode /\
      inst.inst_operands = [op; Lit w] /\ inst.inst_outputs = [v] /\
      dfg_get_uses dfg v = [after] /\
      after.inst_opcode = ASSERT /\ after.inst_id = id /\
      (if inst.inst_opcode = SGT \/ inst.inst_opcode = SLT
       then ao_signed_boundaries (inst.inst_opcode = GT \/ inst.inst_opcode = SGT)
       else ao_unsigned_boundaries (inst.inst_opcode = GT \/ inst.inst_opcode = SGT))
        = (lo,never,hi) /\ w <> never
Proof
  rpt strip_tac >> drule ao_cmp_flip_scan_origins >>
  simp[ao_cmp_origins_def, EVERY_MEM] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `ao_cmp_insert_cert _ _ _` mp_tac >>
  simp[ao_cmp_insert_cert_def, ao_cmp_source_def] >> strip_tac >>
  qexists_tac `i` >> gvs[] >> metis_tac[]
QED

