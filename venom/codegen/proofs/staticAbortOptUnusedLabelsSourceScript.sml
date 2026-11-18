Theory staticAbortOptUnusedLabelsSource
Ancestors
  staticAbortOptUnusedLabelsBoundaryProbe asmToBytecodeProofs asmEncodeParse
  codegenEncodingWf codegenRel asmWf asmSymSem asmSem asmIR symbolResolve blockSimHelpers
  asmOptimizer list rich_list finite_map pred_set words
  staticAbortOptPruneUnreachableLayout

Theorem lookup_at_code_label_name[local]:
  asm_static_wf p /\ d < LENGTH p /\ EL d p = AsmLabel l /\
  FLOOKUP (SND (compute_label_offsets p)) a = SOME off /\
  FLOOKUP (build_offset_to_pc p) off = SOME d ==> a = l
Proof
  strip_tac >> drule_all lookup_pair_code_label_index >>
  simp[INDEX_OF_eq_SOME]
QED

Theorem unused_label_source_contraction:
  !p pre l tail cc req V e rank pc height need tag boolean edge.
  let Shape =
    \p cc req pc height need tag boolean i (t:asm_state).
      t.as_pc = pc i /\ LENGTH t.as_stack = height i /\
      t.as_call_ctx = cc /\ t.as_requests = req /\
      (need i ==> t.as_call_ctx.cc_static) /\
      (!k l origin. tag i k = SOME(l,origin) ==>
         k < height i /\ origin < LENGTH p /\
         (EL origin p = AsmPushLabel l \/
          (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
         ?off dest.
           FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
           off < dimword(:256) /\
           FLOOKUP (build_offset_to_pc p) off = SOME dest /\
           EL k t.as_stack = (n2w off:bytes32)) /\
      (!k. boolean i k ==> k < height i /\
         (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))
  in
  let Flow =
    \p pc height tag boolean (x:num#num) (y:num#num).
    let hi = height x; hj = height y; ins = EL (pc x) p in
    let inherit =
      \(src:num -> num option)
        (fresh:num -> (string#num)option) (bnew:num -> bool).
        (!k l origin. tag y k = SOME(l,origin) ==>
           k < hj /\ (fresh k = SOME(l,origin) \/
           ?a. src k = SOME a /\ a < hi /\ tag x a = SOME(l,origin))) /\
        (!k. boolean y k ==> k < hj /\
           (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean x a))
    in
    case ins of
      AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t u.
            asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
              (AsmPush bs) t = AsmOK u ==>
            (EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w))
    | AsmPushLabel l =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 then SOME(l,pc x) else NONE) (\k. F)
    | AsmPushOfst l d =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ d=0 then SOME(l,pc x) else NONE) (\k. F)
    | AsmOp name =>
        (case ALOOKUP dup_table name of
           SOME n =>
             n < hi /\ hj = hi+1 /\
             inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
         | NONE =>
           case ALOOKUP swap_table name of
             SOME n =>
               0 < n /\ n < hi /\ hj = hi /\
               inherit (\k. SOME(if k=0 then n else if k=n then 0 else k))
                 (\k. NONE) (\k. F)
           | NONE =>
             let a = asm_op_arity name; m = hj + asm_op_arity name - hi in
             a <= hi /\ hj = m+(hi-a) /\
             ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
             inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
               (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                 !t u. LENGTH t.as_stack=hi /\
                   asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                     ins t = AsmOK u ==>
                   (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
    | _ => F
  in
  let Open =
    \p cc req (V:(num#num)->bool) X rank pc height need
      (tag:(num#num)->num->(string#num)option)
      (boolean:(num#num)->num->bool) edge.
    let S = Shape p cc req pc height need tag boolean in
    let target = \x y.
      ?l origin off. tag x 0 = SOME(l,origin) /\
        FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
        off < dimword(:256) /\
        FLOOKUP (build_offset_to_pc p) off = SOME(pc y)
    in
      FINITE V /\ X SUBSET V /\
      (!x. x IN V ==> ?t. S x t) /\
      (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
      (!x y. edge x y ==>
         x IN V DIFF X /\ y IN V /\ rank y < rank x /\
         Flow p pc height tag boolean x y /\
         (if EL (pc x) p = AsmOp "JUMP" then target x y
          else if EL (pc x) p = AsmOp "JUMPI"
               then pc y = pc x+1 \/ target x y
          else pc y = pc x+1)) /\
      (!x t. x IN V DIFF X /\ S x t ==>
         (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                      p 1 t = AsmRevert u \/
                asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                      p 1 t = AsmFault u) /\ u.as_requests=req) \/
         (?y u. edge x y /\
            asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
              p 1 t = AsmOK u /\ S y u))
  in
  let Reach = \(edge:(num#num)->(num#num)->bool) e x.
    ?n (path:num->num#num).
      path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))
  in
  let d = LENGTH pre; L = SND (compute_label_offsets p);
      B = build_offset_to_pc p; S = Shape p cc req pc height need tag boolean in
  p=pre++[AsmLabel l]++tail /\ asm_static_wf p /\
  ~MEM l (asm_label_refs p) /\ Open p cc req V {} rank pc height need tag boolean edge /\
  e IN V /\ (!x. x IN V ==> Reach edge e x) ==>
  (!x k a j. x IN V /\ tag x k=SOME(a,j) ==>
     a<>l /\ j<>d /\ (!off. FLOOKUP L a=SOME off ==> FLOOKUP B off <> SOME d)) /\
  (!x y. edge x y /\ pc y=d ==> EL (pc x) p <> AsmOp "JUMP" /\ pc x+1=d) /\
  (!x. x IN V /\ pc x=d ==>
     ?y. edge x y /\ y IN V /\ rank y < rank x /\ pc y=d+1 /\ height y=height x /\
         (!k a j. tag y k=SOME(a,j) ==> tag x k=SOME(a,j)) /\
         (!k. boolean y k ==> boolean x k) /\ (!t. S x t ==> S y (t with as_pc := d+1)))
Proof
  rpt gen_tac >>
  qmatch_goalsub_abbrev_tac `LET _ Shape` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Flow` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Open` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Reach` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  simp[Abbr `Open`] >> strip_tac >>
  qabbrev_tac `Realizes = Shape p cc req pc height need tag boolean` >>
  qabbrev_tac `d = LENGTH pre` >>
  `d < LENGTH p /\ EL d p = AsmLabel l` by
    (simp[Abbr `d`, EL_APPEND_EQN]) >>
  conj_asm1_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!x. x IN V ==> ?t. Realizes x t` (qspec_then `x` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (qx_choose_then `t0` mp_tac) >>
      simp[Abbr `Realizes`, Abbr `Shape`] >> strip_tac >>
      qpat_assum `!k l origin. tag x k = SOME(l,origin) ==> _`
        (qspecl_then [`k`, `a`, `j`] mp_tac) >>
      simp[] >> strip_tac >>
      `j <> d` by (spose_not_then SUBST_ALL_TAC >> gvs[]) >>
      `a <> l` by
        (strip_tac >>
         `?delta. MEM (AsmPushLabel l) p \/ MEM (AsmPushOfst l delta) p \/
                  MEM (AsmDataLabel l) p` by metis_tac[MEM_EL] >>
         mp_tac (Q.INST [`tags` |-> `K (SOME(l,delta))`]
                   unused_label_excludes_provenanced_incoming_tag) >>
         simp[IgnAsm `p = pre ++ [AsmLabel l] ++ tail`]) >>
      metis_tac[lookup_at_code_label_name]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!x y. edge x y ==> _` (qspecl_then [`x`, `y`] mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      `~(?a j off. tag x 0 = SOME(a,j) /\
                  FLOOKUP (SND(compute_label_offsets p)) a = SOME off /\
                  off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME(pc y))`
        by metis_tac[] >>
      Cases_on `EL (pc x) p = AsmOp "JUMP"`
      >- (gvs[] >> metis_tac[]) >>
      Cases_on `EL (pc x) p = AsmOp "JUMPI"` >> gvs[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!x. x IN V ==> ?t. Realizes x t` (qspec_then `x` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `t0` assume_tac) >>
  `t0.as_pc = pc x` by
    (qpat_assum `Realizes x t0` mp_tac >>
     simp[NoAsms, Abbr `Realizes`, Abbr `Shape`] >> strip_tac >> simp[]) >>
  `asm_block_at p t0.as_pc [AsmLabel l]` by
    simp[asm_block_at_def, IgnAsm `p = pre ++ [AsmLabel l] ++ tail`] >>
  `asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p 1 t0 =
   AsmOK (t0 with as_pc := t0.as_pc+1)` by metis_tac[label_op_asm_steps] >>
  qpat_x_assum `!x t. x IN V /\ Realizes x t ==> _`
    (qspecl_then [`x`, `t0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[IgnAsm `p = pre ++ [AsmLabel l] ++ tail`] >>
  disch_then (qx_choose_then `y` strip_assume_tac) >>
  qpat_x_assum `!x y. edge x y ==> _` (qspecl_then [`x`, `y`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[Abbr `Flow`, IgnAsm `p = pre ++ [AsmLabel l] ++ tail`] >> strip_tac >>
  `need y ==> cc.cc_static` by
    ((qpat_assum `Realizes y _` mp_tac >>
     simp[Abbr `Realizes`, Abbr `Shape`] >> strip_tac >> simp[] >> (metis_tac[Abbr `Realizes`, Abbr `Shape`]))) >>
  qexists `y` >> simp[] >>
  gen_tac >> simp[Abbr `Shape`] >> strip_tac >> simp[] >>
  (* Simplification has already discharged the inherited Boolean demands. *)
  rpt gen_tac >> strip_tac >>
  qpat_assum `!k a j. tag y k = SOME(a,j) ==> _` drule >> strip_tac >>
  qpat_assum `!k a j. tag x k = SOME(a,j) ==> _` drule >> simp[]
QED
