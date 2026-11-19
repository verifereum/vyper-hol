(* Preserve every structural arm at a singleton unreachable deletion. *)
Theory staticAbortOptPruneUnreachableArms
Ancestors
  staticAbortOptPruneUnreachableLayout
  asmOptimizer asmSplice asmSymSem finite_map words list rich_list arithmetic pred_set

Theorem prune_one_arm_geometry:
  !pre t x tail (V:(num#num)->bool) e pc fall taken p q d r Hit.
    p = pre ++ [t;x] ++ tail ==> q = pre ++ [t] ++ tail ==>
    d = LENGTH pre+1 ==> r = (\i. if i < d then i else i-1) ==>
    Hit = (\z l i.
      ?off. FLOOKUP (SND (compute_label_offsets z)) l = SOME off /\
        off < dimword(:256) /\ FLOOKUP (build_offset_to_pc z) off = SOME i) ==>
    asm_terminal_op t /\ ~asm_reachable_marker x /\ asm_static_wf p /\
    e IN V /\ pc e <> d /\
    (!v. v IN V ==> pc v < LENGTH p /\
      ?n (path:num->num#num). path 0=e /\ path n=v /\
        !k. k<n ==> fall (path k) (path (SUC k)) \/ ?l. taken (path k) l (path (SUC k))) /\
    (!a b. fall a b ==> a IN V /\ b IN V /\
      ~asm_terminal_op (EL (pc a) p) /\ pc b=pc a+1) /\
    (!a l b. taken a l b ==> a IN V /\ b IN V /\ Hit p l (pc b)) ==>
    (!v. v IN V ==> pc v <> d /\ r (pc v) < LENGTH q /\
      EL (r (pc v)) q = EL (pc v) p) /\
    (!a b. fall a b ==> r (pc b)=r (pc a)+1) /\
    (!a l b. taken a l b ==> Hit q l (r (pc b)))
Proof
  rpt gen_tac >>
  ntac 5 (disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def])) >>
  strip_tac >>
  `!a l b. taken a l b ==> pc b <> d /\ Hit q l (r (pc b))` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!a l b. taken a l b ==> _` drule >>
     simp[Abbr `Hit`] >> strip_tac >>
     qspecl_then [`pre`, `t`, `x`, `tail`] mp_tac (SIMP_RULE bool_ss [] prune_one_canonical_layout) >>
     simp[Abbr `p`, Abbr `q`, Abbr `d`, Abbr `r`] >>
     disch_then (drule_all o CONJUNCT1) >> metis_tac[]) >>
  `!a b. fall a b ==> pc b <> d` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!a b. fall a b ==> _` drule >> strip_tac >>
     strip_tac >>
     `pc a = LENGTH pre` by (fs[Abbr `d`] >> decide_tac) >>
     qpat_x_assum `~asm_terminal_op _` mp_tac >>
     simp[Abbr `p`] >>
     pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND, EL_LENGTH_APPEND_0] >> simp[]) >>
  `!v. v IN V ==> pc v <> d` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!v. v IN V ==> _` drule >>
     disch_then (mp_tac o CONJUNCT2) >>
     strip_tac >> Cases_on `n` >- metis_tac[] >>
     rename1 `path (SUC j) = v` >>
     qpat_assum `!k. k < SUC j ==> _`
       (qspec_then `j` (strip_assume_tac o REWRITE_RULE [prim_recTheory.LESS_SUC_REFL]))
     >- (qpat_assum `!a b. fall a b ==> pc b <> d` drule >> simp[]) >>
     qpat_assum `!a l b. taken a l b ==> pc b <> d /\ _` drule >> simp[]) >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      `pc v < LENGTH p /\ pc v <> d` by metis_tac[] >>
      `LENGTH (pre ++ [t]) = d` by simp[Abbr `d`] >>
      `(pre ++ [t]) ++ [x] ++ tail = p /\
       (pre ++ [t]) ++ [] ++ tail = q` by
         (pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >> simp[Abbr `p`, Abbr `q`]) >>
      `splice_pc d 1 0 (pc v) = r (pc v)` by
        (Cases_on `pc v < d` >> simp[splice_pc_def, Abbr `r`] >> decide_tac) >>
      simp[] >>
      mp_tac (Q.INST [`pfx` |-> `pre ++ [t:asm_inst]`, `pat` |-> `[x]`,
                       `repl` |-> `[]`, `sfx` |-> `tail`,
                       `i` |-> `(pc:(num#num)->num) v`]
                  (INST_TYPE [alpha |-> ``:asm_inst``] splice_fetch)) >>
      pure_asm_rewrite_tac [LENGTH, ONE, ADD_CLAUSES] >>
      `pc v < d \/ d + 1 <= pc v` by decide_tac >> simp[]) >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!a b. fall a b ==> _ /\ _ /\ _ /\ pc b = pc a+1` drule >>
     strip_tac >>
     `pc a <> d /\ pc b <> d` by metis_tac[] >>
     `pc b < d <=> pc a < d` by decide_tac >>
     Cases_on `pc a < d` >> simp[Abbr `r`] >> decide_tac) >>
  metis_tac[]
QED
