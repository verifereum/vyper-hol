(* Original indices, never generated instruction positions, select restores. *)
Theory fmpLowerIndexedProps
Ancestors
  fmpLowerDefs list

Theorem fmp_select_point_restores_filter:
  !restores p.
  fmp_select_point_restores p restores =
    (MAP SND (FILTER (\r. FST r = p) restores),
     FILTER (\r. FST r <> p) restores)
Proof
  Induct >> simp[fmp_select_point_restores_def] >>
  Cases_on `h` >> simp[fmp_select_point_restores_def] >>
  rpt gen_tac >> Cases_on `q = p` >> simp[]
QED

(* Selection consumes every occurrence at this point, and only this point. *)
Theorem fmp_select_point_restores_once:
  fmp_select_point_restores p restores = (bases,later) ==>
  ~MEM p (MAP FST later) /\
  (!base. MEM base bases <=> MEM (p,base) restores) /\
  (!q base. MEM (q,base) later <=> MEM (q,base) restores /\ q <> p)
Proof
  simp[fmp_select_point_restores_filter, MEM_MAP, MEM_FILTER] >>
  rpt strip_tac >> gvs[MEM_FILTER, MEM_MAP] >>
  metis_tac[pairTheory.PAIR, pairTheory.FST, pairTheory.SND]
QED

(* This is the exact production decomposition, including supply order. *)
Theorem fmp_lower_indexed_cons:
  fmp_lower_indexed infos ctx runner label k s restores (inst::insts) =
    SOME (code,leftover,s') <=>
  ?bases later prefix s0 head s1 tail.
    fmp_select_point_restores (label,k) restores = (bases,later) /\
    fmp_emit_restores runner s bases = (prefix,s0) /\
    fmp_lower_inst infos ctx runner s0 inst = SOME (head,s1) /\
    fmp_lower_indexed infos ctx runner label (SUC k) s1 later insts =
      SOME (tail,leftover,s') /\
    code = prefix ++ head ++ tail
Proof
  Cases_on `fmp_select_point_restores (label,k) restores` >>
  simp[fmp_lower_indexed_def, AllCaseEqs()] >> metis_tac[]
QED

(* Neither an endpoint nor a point outside this original interval is consumed.
   In particular (label,k + LENGTH insts) remains in leftover, never emitted. *)
Theorem fmp_lower_indexed_leftover:
  !insts k s restores code leftover s'.
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (code,leftover,s') ==>
  (!q base. MEM (q,base) leftover <=>
    MEM (q,base) restores /\
    ~(FST q = label /\ k <= SND q /\ SND q < k + LENGTH insts))
Proof
  Induct
  >- simp[fmp_lower_indexed_def] >>
  rpt gen_tac >> simp[fmp_lower_indexed_cons] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule fmp_select_point_restores_once >> strip_tac >>
  Cases_on `q` >> simp[] >>
  Cases_on `q' = label` >> simp[] >>
  Cases_on `MEM ((label,r),base') restores` >> simp[] >>
  rpt (pop_assum kall_tac) >> decide_tac
QED

Theorem fmp_lower_indexed_no_endpoint:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (code,leftover,s') ==>
  (MEM ((label,k + LENGTH insts),target) leftover <=>
   MEM ((label,k + LENGTH insts),target) restores)
Proof
  strip_tac >> drule fmp_lower_indexed_leftover >>
  disch_then (qspecl_then [`(label,k + LENGTH insts)`,`target`] mp_tac) >> simp[]
QED

val _ = List.app (fn (name,th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("unexpected oracle dependency in " ^ name))
  (DB.thms "fmpLowerIndexedProps");
