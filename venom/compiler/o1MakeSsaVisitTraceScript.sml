Theory o1MakeSsaVisitTrace
Ancestors
  makeSsaCurrentDefs makeSsaCurrentInduct irSupply venomInst list pair alist

(* Snapshots follow the lexical ancestor path, never the traversal prefix. *)
Datatype:
  ssa_visit_event = <|
    sve_label : string;
    sve_in : (string # num) list # (string # string list) list;
    sve_out : (string # num) list # (string # string list) list;
    sve_supply_in : ir_supply;
    sve_supply_out : ir_supply;
    sve_before : instruction list;
    sve_after : instruction list;
    sve_succs : string list;
    sve_path : (string # instruction list # instruction list) list
  |>
End

Definition visit_blocks_def:
  (visit_blocks path s rs bbs sm (DNode lbl children) =
    case lookup_block lbl bbs of
      NONE => ((FST rs,s,bbs),[])
    | SOME bb =>
        let (rs1,s1,insts) = rename_current_block_insts s rs bb.bb_instructions in
        let bbs1 = replace_block lbl (bb with bb_instructions := insts) bbs in
        let succs = case ALOOKUP sm lbl of NONE => [] | SOME ss => ss in
        let bbs2 = update_current_succ_phis rs1 lbl bbs1 succs in
        let (result,events) = visit_children
          (path ++ [(lbl,bb.bb_instructions,insts)])
          s1 (FST rs1) (SND rs1) bbs2 sm children in
        (result, <| sve_label := lbl; sve_in := rs; sve_out := rs1;
          sve_supply_in := s; sve_supply_out := s1;
          sve_before := bb.bb_instructions; sve_after := insts;
          sve_succs := succs; sve_path := path |> :: events)) /\
  (visit_children path s ctrs stacks bbs sm [] = ((ctrs,s,bbs),[])) /\
  (visit_children path s ctrs stacks bbs sm (child::rest) =
    let ((ctrs1,s1,bbs1),events1) = visit_blocks path s (ctrs,stacks) bbs sm child in
    let (result,events2) = visit_children path s1 ctrs1 stacks bbs1 sm rest in
      (result,events1 ++ events2))
End

Theorem visit_erasure:
  (!tree path s rs bbs sm.
    FST (visit_blocks path s rs bbs sm tree) =
      rename_current_blocks s rs bbs sm tree) /\
  (!trees path s ctrs stacks bbs sm.
    FST (visit_children path s ctrs stacks bbs sm trees) =
      rename_current_children s ctrs stacks bbs sm trees)
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once visit_blocks_def, Once rename_current_blocks_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >>
      rpt (pairarg_tac >> gvs[]) >> metis_tac[FST]) 
  >- simp[visit_blocks_def, rename_current_blocks_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once visit_blocks_def, Once rename_current_blocks_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[FST, PAIR_EQ]
QED

(* The second call uses stacks, NOT the first child's local outgoing stacks.
   Only counters, supply and the mutable block list cross the sibling boundary. *)
Theorem visit_two_children:
  visit_blocks path s (ctrs,stacks) bbs sm left = ((ctrs1,s1,bbs1),events1) /\
  visit_blocks path s1 (ctrs1,stacks) bbs1 sm right = ((ctrs2,s2,bbs2),events2) ==>
  visit_children path s ctrs stacks bbs sm [left;right] =
    ((ctrs2,s2,bbs2),events1 ++ events2)
Proof
  simp[visit_blocks_def]
QED

Theorem visit_missing_block:
  lookup_block lbl bbs = NONE ==>
  visit_blocks path s rs bbs sm (DNode lbl children) = ((FST rs,s,bbs),[])
Proof
  simp[Once visit_blocks_def]
QED

Theorem visit_leaf_event:
  lookup_block lbl bbs = SOME bb /\
  rename_current_block_insts s rs bb.bb_instructions = (rt,t,insts) /\
  succs = (case ALOOKUP sm lbl of NONE => [] | SOME ss => ss) ==>
  visit_blocks path s rs bbs sm (DNode lbl []) =
    ((FST rt,t,update_current_succ_phis rt lbl
       (replace_block lbl (bb with bb_instructions := insts) bbs) succs),
     [<| sve_label := lbl; sve_in := rs; sve_out := rt;
         sve_supply_in := s; sve_supply_out := t;
         sve_before := bb.bb_instructions; sve_after := insts;
         sve_succs := succs; sve_path := path |>])
Proof
  simp[visit_blocks_def]
QED
