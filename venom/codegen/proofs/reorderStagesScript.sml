(* Proof views of the existing reorder implementation.
   TOP-LEVEL: reorder_one_stages.
   Helpers: restore, depth-reduction and final placement phases. *)
Theory reorderStages
Ancestors
  stackPlanOps stackPlanTypes stackPlanGen stackModel planWf dfgDefs
  foldlSim indexedLists list rich_list arithmetic finite_map
Libs BasicProvers

Definition reorder_restore_def:
  reorder_restore op final_dist num_ops ps =
    case stack_get_unfixed_depth op final_dist num_ops ps.ps_stack of
      NONE => do_restore op ps
    | SOME _ => ([]:stack_op list,ps)
End

Definition reorder_place_def:
  reorder_place dfg op dist final_dist ps =
    if dist = final_dist then ([]:stack_op list,ps)
    else if final_dist < LENGTH ps.ps_stack /\
            operand_equiv dfg op (stack_peek final_dist ps.ps_stack) then
      ([],ps with ps_stack := stack_poke final_dist op
        (stack_poke dist (stack_peek final_dist ps.ps_stack) ps.ps_stack))
    else
      let (ops1,mid) = do_swap dist ps;
          (ops2,post) = do_swap final_dist mid
      in (ops1 ++ ops2,post)
End

Definition reorder_finish_def:
  reorder_finish dfg op final_dist num_ops ps =
    case stack_get_unfixed_depth op final_dist num_ops ps.ps_stack of
      NONE => ([]:stack_op list,ps)
    | SOME dist => reorder_place dfg op dist final_dist ps
End

Theorem reorder_restore_source:
  reorder_restore op final_dist num_ops ps =
    (case stack_get_unfixed_depth op final_dist num_ops ps.ps_stack of
       SOME _ => ([]:stack_op list,ps)
     | NONE =>
         case FLOOKUP ps.ps_spilled op of
           SOME _ => do_restore op ps
         | NONE => ([],ps))
Proof
  Cases_on `stack_get_unfixed_depth op final_dist num_ops ps.ps_stack` >>
  simp[reorder_restore_def] >> Cases_on `FLOOKUP ps.ps_spilled op` >>
  simp[do_restore_def]
QED

Theorem reduce_depth_plan_missing:
  !fuel pending op final_dist num_ops ps.
    stack_get_unfixed_depth op final_dist num_ops ps.ps_stack = NONE ==>
    reduce_depth_plan fuel pending op final_dist num_ops ps = ([],ps)
Proof
  Cases_on `fuel` >> simp[reduce_depth_plan_def]
QED

Theorem reorder_foldl_body_eq[local]:
  !dfg target_ops.
    foldl_body (\(idx,op) ps. reorder_one dfg target_ops idx op ps) =
    (\(ops, ps) (idx, op).
      let (step_ops, ps') = reorder_one dfg target_ops idx op ps in
      (ops ++ step_ops, ps'))
Proof
  rpt gen_tac >>
  simp[FUN_EQ_THM, foldl_body_def, pairTheory.FORALL_PROD]
QED

Theorem reorder_plan_eq_plan_steps:
  !dfg target_ops ps.
    reorder_plan dfg target_ops ps =
    plan_steps (\(idx,op) ps. reorder_one dfg target_ops idx op ps)
      (MAPi (\i op. (i, op)) target_ops) ps
Proof
  rpt gen_tac >>
  REWRITE_TAC[reorder_plan_def] >>
  REWRITE_TAC[GSYM reorder_foldl_body_eq] >>
  REWRITE_TAC[GSYM plan_steps_eq_foldl]
QED


Theorem plan_steps_cons_result:
  !step x xs ps ops ps'.
    plan_steps step (x::xs) ps = (ops,ps') ==>
    ?step_ops ps1 rest_ops.
      step x ps = (step_ops,ps1) /\
      plan_steps step xs ps1 = (rest_ops,ps') /\
      ops = step_ops ++ rest_ops
Proof
  rpt gen_tac >>
  simp[Once plan_steps_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[]
QED


Theorem reorder_one_stages:
  !dfg pending idx op ps.
    reorder_one dfg pending idx op ps =
    let num_ops = LENGTH pending;
        final_dist = num_ops - 1 - idx;
        (restore_ops,mid) = reorder_restore op final_dist num_ops ps;
        (reduce_ops,reduced) =
          reduce_depth_plan (LENGTH mid.ps_stack) pending op final_dist num_ops mid;
        (place_ops,post) = reorder_finish dfg op final_dist num_ops reduced
    in (restore_ops ++ reduce_ops ++ place_ops,post)
Proof
  rpt gen_tac >>
  Cases_on `reorder_restore op (LENGTH pending - 1 - idx) (LENGTH pending) ps` >>
  rename1 `reorder_restore _ _ _ _ = (restore_ops,mid)` >>
  rewrite_tac [Once reorder_one_def] >>
  simp_tac std_ss [LET_THM, GSYM reorder_restore_source] >>
  asm_simp_tac (srw_ss()) [] >>
  Cases_on `stack_get_unfixed_depth op (LENGTH pending - 1 - idx)
    (LENGTH pending) mid.ps_stack`
  >- (asm_simp_tac (srw_ss())
        [reduce_depth_plan_missing, reorder_finish_def, LET_THM]) >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME dist` >>
  Cases_on `dist <= 16`
  >- (`~(dist > 16)` by decide_tac >>
      asm_simp_tac (srw_ss()) [reduce_depth_plan_le_16, reorder_finish_def,
        reorder_place_def, LET_THM] >>
      every_case_tac >> gvs[LET_THM, APPEND_ASSOC] >>
      rpt (pairarg_tac >> gvs[LET_THM, APPEND_ASSOC])) >>
  `dist > 16` by decide_tac >>
  Cases_on `reduce_depth_plan (LENGTH mid.ps_stack) pending op
    (LENGTH pending - 1 - idx) (LENGTH pending) mid` >>
  rename1 `reduce_depth_plan _ _ _ _ _ _ = (reduce_ops,reduced)` >>
  Cases_on `stack_get_unfixed_depth op (LENGTH pending - 1 - idx)
    (LENGTH pending) reduced.ps_stack` >>
  asm_simp_tac (srw_ss()) [reorder_finish_def, reorder_place_def, LET_THM,
    APPEND_ASSOC] >> every_case_tac >> gvs[LET_THM, APPEND_ASSOC] >>
  rpt (pairarg_tac >> gvs[LET_THM, APPEND_ASSOC])
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed reorder phase proof: " ^ name)
  end) (DB.thms "reorderStages")
