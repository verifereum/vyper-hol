(* The exhausted linked Array uses the comparison and exit of the paired cuts. *)
Theory bodyForArrayNilCutMods
Ancestors
  bodyForArrayCodeCutsMods bodyForArrayNilExitMods bodyFullForArrayRound
  bodyForArrayHeaderMods exprLoweringProps loweringPosts compileEnv
  vyperStorageFootprint fragGasOriginPtr venomInst venomExecSemantics
  freshWrites

Theorem for_array_nil_from_cuts_mods:
  for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond,bod,incr,exit,idx,invalid,valid,dv,next_var)
    addr_cut (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
  local_ptrs_reserved c sa0 /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    for_array_header_mods mods DF lo d ctx func c cx env id st0
      (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu) (xd,dw,capacity,aidItem)
      vs (vv_operand vv,bw,len_op,idx) cond Route H [] ee G tn s) ==>
  ?t G1 tn1. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1) /\
    for_array_done_mods DF lo d ctx func c cx lctx sa0 sb es0 s0 G0 tn0
      H (ee with gas_obs := []) G1 tn1 t
Proof
  PairCases_on `addr_cut` >> strip_tac >>
  qhdtm_x_assum `for_nonslot_layout`
    (strip_assume_tac o REWRITE_RULE [for_nonslot_layout_def]) >>
  rpt (qhdtm_x_assum `ci_mono`
    (assume_tac o cj 2 o REWRITE_RULE [ci_mono_def])) >>
  `sa0.cs_next_var <= sb.cs_next_var` by decide_tac >>
  qpat_x_assum `EVERY _ [idx;dv;next_var]`
    (strip_assume_tac o SIMP_RULE bool_ss [listTheory.EVERY_DEF]) >>
  `~not_fresh_at sa0 dv` by
    (strip_tac >>
     `not_fresh_at saL dv` suffices_by simp[] >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa0` >> simp[]) >>
  irule for_array_nil_exit_mods >> simp[] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (part_match_exists_tac (fst o dest_conj) o concl) >>
  qpat_assum `lookup_block cond _ = SOME _`
    (part_match_exists_tac (List.last o strip_conj) o concl) >>
  simp[]
QED
