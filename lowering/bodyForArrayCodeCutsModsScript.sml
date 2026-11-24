(* Paired compiler cuts for linked Array For statements. *)
Theory bodyForArrayCodeCutsMods
Ancestors
  bodyFullForArrayRound
  loweringPosts stmtLowering compileEnv gasShadow
Libs
  monadsyntax

Theorem for_array_paired_cuts_mods:
  expr_type e = ArrayT sty bd /\ c.ce_alloca_locals /\
  local_ptrs_reserved c sa0 /\ gas_shadow_state sa0 shadow_sa0 /\
  compile_stmt c lctx ret_ty (For id fty (Array e) n loop_body) sa0 = ((),sb) /\
  compile_stmt (gas_shadow_env T c) lctx ret_ty
    (gas_shadow_stmt (For id fty (Array e) n loop_body)) shadow_sa0 =
    ((),shadow_sb) /\
  fn_has_code sa0 sb func /\
  fn_has_code shadow_sa0 shadow_sb shadow_func ==>
  ?vv sbExpr shadow_sbExpr loc len_op saL bc saD saA xd capacity aidItem
   entry cond bod incr exit idx invalid valid done_var next_var
   sa stride off_op sm sum_op sn addr saCopy sbCopy sbBody sj
   shadow_sbCopy shadow_sbBody.
    for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
      (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
      (bc,saD,saA,xd,capacity,aidItem)
      (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
      (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
      (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\ not_fresh_at sa done_var /\
      next_var = STRING #"%" (toString sj.cs_next_var)
Proof
  rpt strip_tac >> irule for_nonslot_array_layout_full_with_increment >>
  rpt conj_tac >> (fn g => if length (fst g) = 8 andalso String.translate (fn c => if Char.isSpace c then "" else String.str c) (PP.pp_to_string 100 Parse.pp_term (snd g)) = "∃lctxnshadow_sb.compile_stmtclctxret_ty(Foridfty(Arraye)nloop_body)sa0=((),sb)∧compile_stmt(gas_shadow_envTc)lctxret_ty(gas_shadow_stmt(Foridfty(Arraye)nloop_body))shadow_sa0=((),shadow_sb)∧fn_has_codeshadow_sa0shadow_sbshadow_func" then (metis_tac[]) g else (first_assum ACCEPT_TAC) g)
QED
