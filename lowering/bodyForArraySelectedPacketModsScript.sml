(* Keep the syntactic Array selector with the capture. Only the source
   entry or immutable root looked up at the current endpoint can change. *)
Theory bodyForArraySelectedPacketMods
Ancestors
  bodyForArrayOriginMods bodyForArrayHeaderMods bodyForArrayEntryMods
  loweringPosts bodyFullPredsMods vyperTypeContract vyperTypeSystem
  vyperStorageFootprint vyperValueOperation vyperState vyperAST
  compileEnv ptrDiscipline words list finite_map

val _ = Parse.hide "body";

Datatype:
  for_array_selector = ArraySelectorPlain
    | ArraySelectorHeld base_assignment_target (identifier list) (subscript list)
        scope_entry type_value string num (256 word) num
    | ArraySelectorImmutable base_assignment_target (identifier list) (subscript list)
        array_value
End

Definition for_array_selector_static_mods_def[nocompute]:
  for_array_selector_static_mods c cx (e,sty,bd,saL)
    ((em,u,Gu,tu,dw,bw,capture),sel,w) <=>
    case (capture,w) of
      (ForArraySlot _ _ _ _ _,ArraySelectorPlain) => T
    | (ForArrayOwned _,ArraySelectorPlain) => T
    | (ForArrayHeld name path _,ArraySelectorHeld p attrs tail old tv q sz rw delta) =>
        MEM p (expr_places e) /\
        place_access p [] = (NameTarget name,attrs) /\
        path = MAP AttrSubscript attrs ++ tail /\
        lookup_scopes name em.scopes = SOME old /\
        evaluate_type (get_tenv cx) sty = SOME tv /\
        FLOOKUP c.ce_vars name = SOME (PtrVar (Var q) sz) /\
        lookup_var q u = SOME rw /\ not_fresh_at saL q /\
        mem_path_offset old.type path = SOME (delta,ArrayTV tv bd) /\
        bw = rw + n2w delta /\ w2n rw + delta < dimword (:256) /\
        w2n rw <= w2n bw /\
        w2n bw + type_memory_size (ArrayTV tv bd) <= w2n rw + sz
    | (ForArrayImmutable src name path off itv _ av,ArraySelectorImmutable p attrs tail cap) =>
        loop_iterator_place e = SOME p /\
        place_access p [] = (TopLevelNameTarget (src,name),attrs) /\
        path = MAP AttrSubscript attrs ++ tail /\ sel = SOME cap /\
        off + type_memory_size itv < dimword (:256) /\
        (?old. lookup_immutable cx em src name = SOME (itv,old) /\
               evaluate_subscripts itv old (MAP AttrSubscript attrs) = INL (ArrayV cap) /\
               evaluate_subscripts itv old path = INL (ArrayV av))
    | _ => F
End

Definition for_array_selector_current_mods_def[nocompute]:
  for_array_selector_current_mods cx ((em,u,Gu,tu,dw,bw,capture),sel,w) ee <=>
    case (capture,w) of
      (ForArraySlot _ _ _ _ _,ArraySelectorPlain) => T
    | (ForArrayOwned _,ArraySelectorPlain) => T
    | (ForArrayHeld name path av,ArraySelectorHeld _ _ _ old _ _ _ _ _) =>
        (?entry. lookup_scopes name ee.scopes = SOME entry /\
                 entry.type = old.type /\
                 evaluate_subscripts entry.type entry.value path = INL (ArrayV av))
    | (ForArrayImmutable src name path _ itv _ av,ArraySelectorImmutable _ attrs _ cap) =>
        (?now. lookup_immutable cx ee src name = SOME (itv,now) /\
               evaluate_subscripts itv now (MAP AttrSubscript attrs) = INL (ArrayV cap) /\
               evaluate_subscripts itv now path = INL (ArrayV av))
    | _ => F
End

Definition for_array_selected_origin_mods_def[nocompute]:
  for_array_selected_origin_mods c cx lo (sty,bd,loc) sbExpr op vs
    ((em,u,Gu,tu,dw,bw,capture),sel,w) <=>
    for_array_origin_mods c cx lo (sty,bd,loc)
      (em,sbExpr,u,Gu,tu) (op,bw) vs ((em,u,Gu,tu,dw,bw,capture),sel)
End

Definition for_array_selected_header_mods_def[nocompute]:
  for_array_selected_header_mods mods exps
    (DF,lo,d,ctx,func,shadow_func) cx env st0
    (es0,sa0,s0,G0,tn0) layout (saved,sel,w) H0 vs rs ee G tn t <=>
    for_array_origin_header_mods mods exps (DF,lo,d,ctx,func,shadow_func)
      cx env st0 (es0,sa0,s0,G0,tn0) layout saved sel H0 vs rs ee G tn t /\
    for_array_selector_current_mods cx (saved,sel,w) ee
End

Definition for_array_selected_entry_mods_def[nocompute]:
  for_array_selected_entry_mods mods exps cx env st0 tyv id body
    (DF,lo,d,ctx,func,shadow_func) (es0,sa0,s0,G0,tn0)
    ((c,id0,fty,e,sty,bd,ret_ty,loop_body),
     (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
     (bc,saD,saA,xd,capacity,aidItem),
     (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
     addr_cut,body_cut) h vs ee G tn t <=>
    valid_horizon cx st0 h ee.storage_trace /\
    ?P. for_array_selected_origin_mods c cx lo (sty,bd,loc) sbExpr (vv_operand vv) vs P /\
        for_array_selector_static_mods c cx (e,sty,bd,saL) P /\
        body_for_full_ok_mods mods exps cx tyv id body vs /\
        (!K. valid_horizon cx st0 K ee.storage_trace ==>
          for_array_selected_header_mods mods exps
            (DF,lo,d,ctx,func,shadow_func) cx env st0 (es0,sa0,s0,G0,tn0)
            ((c,id0,fty,e,sty,bd,ret_ty,loop_body),
             (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
             (bc,saD,saA,xd,capacity,aidItem),
             (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
             addr_cut,body_cut) P K vs vs ee G tn t)
End

Theorem for_array_selected_header_route_mods:
  for_array_selected_header_mods mods exps
    (DF,lo,d,ctx,func,shadow_func) cx env st0
    (es0,sa0,s0,G0,tn0)
    ((c,id,fty,e,sty,bd,ret_ty,loop_body),
     (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
     (bc,saD,saA,xd,capacity,aidItem),
     (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
     addr_cut,body_cut)
    ((em,u,Gu,tu,dw,bw,capture),sel,w) H0 vs rs ee G tn t <=>
    for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body)
      (func,shadow_func)
      (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
      (bc,saD,saA,xd,capacity,aidItem)
      (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
      addr_cut body_cut /\
    copy_old_operand saL (vv_operand vv) /\
    (!lbl. vv_operand vv <> Label lbl) /\
    for_array_header_mods mods DF lo d ctx func c cx env id st0
      (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu)
      (xd,dw,capacity,aidItem) vs (vv_operand vv,bw,len_op,idx) cond
      (\H rs' ee' G' tn' t'.
        for_array_observation_mods c cx lo (sty,bd,loc)
          (em,sbExpr,u,Gu,tu) (vv_operand vv,bw) vs
          ((em,u,Gu,tu,dw,bw,capture),sel) H rs' ee' G' tn' t' /\
        for_array_selector_current_mods cx ((em,u,Gu,tu,dw,bw,capture),sel,w) ee')
      H0 rs ee G tn t /\
    (rs = vs \/ body_stmts_full_ok_mods mods exps cx loop_body)
Proof
  simp[for_array_selected_header_mods_def,for_array_origin_header_mods_def] >>
  simp[for_array_header_mods_def, AC CONJ_ASSOC CONJ_COMM]
QED

Theorem for_array_selected_entry_extract_mods:
  storage_trace_domain cx st0 ee.storage_trace /\
  (!h. valid_horizon cx st0 h ee.storage_trace ==>
    for_array_selected_entry_mods mods exps cx env st0 tyv id body
      (DF,lo,d,ctx,func,shadow_func) (es0,sa0,s0,G0,tn0)
      ((c,id0,fty,e,sty,bd,ret_ty,loop_body),
       (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
       (bc,saD,saA,xd,capacity,aidItem),
       (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
       addr_cut,body_cut) h vs ee G tn t) ==>
  ?P. for_array_selected_origin_mods c cx lo (sty,bd,loc) sbExpr (vv_operand vv) vs P /\
      for_array_selector_static_mods c cx (e,sty,bd,saL) P /\
      body_for_full_ok_mods mods exps cx tyv id body vs /\
      (!K. valid_horizon cx st0 K ee.storage_trace ==>
        for_array_selected_header_mods mods exps
          (DF,lo,d,ctx,func,shadow_func) cx env st0 (es0,sa0,s0,G0,tn0)
          ((c,id0,fty,e,sty,bd,ret_ty,loop_body),
           (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
           (bc,saD,saA,xd,capacity,aidItem),
           (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
           addr_cut,body_cut) P K vs vs ee G tn t)
Proof
  strip_tac >>
  qpat_x_assum `!h. _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  fs[storage_trace_domain_def,for_array_selected_entry_mods_def]
QED
