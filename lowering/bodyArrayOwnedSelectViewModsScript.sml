(* The owned buffer at the end of the key evaluation, and the physical
   result of the subsequent bounds check and address calculation. *)
Theory bodyArrayOwnedSelectViewMods
Ancestors
  bodyFullTargetArrayLoad loweringPosts bodyPtrDefs ptrDiscipline
  valueEncoding vyperTyping vyperInterpreter vyperState vyperAST
  venomState fragExec fragGasOriginPtr compileEnv context words

Definition array_owned_memory_view_mods_def[nocompute]:
  array_owned_memory_view_mods ce cx (et,bd,etv) (sa,st2)
      (fin,v) (bop,it,Gi,tni,a) <=>
    let tv = ArrayTV etv bd;
        vv = LocatedValue (ArrayT et bd) (mk_ptr bop LocMemory);
        sz = type_memory_size tv
    in
      evaluate_type (get_tenv cx) et = SOME etv /\
      evaluate_type (get_tenv cx) (ArrayT et bd) = SOME tv /\
      value_has_type tv v /\ val_wf tv v /\
      eval_operand bop it = SOME a /\ op_taint tni bop = {} /\
      vv_own ce cx (ArrayT et bd) sa st2 fin (Value v) vv it /\
      vv_at ce cx (ArrayT et bd) sa st2 fin (Value v) vv it /\
      w2n a + sz < dimword (:256) /\
      (!m. mem_agree_outside tni.t_mem it.vs_memory m ==>
           val_in_memory tv v (w2n a) m) /\
      (sz <> 0 ==>
        w2n a + sz <= it.vs_alloca_next /\
        ?base len. op_prov Gi bop = SOME (base,len) /\ base <= w2n a /\
                   w2n a + sz <= base + len) /\
      (!cap. bd = vyperAST$Dynamic cap ==>
        ?vs. v = ArrayV (DynArrayV vs) /\ LENGTH vs <= cap /\
             mem_word_taint tni.t_mem (w2n a) = {} /\
             mload (w2n a) it = n2w (LENGTH vs))
End

Definition array_owned_select_run_mods_def[nocompute]:
  array_owned_select_run_mods (lo,explicit,ctx,func,PG) ce cx
      (et,bd,obj,idx) (sa,st2,sb,dst) (v,key) (fin,it,Gi,tni) <=>
    ?res r Gq tq.
      (!tail. select_result cx (ArrayT et bd) (Value v) (ValueSubscript key)
                  (fin with gas_obs := tail) = (res,fin with gas_obs := tail)) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (it,Gi,tni) []
              (r,Gq,tq)) /\
      ((?q. r = Abort Revert_abort q /\
            res = INR (Error (RuntimeError "evaluate_subscripts array_index"))) \/
       (?q child.
          r = OK q /\ res = INL (Value child) /\
          q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\
          ~q.vs_halted /\ alloca_history func q /\
          array_length_frame st2 it Gi tni q Gq tq /\
          let vv = LocatedValue et (mk_ptr dst LocMemory) in
            vv_holds ce cx et (Value child) vv fin q /\
            vv_at ce cx et sa sb fin (Value child) vv q /\
            vv_store_bound cx et et fin (Value child) vv q /\
            ptr_vv_ok cx et (Value child) vv fin Gq tq q /\
            (~is_word_type et /\ ~is_bytestring_type et ==>
               vv_own ce cx et sa sb fin (Value child) vv q) /\
            ptr_buf_ok ce (Subscript et obj idx) dst Gq q))
End

Theorem array_owned_view_dynamic_mods:
  array_owned_memory_view_mods ce cx (et,Dynamic cap,etv) (sa,st2)
      (fin,v) (bop,it,Gi,tni,a) ==>
  (?vs. v = ArrayV (DynArrayV vs) /\ LENGTH vs <= cap /\
        mem_word_taint tni.t_mem (w2n a) = {} /\
        mload (w2n a) it = n2w (LENGTH vs)) /\
  w2n a + (32 + cap * type_memory_size etv) <= it.vs_alloca_next /\
  (?base len. op_prov Gi bop = SOME (base,len) /\ base <= w2n a /\
              w2n a + (32 + cap * type_memory_size etv) <= base + len)
Proof
  simp[array_owned_memory_view_mods_def,type_memory_size_def]
QED

Theorem array_owned_run_path_mods:
  array_owned_select_run_mods (lo,explicit,ctx,func,PG) ce cx
      (et,bd,obj,idx) (sa,st2,sb,dst) (v,key) (fin,it,Gi,tni) ==>
  ?res r Gq tq.
    (!tail. select_result cx (ArrayT et bd) (Value v) (ValueSubscript key)
                (fin with gas_obs := tail) = (res,fin with gas_obs := tail)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (it,Gi,tni) [] (r,Gq,tq)) /\
    ((?q. r = Abort Revert_abort q /\
          res = INR (Error (RuntimeError "evaluate_subscripts array_index"))) \/
     (?q child. r = OK q /\ res = INL (Value child) /\
                array_length_frame st2 it Gi tni q Gq tq))
Proof
  rewrite_tac[array_owned_select_run_mods_def] >>
  disch_then (qx_choosel_then [`res`,`r`,`Gq`,`tq`] strip_assume_tac) >>
  qexistsl [`res`,`r`,`Gq`,`tq`] >> simp[] >>
  disj2_tac >> qexistsl [`q`,`child`] >> simp[]
QED
