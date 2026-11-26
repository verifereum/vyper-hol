Theory intCallResultsProps
Ancestors
  vyperContext vyperInterpreter vyperState list

Theorem intcall_results_ih:
  !P cx src_id_opt fn es ts mut nr args dflts ret ss.
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') ==>
       P cx es) /\
    get_module_code cx src_id_opt = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts =
      SOME (mut,nr,args,dflts,ret,ss) /\
    LENGTH args - LENGTH dflts <= LENGTH es /\ LENGTH es <= LENGTH args /\
    ~MEM (src_id_opt,fn) cx.stk ==>
    P cx es
Proof
  rpt strip_tac >>
  `LENGTH args - LENGTH es <= LENGTH dflts` by decide_tac >>
  first_x_assum irule >>
  simp[type_check_def, assert_def, lift_option_type_def, return_def]
QED
