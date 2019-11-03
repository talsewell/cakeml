(*
  Alternative semantics of dataLang without use of cut sets
*)

open preamble dataLangTheory dataSemTheory dataPropsTheory;

val _ = new_theory"data_no_cutSem";

val _ = set_grammar_ancestry ["dataProps", "dataLang", "dataSem",
                              "misc","sptree"];

val s = ``(s:('c,'ffi) dataSem$state)``

val vs = ``(vs:dataSem$v list)``

(* Alternative definition of evaluate, no cutting of states *)

val fix_clock_IMP = Q.prove(
  `fix_clock s x = (res,s1) ==> s1.clock <= s.clock`,
  Cases_on `x` \\ fs [fix_clock_def] \\ rw [] \\ fs []);

Definition evaluate_def:
  (evaluate (Skip,^s) = (NONE,s)) /\
  (evaluate (Move dest src,s) =
     case get_var src s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME v => (NONE, set_var dest v s)) /\
  (evaluate (Assign dest op args _,s) =
     (case get_vars args s.locals of
      | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
      | SOME xs => (case do_app op xs s of
                    | Rerr e => (SOME (Rerr e),call_env [] s with stack := [])
                    | Rval (v,s) =>
                      (NONE, set_var dest v s)))) /\
  (evaluate (Tick,s) =
     if s.clock = 0 then (SOME (Rerr(Rabort Rtimeout_error)),call_env [] s with stack := [])
                    else (NONE,dec_clock s)) /\
  (evaluate (MakeSpace k names,s) =
     (NONE,add_space s k)) /\
  (evaluate (Raise n,s) =
     case get_var n s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME x =>
       (case jump_exc s of
        | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
        | SOME s => (SOME (Rerr(Rraise x)),s))) /\
  (evaluate (Return n,s) =
     case get_var n s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME x => (SOME (Rval x),call_env [] s)) /\
  (evaluate (Seq c1 c2,s) =
     let (res,s1) = fix_clock s (evaluate (c1,s)) in
       if res = NONE then evaluate (c2,s1) else (res,s1)) /\
  (evaluate (If n c1 c2,s) =
     case get_var n s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
                        (* no time stamp *)
     | SOME x => if isBool T x then evaluate (c1,s) else
                 if isBool F x then evaluate (c2,s) else
                   (SOME (Rerr(Rabort Rtype_error)),s)) /\
  (evaluate (Call ret dest args handler,s) =
     case get_vars args s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME xs =>
       (case find_code dest xs s.code of
        | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
        | SOME (args1,prog) =>
          (case ret of
           | NONE (* tail call *) =>
             if handler = NONE then
               if s.clock = 0
               then (SOME (Rerr(Rabort Rtimeout_error)),
                     call_env [] s with stack := [])
               else
                 (case evaluate (prog, call_env args1 (dec_clock s)) of
                  | (NONE,s) => (SOME (Rerr(Rabort Rtype_error)),s)
                  | (SOME res,s) => (SOME res,s))
               else (SOME (Rerr(Rabort Rtype_error)),s)
           | SOME (n,_) (* returning call, returns into var n *) =>
               if s.clock = 0
               then (SOME (Rerr(Rabort Rtimeout_error)),
                     call_env [] s with stack := [])
               else
                 (case fix_clock s (evaluate (prog, call_env args1
                        (push_env s.locals (IS_SOME handler) (dec_clock s)))) of
                  | (SOME (Rval x),s2) =>
                     (case pop_env s2 of
                      | NONE => (SOME (Rerr(Rabort Rtype_error)),s2)
                      | SOME s1 => (NONE, set_var n x s1))
                  | (SOME (Rerr(Rraise x)),s2) =>
                     (case handler of (* if handler is present, then handle exc *)
                      | NONE => (SOME (Rerr(Rraise x)),s2)
                      | SOME (n,h) => evaluate (h, set_var n x s2))
                  | (NONE,s) => (SOME (Rerr(Rabort Rtype_error)),s)
                  | res => res))))
Termination
  WF_REL_TAC `(inv_image (measure I LEX measure prog_size)
                          (\(xs,s). (s.clock,xs)))`
  \\ rpt strip_tac
  \\ simp[dec_clock_def]
  \\ fs [Q.ISPEC `(x, y)` EQ_SYM_EQ]
  \\ imp_res_tac fix_clock_IMP
  \\ simp []
End

val evaluate_ind = theorem"evaluate_ind";

Theorem cut_env_locals_ok:
  cut_env cut_set e = SOME e' /\ locals_ok e ls ==>
  locals_ok e' ls
Proof
  simp [cut_env_def]
  \\ rw []
  \\ fs [locals_ok_def, lookup_inter, option_case_eq]
QED

Theorem cut_state_locals_ok:
  cut_state cut_set s = SOME s' /\ locals_ok s.locals ls ==>
  locals_ok s'.locals ls
Proof
  simp [cut_state_def, option_case_eq]
  \\ rw []
  \\ drule_then drule cut_env_locals_ok
  \\ simp []
QED

Theorem cut_state_opt_locals_ok:
  cut_state_opt cut_set s = SOME s' /\ locals_ok s.locals ls ==>
  locals_ok s'.locals ls
Proof
  simp [cut_state_opt_def, option_case_eq]
  \\ rw []
  \\ simp []
  \\ drule_then drule cut_state_locals_ok
  \\ simp []
QED

Theorem cut_state_eq_upd:
  cut_state cut_set s = SOME s' ==>
  ?cut_ls. s' = s with <| locals := cut_ls |>
Proof
  simp [cut_state_def, option_case_eq]
  \\ rw []
  \\ metis_tac []
QED

Theorem cut_state_opt_eq_upd:
  cut_state_opt cut_set s = SOME s' ==>
  ?cut_ls. s' = s with <| locals := cut_ls |>
Proof
  simp [cut_state_opt_def, option_case_eq]
  \\ rw []
  \\ TRY (drule_then irule cut_state_eq_upd)
  \\ qexists_tac `s.locals`
  \\ simp [state_component_equality]
QED

Theorem locals_ok_insert:
  locals_ok ls ls' ==>
  locals_ok (insert x y ls) (insert x y ls')
Proof
  simp [locals_ok_def, lookup_insert]
  \\ rw [] \\ rw []
  \\ fs []
QED

Definition s_frame_rel_def:
  s_frame_rel (Env env) sf = (?env'. sf = Env env' /\ locals_ok env env') /\
  s_frame_rel (Exc env n) sf = (?env'. sf = Exc env' n /\ locals_ok env env')
End

Definition s_rel_def:
  s_rel s t <=> (?ls st ss.
    t = s with <| locals := ls; stack := st; safe_for_space := ss |> /\
    locals_ok s.locals ls /\ LIST_REL s_frame_rel s.stack st)
End

Theorem s_rel_get_var:
  s_rel s t /\ get_var src s.locals = SOME v ==>
  get_var src t.locals = SOME v
Proof
  rw [s_rel_def]
  \\ simp []
  \\ metis_tac [locals_ok_get_var]
QED

Theorem s_rel_get_vars:
  s_rel s t /\ get_vars src s.locals = SOME vs ==>
  get_vars src t.locals = SOME vs
Proof
  rw [s_rel_def]
  \\ simp []
  \\ metis_tac [locals_ok_get_vars]
QED

Theorem cut_state_s_rel:
  cut_state names s = SOME s' /\ s_rel s t ==>
  s_rel s' t
Proof
  rw [s_rel_def, cut_state_def, option_case_eq]
  \\ simp [state_component_equality]
  \\ drule_then drule cut_env_locals_ok
  \\ simp []
QED

Theorem cut_state_opt_s_rel:
  cut_state_opt names s = SOME s' /\ s_rel s t ==>
  s_rel s' t
Proof
  rw [cut_state_opt_def, option_case_eq]
  \\ simp []
  \\ drule_then drule cut_state_s_rel
  \\ simp []
QED

Theorem s_rel_set_var:
  s_rel s t ==> s_rel (set_var x v s) (set_var x v t)
Proof
  rw [set_var_def, s_rel_def]
  \\ simp [state_component_equality, locals_ok_insert]
QED

Theorem pop_env_s_rel:
  pop_env s = SOME s' /\ s_rel s t ==>
  ?t'. pop_env t = SOME t' /\ s_rel s' t'
Proof
  rw []
  \\ fs [s_rel_def]
  \\ simp [PULL_EXISTS]
  \\ fs [pop_env_def, case_eq_thms]
  \\ EVERY_CASE_TAC
  \\ rveq \\ fs []
  \\ fs [s_frame_rel_def]
  \\ rveq \\ fs []
  \\ simp [state_component_equality]
QED

Theorem do_space_rel:
  do_space op len s = res /\
  s_rel s t ==>
  OPTREL s_rel res (do_space op len t)
Proof
  simp [do_space_def]
  \\ EVERY_CASE_TAC \\ fs []
  \\ rw []
  \\ fs [OPTREL_def]
  \\ fs [s_rel_def, state_component_equality]
  \\ fs [consume_space_def]
  \\ rveq \\ fs []
QED

fun eq_2case_tac get_case1 get_case2 (hyps, goal) = let
    val (_, ct1, _) = TypeBase.dest_case (get_case1 goal)
    val (_, ct2, _) = TypeBase.dest_case (get_case2 goal)
    val tac = if term_eq ct1 ct2 then
        Cases_on `^ct1`
        else (reverse (suff_tac (mk_eq (ct1, ct2)))
            THENL [all_tac, simp [] \\ Cases_on `^ct2`])
  in tac (hyps, goal) end

val rel_eq_2case_tac = eq_2case_tac (rand o rator) rand

Theorem do_app_s_rel:
  do_app op xs s = res /\
  s_rel s t ==>
  result_rel ((=) ### s_rel) (=) res (do_app op xs t)
Proof
  strip_tac
  \\ fs [do_app_def, bool_case_eq, option_case_eq]
  >- (
    simp [do_install_def]
    \\ rpt ((rel_eq_2case_tac ORELSE pairarg_tac ORELSE disch_tac) \\ fs [])
    \\ fs [s_rel_def, quotient_pairTheory.PAIR_REL_THM] \\ rveq \\ fs []
    \\ simp [state_component_equality]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rpt (CASE_TAC \\ fs [])
    \\ fs [quotient_pairTheory.PAIR_REL_THM, s_rel_def,
        state_component_equality]
  )
  \\ drule_then drule do_space_rel
  \\ simp [OPTREL_def]
  \\ rw []
  \\ simp []
  (* saved *)
  \\ simp [do_app_aux_def, with_fresh_ts_def]
  \\ rpt ((do_2case_tac ORELSE disch_tac) \\ simp [])
  \\ rw [quotient_pairTheory.PAIR_REL_THM]
  \\ TRY (fs [s_rel_def] \\ rveq \\ fs [state_component_equality] \\ NO_TAC)
QED

Theorem exc_rel_eq:
  exc_rel $= = $=
Proof
  simp [FUN_EQ_THM]
  \\ rpt Cases
  \\ simp []
QED

Theorem evaluate_no_cut:
  !prog s s' t res ls.
  case (prog, s) of (prog, s) =>
  (
  dataSem$evaluate (prog, s) = (res, s') /\
  s_rel s t /\
  res <> SOME (Rerr(Rabort Rtype_error))
  ==>
  ?t'. evaluate (prog, t) = (res, t')
  /\ s_rel s' t'
  )
Proof
  ho_match_mp_tac dataSemTheory.evaluate_ind
  \\ simp [evaluate_def, dataSemTheory.evaluate_def]
  \\ rpt strip_tac
  \\ fs [option_case_eq] \\ rveq \\ fs []
  \\ TRY (drule_then drule s_rel_get_var)
  \\ TRY (drule_then drule s_rel_get_vars)
  \\ fs [s_rel_set_var]
  >- (
    (* op *)
    qmatch_asmsub_abbrev_tac `if nm_err then (SOME (Rerr _), _) else _`
    \\ fs [bool_case_eq, Q.ISPEC `(x, y)` EQ_SYM_EQ, option_case_eq]
    \\ drule_then drule cut_state_opt_s_rel
    \\ rw []
    \\ drule_then drule s_rel_get_vars
    \\ rw []
    \\ EVERY_CASE_TAC
    \\ drule_then drule do_app_s_rel
    \\ simp [quotient_pairTheory.PAIR_REL_THM]
    \\ fs [] \\ rveq \\ fs []
    \\ simp [s_rel_set_var]
    \\ simp [call_env_def, exc_rel_eq, s_rel_def]
    \\ fs [s_rel_def, state_component_equality, locals_ok_refl]
  )
  >- (
    fs [bool_case_eq, call_env_def, dec_clock_def]
    \\ fs [s_rel_def, state_component_equality, locals_ok_refl]
  )
  >- (
    fs [s_rel_def, state_component_equality, add_space_def]
    \\ drule_then drule cut_env_locals_ok
    \\ simp []
  )
  >- (
    fs [jump_exc_def, case_eq_thms, CaseEq "stack"]
    \\ simp [PULL_EXISTS]
    \\ fs [s_rel_def]
    \\ imp_res_tac LIST_REL_LENGTH
    \\ drule (REWRITE_RULE [Once CONJ_COMM] list_rel_lastn)
    \\ disch_then (qspec_then `s.handler + 1` mp_tac)
    \\ rw []
    \\ fs [s_frame_rel_def, state_component_equality]
  )
  >- (
    fs [call_env_def]
    \\ fs [s_rel_def, state_component_equality, locals_ok_refl]
  )
  >- (
    rpt (pairarg_tac \\ fs [])
    \\ first_x_assum drule
    \\ impl_tac >- (CCONTR_TAC \\ fs [])
    \\ strip_tac
    \\ fs [fix_clock_def]
    \\ rveq \\ fs []
    \\ imp_res_tac evaluate_clock
    \\ `MIN t.clock t'.clock = t'.clock` by
      fs [s_rel_def, arithmeticTheory.MIN_DEF]
    \\ fs [bool_case_eq, Q.ISPEC `(x, y)` EQ_SYM_EQ]
  )
  >- (
    fs [bool_case_eq]
    \\ fs [Q.ISPEC `(x, y)` EQ_SYM_EQ]
  )
  >- (
    `t.code = s.code /\ t.clock = s.clock` by fs [s_rel_def]
    \\ fs [pair_case_eq] \\ rveq \\ fs []
    \\ fs [call_env_def]
    \\ `s_rel (dec_clock s with locals := fromList args1)
        (dec_clock t with locals := fromList args1)`
      by fs [s_rel_def, dec_clock_def, locals_ok_refl, state_component_equality]
    \\ fs [pair_case_eq, option_case_eq, bool_case_eq] \\ rveq \\ fs []
    \\ TRY (fs [s_rel_def, state_component_equality, locals_ok_refl] \\ NO_TAC)
    \\ `locals_ok env t.locals`
      by (fs [s_rel_def] \\ drule_then drule cut_env_locals_ok \\ simp [])
    \\ `s_rel (push_env env (IS_SOME handler) (dec_clock s)
            with locals := fromList args1)
            (push_env t.locals (IS_SOME handler) (dec_clock t)
            with locals := fromList args1)`
      by (Cases_on `handler` \\ fs [s_rel_def, push_env_def, dec_clock_def]
        \\ imp_res_tac LIST_REL_LENGTH
        \\ rveq \\ fs []
        \\ simp [state_component_equality, locals_ok_refl, s_frame_rel_def])
    \\ first_x_assum drule
    \\ impl_tac >- (CCONTR_TAC \\ fs [])
    \\ rpt strip_tac
    \\ fs [fix_clock_def]
    \\ imp_res_tac evaluate_clock
    \\ `MIN s.clock t'.clock = t'.clock` by
      (Cases_on `handler`
      \\ fs [s_rel_def, push_env_def, dec_clock_def, arithmeticTheory.MIN_DEF])
    \\ fs [case_eq_thms, CaseEq "result", CaseEq "error_result"]
    \\ rveq \\ fs []
    \\ imp_res_tac pop_env_s_rel
    \\ simp [PULL_EXISTS, s_rel_set_var]
  )
QED

val _ = export_theory ();

