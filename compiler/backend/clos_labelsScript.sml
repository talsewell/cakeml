(*
  Replaces calls to unknown functions with constant type errors.
*)
open preamble closLangTheory;

val _ = new_theory "clos_labels";
val _ = set_grammar_ancestry ["closLang","misc","sptree"];

val remove_dests_def = tDefine "remove_dests" `
  (remove_dests (ds:num_set) [] = []) /\
  (remove_dests ds ((x:closLang$exp)::y::xs) =
     HD (remove_dests ds [x]) :: remove_dests ds (y::xs)) /\
  (remove_dests ds [Var t v] = [Var t v]) /\
  (remove_dests ds [If t x1 x2 x3] =
     [If t (HD (remove_dests ds [x1]))
           (HD (remove_dests ds [x2]))
           (HD (remove_dests ds [x3]))]) /\
  (remove_dests ds [Let t xs x2] =
     let xs = remove_dests ds xs in
     let x2 = HD (remove_dests ds [x2]) in
       [Let t xs x2]) /\
  (remove_dests ds [Raise t x1] =
     [Raise t (HD (remove_dests ds [x1]))]) /\
  (remove_dests ds [Handle t x1 x2] =
     [Handle t (HD (remove_dests ds [x1]))
              (HD (remove_dests ds [x2]))]) /\
  (remove_dests ds [Op t op xs] =
     [Op t op (remove_dests ds xs)]) /\
  (remove_dests ds [Tick t x] = [Tick t (HD (remove_dests ds [x]))]) /\
  (remove_dests ds [Call t ticks dest xs] =
   if IS_SOME (lookup dest ds) then
    [Call t ticks dest (remove_dests ds xs)]
   else [Op t (if NULL xs then El else String "") (remove_dests ds xs)]) /\
  (remove_dests ds [App t NONE x1 xs] =
  [App t NONE (HD (remove_dests ds [x1])) (remove_dests ds xs)]) /\
  (remove_dests ds [App t (SOME dest) x1 xs] =
  if IS_SOME (lookup dest ds) then
    [App t (SOME dest) (HD (remove_dests ds [x1])) (remove_dests ds xs)]
  else
    if NULL xs then [Let t [Op t El []] (HD (remove_dests ds [x1]))]
    else [Op t (String"") (remove_dests ds xs ++ remove_dests ds [x1])]) /\
  (remove_dests ds [Letrec t loc_opt vs fns x1] =
     let m = LENGTH fns in
     let new_fns =
       MAP (\(num_args, x).
         (num_args, HD (remove_dests ds [x]))) fns in
     [Letrec t loc_opt vs new_fns (HD (remove_dests ds [x1]))]) /\
  (remove_dests ds [Fn t loc_opt vs num_args x1] =
    [Fn t loc_opt vs num_args (HD (remove_dests ds [x1]))])`
  (WF_REL_TAC `measure (exp3_size o SND)`
   \\ simp []
   \\ rpt strip_tac
   \\ imp_res_tac exp1_size_lemma
   \\ simp []);

Theorem LENGTH_LE_EXP_SIZE:
  !xs. LENGTH xs <= closLang$exp3_size xs
Proof
  Induct_on `xs` \\ fs [exp_size_def]
QED

Theorem exp1_size:
  exp1_size fns = exp3_size (MAP SND fns) + LENGTH fns + list$SUM (MAP FST fns)
Proof
  Induct_on `fns` \\ fs [exp_size_def, FORALL_PROD]
QED

val add_code_locs_def = tDefine "add_code_locs" `
  (add_code_locs ds [] = (F, ds)) /\
  (add_code_locs ds (x::y::xs) =
     let install_ds = add_code_locs ds [x] in
       if FST install_ds then (T, fromList [])
       else add_code_locs (SND install_ds) (y::xs)) /\
  (add_code_locs ds [Var _ v] = (F, ds)) /\
  (add_code_locs ds [If _ x1 x2 x3] =
     add_code_locs ds [x1; x2; x3]) /\
  (add_code_locs ds [closLang$Let _ xs x2] =
     add_code_locs ds (x2 :: xs)) /\
  (add_code_locs ds [Raise _ x1] =
     add_code_locs ds [x1]) /\
  (add_code_locs ds [Tick _ x1] =
     add_code_locs ds [x1]) /\
  (add_code_locs ds [Op _ op xs] =
     if op = Install then (T, fromList [])
     else add_code_locs ds xs) /\
  (add_code_locs ds [App _ loc_opt x1 xs] =
     add_code_locs ds (x1 :: xs)) /\
  (add_code_locs ds [Fn _ loc_opt vs num_args x1] =
     let loc = case loc_opt of NONE => 0 | SOME n => n in
     add_code_locs (insert loc () ds) [x1]) /\
  (add_code_locs ds [Letrec _ loc_opt vs fns x1] =
     let loc = case loc_opt of NONE => 0 | SOME n => n in
     let ds = list_insert (GENLIST (λn. loc + 2*n) (LENGTH fns)) ds in
     add_code_locs ds (x1 :: MAP SND fns)) /\
  (add_code_locs ds [Handle _ x1 x2] =
     add_code_locs ds [x1; x2]) /\
  (add_code_locs ds [Call _ ticks dest xs] =
     add_code_locs ds xs)`
  (WF_REL_TAC `measure ((\exps. (3 * exp3_size exps)
        - (2 * LENGTH exps)) o SND)`
  \\ rw [arithmeticTheory.LEFT_ADD_DISTRIB]
  \\ ASSUME_TAC (SPEC_ALL LENGTH_LE_EXP_SIZE)
  \\ fs [exp1_size]);

val compile_def = Define`
  compile prog =
    let ds = list_insert (MAP FST prog) LN in
    case add_code_locs ds (MAP (SND o SND) prog) of
      (T, ds) => prog
    | (F, ds) =>
      MAP (λ(n,args,exp). (n, args, HD(remove_dests ds [exp]))) prog`;

Theorem LENGTH_remove_dests
  `!dests xs. LENGTH (remove_dests dests xs) = LENGTH xs`
  (recInduct (fetch "-" "remove_dests_ind") \\ simp [remove_dests_def] \\ rw []);

val _ = export_theory();
