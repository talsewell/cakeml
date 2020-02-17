(*
  Abstract syntax for Pancake language.
  Pancake is an imperative language with
  instructions for conditionals, While loop,
  memory load and store, functions,
  and foreign function calls.
*)

open preamble
     mlstringTheory
     asmTheory            (* for binop and cmp *)
     backend_commonTheory (* for overloading the shift operation *);

val _ = new_theory "panLang";

Type shift = ``:ast$shift``

Type sname = ``:mlstring``

Type varname = ``:mlstring``

Type funname = ``:mlstring``

Type index = ``:num``


Datatype:
  shape = One
        | Comb (shape list)
End

Datatype:
  exp = Const ('a word)
      | Var varname    (* varname can hold any v: WordVal, LabelVal and StructVal *)
      | Label funname  (* return (LabelVal funname) if funname is decalred in code *)
      | Struct (exp list)
      | Field index exp
      | Load exp shape  (* TODISC:shape? *)
      | LoadByte exp
      | Op binop (exp list)
      | Cmp cmp exp exp
      | Shift shift exp num
End

Datatype:
  ret = Tail
      | Ret varname
      | Handle varname varname prog; (* ret variable, excp variable *)

  prog = Skip
       | Dec varname ('a exp) prog
       | Assign    varname  shape ('a exp)   (* dest, source *)
       | Store     ('a exp) ('a exp) shape   (* dest, source *)
       | StoreByte ('a exp) ('a exp)   (* dest, source *)
       | Seq prog prog
       | If    ('a exp) prog prog
       | While ('a exp) prog
       | Break
       | Continue
       | Call ret ('a exp) (('a exp) list)
       | ExtCall funname varname varname varname varname (* FFI name, conf_ptr, conf_len, array_ptr, array_len *)
       | Raise  ('a exp) shape
       | Return ('a exp) shape
       | Tick
End
(* idea to infer shapes where ever we can *)

Theorem MEM_IMP_exp_size:
   !xs a. MEM a xs ==> (exp_size l a < exp1_size l xs)
Proof
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [definition"exp_size_def"]
  \\ RES_TAC \\ DECIDE_TAC
QED

Overload shift = “backend_common$word_shift”

val _ = export_theory();
