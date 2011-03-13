type expr =
    Int of string
  | Float of string
  | Plus of expr * expr
  | Minus of expr * expr
  | Mult of expr * expr
  | Divide of expr * expr
  | Var_ref of var_param
  | Neg of expr

and var_param =
    Cprev
  | Aprev
  | C0
  | A0
  | C1
  | A1
  | C2
  | A2
  | Texc
  | Texa
  | Rasc
  | Rasa

and dest_var =
    Tevprev
  | Tevreg0
  | Tevreg1
  | Tevreg2
