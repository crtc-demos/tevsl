type expr =
    Int of int32
  | Float of float
  | Plus of expr * expr
  | Minus of expr * expr
  | Mult of expr * expr
  | Divide of expr * expr
  | Var_ref of var_param
  | Neg of expr
  | Clamp of expr
  | Assign of dest_var * expr

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

(* 
    TevColorIn: a b c d
    TevColorOp: tevop tevbias tevscale clamp tevregid

    regular operation:

    tevregid = (d [+/-] ((1-c)*a + c*b) + tevbias) * tevscale
*)

type arith_op =
  {
    a : var_setting;
    b : var_setting;
    c : var_setting;
    d : var_setting;
    op : tev_op;
    bias : bias_values;
    scale : scale_values;
    clamp : bool;
    result : dest_var
  }

and var_setting =
    CC_cprev
  | CC_aprev
  | CC_c0
  | CC_a0
  | CC_c1
  | CC_a1
  | CC_c2
  | CC_a2
  | CC_texc
  | CC_texa
  | CC_rasc
  | CC_rasa
  | CC_one
  | CC_half
  | CC_const of unit
  | CC_zero

and tev_op =
    OP_add
  | OP_sub

and bias_values =
    TB_zero
  | TB_addhalf
  | TB_subhalf

and scale_values =
    CS_scale_1
  | CS_scale_2
  | CS_scale_4
  | CS_divide_2
