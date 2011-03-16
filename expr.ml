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
  | Mix of expr * expr * expr
  | Assign of dest_var * expr
  | Ceq of select_expr * select_expr
  | Cgt of select_expr * select_expr
  | Clt of select_expr * select_expr
  | Ternary of expr * expr * expr

and select_expr =
  expr * lane_select array

and lane_select = R | G | B | A

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

(*
    tevregid = d + ((a OP b) ? c : 0)
*)

and compare_op =
  {
    cmp_a : var_setting;
    cmp_b : var_setting;
    cmp_c : var_setting;
    cmp_d : var_setting;
    cmp_op : tev_cmp_op;
    cmp_result : dest_var
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

and tev_cmp_op =
    CMP_r8_gt
  | CMP_r8_eq
  | CMP_gr16_gt
  | CMP_gr16_eq
  | CMP_bgr24_gt
  | CMP_bgr24_eq
  | CMP_rgb8_gt
  | CMP_rgb8_eq

and bias_values =
    TB_zero
  | TB_addhalf
  | TB_subhalf

and scale_values =
    CS_scale_1
  | CS_scale_2
  | CS_scale_4
  | CS_divide_2

and tev =
    Arith of arith_op
  | Comp of compare_op
